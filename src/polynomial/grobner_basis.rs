// TODO: possible optimizations for this grubner basis calculator:
// - Implement Faugère's F4 and F5 algorithms
//    - https://en.wikipedia.org/wiki/Faug%C3%A8re%27s_F4_and_F5_algorithms
// - Use degrevlex ordering, and then transform to lex, which is cheaper than calculating in lex directly

use crate::{
    ordered_ops,
    polynomial::{Id, Polynomial, Power, Term},
};

use num_traits::Zero;
use std::{
    cell::Cell,
    cmp::Reverse,
    collections::{BTreeMap, HashMap},
};

use super::{
    division::{InvertibleCoefficient, TermAccumulator},
    monomial_ordering::Ordering,
    Coefficient, Monomial,
};

/// Replace polynomial variables so that they have an order that is
/// more suitable to calculate the Gröbner Basis, according to this:
/// https://gitlab.trnsz.com/reduce-algebra/reduce-algebra/-/blob/master/packages/groebner/groebopt.red
///
/// Returns a map from the old variables to the new ones.
///
/// PS: this heuristic sucks for my zokrates example
pub fn reorder_vars_for_easier_gb<O, C, P>(
    polynomials: &mut Vec<Polynomial<O, usize, C, P>>,
) -> HashMap<usize, usize>
where
    O: Ordering,
    C: Coefficient,
    P: Power,
{
    let mut var_map = HashMap::new();

    for p in polynomials.iter() {
        for t in p.terms.iter() {
            for var in t.monomial.product.iter() {
                let entry = var_map.entry(var.id).or_insert((P::zero(), 0usize));
                // TODO: maybe the correct is to use variable power, not monomial power?
                if entry.0 < t.monomial.total_power {
                    *entry = (t.monomial.total_power.clone(), 1);
                } else {
                    entry.1 += 1;
                }
            }
        }
    }

    let mut reordered: Vec<_> = var_map.keys().copied().collect();
    // The id must be included in the sorting key so the result is deterministic,
    // as the hash map is probably randomized for security.
    reordered.sort_unstable_by_key(|id| (var_map.get(id).unwrap(), *id));

    let var_map: HashMap<usize, usize> = reordered.into_iter().zip(0..).collect();

    for p in polynomials.iter_mut() {
        for t in p.terms.iter_mut() {
            for var in t.monomial.product.iter_mut() {
                let new_id = var_map.get(&var.id).unwrap();
                var.id = *new_id;
            }

            t.monomial.product.sort_unstable_by_key(|w| Reverse(w.id));
        }

        p.terms.sort_unstable_by(|a, b| b.monomial.cmp(&a.monomial));
    }

    var_map
}

/// Reduce just the leading term of one polynomial with respect to another.
fn lt_reduction_step<O, I, C, P>(
    p: &mut Polynomial<O, I, C, P>,
    reference: &Polynomial<O, I, C, P>,
) -> bool
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let ini_p = p.terms.get(0);

    let mut ref_iter = reference.terms.iter();
    let ini_ref = ref_iter.next();

    if let (Some(ini_p), Some(ini_ref)) = (ini_p, ini_ref) {
        // Find the quotient between the monomial ini(p) and ini(ref),
        // so that p - c*quot*ref eliminates the first term in p:
        let quot = match ini_p.monomial.clone().whole_division(&ini_ref.monomial) {
            Some(quot) => quot,
            None => {
                return false;
            }
        };

        let mut p_iter = std::mem::take(&mut p.terms).into_iter();
        let ini_p = p_iter.next().unwrap();

        // Calculate elimination factor, so that p + factor*ref eliminates the first term in p:
        let factor = Term {
            coefficient: ini_p
                .coefficient
                .elimination_factor(&ini_ref.coefficient.clone().inv()),
            monomial: quot,
        };

        // Apply the coefficient to all the remaining terms of reference
        let difference: Vec<_> = ref_iter.map(|t| factor.clone() * t.clone()).collect();

        // Sum the remaining terms into a new polinomial:
        p.terms = Polynomial::sum_terms(p_iter, difference.into_iter());

        true
    } else {
        false
    }
}

#[derive(Default)]
struct CallDetector {
    called: bool,
}

impl<O, I, C, P> TermAccumulator<O, I, C, P> for CallDetector {
    fn push(&mut self, _: Term<O, I, C, P>) {
        self.called = true;
    }
}

struct ReducedSet<O, I, C, P> {
    next_id: usize,
    ordered_set: BTreeMap<(Polynomial<O, I, C, P>, usize), Cell<usize>>,
}

impl<O, I, C, P> ReducedSet<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    fn new() -> Self {
        Self {
            next_id: 0,
            ordered_set: BTreeMap::new(),
        }
    }

    fn reduce(&self, p: Polynomial<O, I, C, P>) -> (bool, Polynomial<O, I, C, P>) {
        let mut was_reduced = false;

        let mut reduced = Vec::new();
        let mut p_key = (p, self.next_id);

        'outer: while !p_key.0.terms.is_empty() {
            // Find first element to reduce. Must do this so that p is not borrowed
            // during the iteration, so it can be mutated.
            let first = self.ordered_set.range(..=&p_key).rev().next();
            if let Some((first, _)) = first {
                // Try to reduce using every polynomial <= p in g, in decreasing order:
                for gp in self.ordered_set.range(..=first).rev() {
                    if lt_reduction_step(&mut p_key.0, &gp.0 .0) {
                        was_reduced = true;
                        continue 'outer;
                    }
                }
            };

            // Leading term could not be reduced by any polynomial in self, so remove it for further reducing:
            reduced.push(p_key.0.terms.remove(0));
        }

        (was_reduced, Polynomial { terms: reduced })
    }

    fn set_one(&mut self, p: Polynomial<O, I, C, P>) {
        self.ordered_set = BTreeMap::new();
        self.ordered_set.insert((p, self.next_id), Cell::new(0));
        self.next_id += 1;
    }

    fn insert(&mut self, p: Polynomial<O, I, C, P>) {
        let mut to_insert = vec![p];

        while let Some(p) = to_insert.pop() {
            let p = self.reduce(p).1;

            if p.is_constant() {
                // p is either reduced to zero, so we do nothing, or is constant, so we
                // can set self to p and return (because p divides everything there).
                if !p.is_zero() {
                    self.set_one(p);
                    return;
                }
                continue;
            }

            // Split the subset that might be reduced by p
            let key = (p, 0);
            let mut unchanged_lt = Vec::new();
            for mut e in self.ordered_set.split_off(&key) {
                if lt_reduction_step(&mut e.0 .0, &key.0) {
                    // Polynomial leading term was changed, so insert in the list to be inserted back.
                    to_insert.push(e.0 .0);
                } else {
                    // Leading term is unchanged: the polynomial itself might still need
                    // reducing, but all others in self are still reduced w.r.t. to it.
                    unchanged_lt.push(e);
                }
            }

            // Now p cannot reduce any remaining element of self, and have been reduced by self, so it
            // can be included in the set:
            self.ordered_set.insert((key.0, self.next_id), Cell::new(0));
            self.next_id += 1;

            // Polynomials with unchanged leading term must be reduced and inserted back into self.
            // It is done in increasing order so that each newly inserted polynomial might reduce
            // the following ones.
            for mut q in unchanged_lt {
                let (was_reduced, new_poly) = self.reduce(q.0 .0);
                if was_reduced {
                    self.ordered_set
                        .insert((new_poly, self.next_id), Cell::new(0));
                    self.next_id += 1;
                } else {
                    // Polynomial is unchanged, insert element back as is:
                    q.0 .0 = new_poly;
                    self.ordered_set.insert(q.0, q.1);
                }
            }
        }
    }
}

fn spar<O, I, C, P>(
    p: &Polynomial<O, I, C, P>,
    q: &Polynomial<O, I, C, P>,
) -> Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let sat_diff = |a: &Term<O, I, C, P>, b: &Term<O, I, C, P>| {
        let product = ordered_ops::saturating_sub(
            a.monomial.product.iter().cloned(),
            b.monomial.product.iter(),
            |x, y| y.id.cmp(&x.id),
            |mut x, y| {
                x.power = x.power.saturating_sub(&y.power);
                if x.power.is_zero() {
                    None
                } else {
                    Some(x)
                }
            },
        );

        let total_power = product.iter().fold(P::zero(), |mut acc, v| {
            acc += &v.power;
            acc
        });

        let monomial = Monomial {
            product,
            total_power,
            _phantom_ordering: std::marker::PhantomData,
        };

        Term {
            monomial,
            coefficient: a.coefficient.clone(),
        }
    };

    let mut iter_p = p.terms.iter();
    let mut iter_q = q.terms.iter();

    if let (Some(ini_p), Some(ini_q)) = (iter_p.next(), iter_q.next()) {
        if !ini_p.monomial.has_shared_variables(&ini_q.monomial) {
            return Polynomial::zero();
        }

        let p_complement = sat_diff(ini_q, ini_p);
        let mut q_complement = sat_diff(ini_p, ini_q);

        // q_complement must be negative, so the sum would eliminate the first term:
        q_complement.coefficient = {
            let mut neg = C::zero();
            neg -= q_complement.coefficient;
            neg
        };

        Polynomial {
            terms: Polynomial::sum_terms(
                iter_p.cloned().map(|x| x * p_complement.clone()),
                iter_q.cloned().map(|x| x * q_complement.clone()),
            ),
        }
    } else {
        Polynomial::zero()
    }
}

pub fn grobner_basis<O, I, C, P>(
    input: &mut dyn Iterator<Item = Polynomial<O, I, C, P>>,
) -> Vec<Polynomial<O, I, C, P>>
where
    O: Ordering,
    I: Id + std::fmt::Display,
    C: InvertibleCoefficient + std::fmt::Display,
    P: Power + std::fmt::Display,
{
    let mut gb = ReducedSet::new();

    for p in input {
        println!("{}", p);
        gb.insert(p);
    }

    println!("=======================");
    for (p, _) in gb.ordered_set.keys() {
        println!("{}", p);
    }

    while let Some(((elem, next_to_spar), _)) = gb.ordered_set.iter().fold(None, |acc, e| {
        if e.1.get() < e.0 .1 {
            let nterms = e.0 .0.terms.len();
            match acc {
                None => Some((e, nterms)),
                Some((c, c_nterms)) => {
                    if c_nterms < nterms {
                        Some((c, c_nterms))
                    } else {
                        Some((e, nterms))
                    }
                }
            }
        } else {
            acc
        }
    }) {
        let mut partner = elem;

        for e in gb.ordered_set.keys() {
            if e.1 >= next_to_spar.get() && e.1 < partner.1 {
                partner = e;
            }
        }
        next_to_spar.set(partner.1 + 1);

        println!(
            "==================\n\nWorking on {} and {} ...",
            elem.1, partner.1
        );

        if partner.1 < elem.1 {
            let new_p = spar(&elem.0, &partner.0);
            println!("Sparred! Inserting ...");
            gb.insert(new_p);
            println!("Inserted! New set:");

            for ((p, id), nts) in gb.ordered_set.iter() {
                println!(
                    " {}: {} (LT deg: {}, term count: {})",
                    id,
                    nts.get(),
                    p.terms[0].monomial.total_power,
                    p.terms.len()
                );
            }
        } else {
            println!("Skipped");
        }
    }

    gb.ordered_set.into_iter().map(|((p, _), _)| p).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::division::tests::*;
    use num_traits::{Inv, Pow};

    #[test]
    fn reduction_step_test() {
        // Can't use SmallPoly because i32 is not invertible
        let [x, y]: [QPoly; 2] = QPoly::new_variables([1u8, 0u8]).try_into().unwrap();

        let p = &(x.clone().pow(5u8) * y.clone().pow(3u8)) * r(4);

        let q = &x.clone().pow(3u8) * r(2) - y.clone() * x.clone() + &y.clone() * r(2) - r(3);

        let (quot, reduced) = p.clone().div_rem(&q).unwrap();
        println!("quot: {}, rem: {}", quot, reduced);

        let reconstructed_p = reduced + quot * q;

        assert_eq!(reconstructed_p, p);
    }

    #[test]
    fn grobner_basis_test() {
        let [x, y, z]: [QPoly; 3] = QPoly::new_variables([2, 1, 0u8]).try_into().unwrap();
        let eqs = [
            x.clone() * x.clone() + y.clone() * y.clone() + z.clone() * z.clone() - r(1),
            x.clone() * x.clone() - y.clone() + z.clone() * z.clone(),
            x.clone() - z.clone(),
        ];

        let grobner_basis = grobner_basis(&mut eqs.into_iter());
        println!("Gröbner Basis:");
        for p in grobner_basis.iter() {
            println!("{}", p);
        }

        let expected_solution = [
            &z.clone().pow(4u8) * r(4) + &z.clone().pow(2u8) * r(2) - r(1),
            y.clone() - &z.clone().pow(2u8) * r(2),
            x - z,
        ];

        for (result, expected) in grobner_basis.iter().zip(expected_solution) {
            assert_eq!(
                result * result.terms[0].coefficient.clone().inv(),
                &expected * expected.terms[0].coefficient.clone().inv()
            );
        }
    }

    #[test]
    fn test_grobner_basis_equal_1() {
        let [x, y]: [QPoly; 2] = QPoly::new_variables([1, 0u8]).try_into().unwrap();
        let unsolvable = [
            x.clone().pow(2u8) + x.clone() * y.clone() - r(10),
            x.clone().pow(3u8) + x.clone() * y.clone().pow(2u8) - r(25),
            x.clone().pow(4u8) + x.clone() * y.clone().pow(3u8) - r(70),
        ];

        let grobner_basis = grobner_basis(&mut unsolvable.into_iter());

        assert_eq!(grobner_basis.len(), 1);
        let p = grobner_basis.first().unwrap();
        assert!(p.is_constant() && !p.is_zero());

        println!("{}", grobner_basis.first().unwrap());
    }

    #[test]
    fn test_resilience_to_weird_input() {
        // Assert only the non-zero element remains:
        let zero_in_the_set =
            grobner_basis(&mut [QPoly::new_constant(r(42)), QPoly::zero()].into_iter());

        assert_eq!(zero_in_the_set.len(), 1);
        let p = zero_in_the_set.first().unwrap();
        assert!(p.is_constant() && !p.is_zero());

        // Assert set is empty:
        let empty: Vec<QPoly> = grobner_basis(&mut [].into_iter());
        assert!(empty.is_empty());
    }
}
