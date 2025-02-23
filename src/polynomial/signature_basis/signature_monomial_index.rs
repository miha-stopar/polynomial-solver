//! This module uses a k-d tree to provide a multidimensional index on signature
//! to leading monomial ratio and the exponents of the leading monomial.

use crate::kd_tree::{self, KDTree, SearchPath};
use crate::polynomial::divmask::DivMaskTestResult;
use crate::polynomial::Monomial;
use crate::polynomial::{division::Field, monomial_ordering::Ordering, Id, VariablePower};

use super::{DivMap, DivMask, MaskedMonomialRef, Ratio, SignPoly, SignedExponent};

/// The entries stored in the leafs are just raw pointers to SignPoly.
struct Entry<O: Ordering, I: Id, F: Field, E: SignedExponent>(*const SignPoly<O, I, F, E>);

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> Clone for Entry<O, I, F, E> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<O: Ordering, I: Id, F: Field, E: SignedExponent> Copy for Entry<O, I, F, E> {}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> kd_tree::Entry for Entry<O, I, F, E> {
    type KeyElem = KeyElem<O, I, E>;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
        let poly = unsafe { &(*self.0) };
        if dim == 0 {
            KeyElem::S2LMRatio(&poly.sign_to_lm_ratio)
        } else {
            let id = I::from_idx(dim - 1);
            let power = get_var_exp_from_lm(poly, &id);
            KeyElem::MonomialVar(VariablePower { id, power })
        }
    }

    fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem {
        let b = unsafe { &(*other.0) };
        if dim == 0 {
            KeyElem::S2LMRatio(&b.sign_to_lm_ratio)
        } else {
            let a = unsafe { &(*self.0) };
            let id = I::from_idx(dim - 1);

            let exp_a = get_var_exp_from_lm(a, &id);
            let exp_b = get_var_exp_from_lm(b, &id);
            let avg = (exp_a + exp_b + E::one()) / E::from(2);
            KeyElem::MonomialVar(VariablePower { id, power: avg })
        }
    }

    fn cmp_dim(&self, other: &Self::KeyElem) -> std::cmp::Ordering {
        let poly = unsafe { &(*self.0) };
        match other {
            KeyElem::S2LMRatio(ratio) => poly.sign_to_lm_ratio.cmp(unsafe { &(**ratio) }),
            KeyElem::MonomialVar(var) => var.power.cmp(&get_var_exp_from_lm(poly, &var.id)),
        }
    }
}

fn get_var_exp_from_lm<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    poly: &SignPoly<O, I, F, E>,
    id: &I,
) -> E {
    get_var_exp_from_monomial(&poly.polynomial.terms[0].monomial, id)
}

fn get_var_exp_from_monomial<O: Ordering, I: Id, E: SignedExponent>(
    monomial: &Monomial<O, I, E>,
    id: &I,
) -> E {
    let m = &monomial.product;
    // Is binary search better than linear?
    match m.binary_search_by(|v| v.id.cmp(id)) {
        Ok(idx) => m[idx].power.clone(),
        Err(_) => E::zero(),
    }
}

/// The key element 0 is a signature/leading monomial ratio, which is stored as
/// the integer comparer and a pointer to the original. The other key elements
/// are variables to some power, factors of the leading monomial.
enum KeyElem<O: Ordering, I: Id, E: SignedExponent> {
    S2LMRatio(*const Ratio<O, I, E>),
    MonomialVar(VariablePower<I, E>),
}

impl<O: Ordering, I: Id, E: SignedExponent> kd_tree::KeyElem for KeyElem<O, I, E> {
    fn dim_index(&self) -> usize {
        match self {
            KeyElem::S2LMRatio(_) => 0,
            KeyElem::MonomialVar(var) => var.id.to_idx() + 1,
        }
    }
}

#[derive(Clone)]
struct MaskedMonomial<O: Ordering, I: Id, E: SignedExponent> {
    divmask: DivMask,
    monomial: Monomial<O, I, E>,
}

impl<O: Ordering, I: Id, E: SignedExponent> MaskedMonomial<O, I, E> {
    fn from_ref(r: MaskedMonomialRef<O, I, E>) -> Self {
        Self {
            divmask: r.0.clone(),
            monomial: r.1.clone(),
        }
    }
}

/// A k-dimensional tree index, indexed by the signatures/leading monomial ratio
/// and the exponents of the leading monomial.
///
/// The tree is accelerated by the having the divmask of the GCD between all
/// contained elements, to quickly rule out the branch on search for a divisor,
/// using the fact that if a divides b then GCD(a, c) also divides b, for any c.
pub struct SignatureMonomialIndex<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    KDTree<Entry<O, I, F, E>, MaskedMonomial<O, I, E>>,
);

/// Maps a tree entry to its NodeData.
fn node_data_map<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    &Entry(p): &Entry<O, I, F, E>,
) -> Monomial<O, I, E> {
    unsafe { (*p).polynomial.terms[0].monomial.clone() }
}

/// Maps a tree entry to its NodeData.
fn node_data_builder<O: Ordering, I: Id, E: SignedExponent>(
    div_map: &DivMap<E>,
    a: Monomial<O, I, E>,
    b: Monomial<O, I, E>,
) -> (MaskedMonomial<O, I, E>, Monomial<O, I, E>) {
    let gcd = a.gcd(&b);
    let divmask = div_map.map(&gcd);
    let masked_gcd = MaskedMonomial {
        divmask,
        monomial: gcd.clone(),
    };
    // If the compiler is smart enough, it will reuse the allocation
    // of the two input monomials into the output monomials.
    (masked_gcd, gcd)
}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> SignatureMonomialIndex<O, I, F, E> {
    pub fn new(
        num_dimensions: usize,
        div_map: &DivMap<E>,
        elems: Vec<*const SignPoly<O, I, F, E>>,
    ) -> Self {
        let entries = elems.into_iter().map(|e| Entry(e)).collect();
        Self(KDTree::new(
            num_dimensions,
            entries,
            &node_data_map,
            &|a, b| node_data_builder(div_map, a, b),
        ))
    }

    pub fn insert(&mut self, div_map: &DivMap<E>, elem: *const SignPoly<O, I, F, E>) {
        let new_entry = Entry(elem);
        self.0.insert(
            new_entry,
            &|a, b| node_data_builder(div_map, node_data_map(a), node_data_map(b)),
            &|node_data, new_gcd| {
                node_data.monomial = new_gcd.gcd(&node_data.monomial);
                node_data.divmask = div_map.map(&node_data.monomial);
                node_data.monomial.clone()
            },
        )
    }

    pub(super) fn find_regular_reducer(
        &self,
        s_lm_ratio: &Ratio<O, I, E>,
        lm: &MaskedMonomialRef<O, I, E>,
    ) -> Option<*const SignPoly<O, I, F, E>> {
        let mut found = None;
        self.0.search(
            &|key, contained_gcd| {
                if let DivMaskTestResult::NotDivisible = contained_gcd.divmask.divides(lm.0) {
                    return SearchPath::None;
                };

                match key {
                    KeyElem::S2LMRatio(ratio) => {
                        if s_lm_ratio < (unsafe { &(**ratio) }) {
                            SearchPath::LessThan
                        } else {
                            SearchPath::Both
                        }
                    }
                    KeyElem::MonomialVar(var) => {
                        let exp = get_var_exp_from_monomial(lm.1, &var.id);
                        if exp < var.power {
                            SearchPath::LessThan
                        } else {
                            SearchPath::Both
                        }
                    }
                }
            },
            &mut |Entry(poly_ptr)| {
                let poly = unsafe { &**poly_ptr };
                if poly.sign_to_lm_ratio <= *s_lm_ratio && poly.leading_monomial().divides(lm) {
                    found = Some(*poly_ptr);
                    false
                } else {
                    true
                }
            },
        );

        found
    }
}
