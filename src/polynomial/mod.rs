pub mod cocoa_print;
pub mod division;
pub mod divmask;
pub mod grobner_basis;
pub mod monomial_ordering;
pub mod signature_basis;
pub mod circuit;

use super::ordered_ops;
use bitvec::macros::internal::funty::Unsigned;
use monomial_ordering::Ordering;
use num_traits::{One, Signed};
use std::{
    cmp::{Ordering as CmpOrd, Reverse},
    fmt::Write,
    marker::PhantomData,
    ops::{Mul, MulAssign},
};

/// The trait used to identify a variable.
///
/// The Id must be a bijection to usize from 0 up to the maximum used Id. The
/// alternative would be to require Id to be hashable and use hash table where
/// Id is used as index, but that would worsen the performance of Gröbner Basis
/// algorithm.
pub trait Id: core::fmt::Debug + Eq + Ord + Clone {
    /// The forward side of the bijection with usize:
    fn to_idx(&self) -> usize;

    /// The reverse side of the bijection with usize. This will be called from 0
    /// up to the maximum value returned by to_idx() in the set of all Ids seen.
    fn from_idx(idx: usize) -> Self;

    /// Display function for Id.
    ///
    /// Default implementation simply prints x followed by the index.
    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "x{}", self.to_idx())
    }
}

/// Implement Id for all basic unsigned types:
impl<T> Id for T
where
    T: Unsigned + TryInto<usize>,
    usize: TryInto<T>,
    <T as TryInto<usize>>::Error: std::fmt::Debug,
    <usize as TryInto<T>>::Error: std::fmt::Debug,
{
    fn to_idx(&self) -> usize {
        (*self).try_into().unwrap()
    }

    fn from_idx(idx: usize) -> T {
        idx.try_into().unwrap()
    }
}

pub trait CommutativeRing:
    core::fmt::Debug
    + PartialEq
    + Clone
    + std::ops::AddAssign
    + std::ops::SubAssign
    + for<'a> MulAssign<&'a Self>
    + num_traits::Zero
    + num_traits::One
{
}

pub trait Exponent:
    core::fmt::Debug
    + Eq
    + Ord
    + Clone
    + std::ops::AddAssign
    + for<'a> std::ops::AddAssign<&'a Self>
    + for<'a> std::ops::SubAssign<&'a Self>
    + for<'a> std::ops::Mul<&'a Self, Output = Self>
    + for<'a> std::ops::Div<&'a Self, Output = Self>
    + num_traits::Zero
    + num_traits::One
    + num_traits::Bounded
    + From<u8>
{
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariablePower<I, P> {
    id: I,
    power: P,
}

impl<I, P> VariablePower<I, P>
where
    I: Id,
    P: Exponent,
{
    pub fn new(id: I, power: P) -> Self {
        VariablePower { id, power }
    }

    pub fn get_id(&self) -> &I {
        &self.id
    }
}

#[derive(Debug)]
pub struct Monomial<O: ?Sized, I, P> {
    // Product is sorted in decreasing order of id:
    product: Vec<VariablePower<I, P>>,
    total_power: P,
    _phantom_ordering: PhantomData<O>,
}

impl<O, I, P> Monomial<O, I, P>
where
    O: Ordering,
    I: Id,
    P: Exponent,
{
    /// Greatest Common Divisor between two monomials.
    pub fn gcd(mut self, other: &Self) -> Self {
        let mut remover = other.product.iter().peekable();

        self.total_power = P::zero();
        self.product.retain_mut(|var| {
            while let Some(r) = remover.peek() {
                match r.id.cmp(&var.id) {
                    CmpOrd::Greater => (),
                    CmpOrd::Equal => {
                        var.power = var.power.clone().min(r.power.clone());
                        self.total_power += &var.power;
                        return true;
                    }
                    CmpOrd::Less => break,
                }
                remover.next();
            }
            false
        });

        self
    }

    /// Whole division implementation. If self is not divisible by
    /// divisor, returns None.
    pub fn whole_division(mut self, divisor: &Self) -> Option<Self> {
        let mut iter = self.product.iter_mut();

        for var in divisor.product.iter() {
            let found = iter.find(|e| e.id == var.id)?;
            if found.power < var.power {
                return None;
            }

            found.power -= &var.power;
            self.total_power -= &var.power;
        }

        self.product.retain(|e| !e.power.is_zero());

        Some(self)
    }

    /// Tells if you can whole divide other by self.
    ///
    /// This function is intended to be faster than directly attempting
    /// whole_division.
    pub fn divides(&self, other: &Self) -> bool {
        if self.total_power > other.total_power || self.product.len() > other.product.len() {
            return false;
        }

        let mut window_start = 0;
        let mut window_end = other.product.len() - self.product.len();

        // Search each self variable in the possible range of other, considering
        // both sequences are ordered by decreasing variable.
        'outer: for self_var in self.product.iter() {
            // There is only a window of variables that is worth searching for a
            // match in the other monomial, because even it is present later,
            // there is no room for the remaining variables. If not present in
            // this window, we know self can't divide other.
            let window = &other.product[window_start..=window_end];
            window_end += 1;

            // Search inside the window:
            for (j, other_var) in window.iter().enumerate() {
                match other_var.id.cmp(&self_var.id) {
                    CmpOrd::Less => {
                        // Since monomial.product is ordered in decreasing
                        // order, there is no match for self_var in other.
                        return false;
                    }
                    CmpOrd::Equal => {
                        // The variable is in both monomials, but we still have
                        // to compare the powers:
                        if other_var.power < self_var.power {
                            return false;
                        }

                        // Next time, the window starts on the next element.
                        window_start += j + 1;

                        continue 'outer;
                    }
                    CmpOrd::Greater => {
                        // Not this one, maybe it is the next one.
                    }
                }
            }
            // There is no match for the variable in the window, so it is not
            // divisible.
            return false;
        }

        // All self variables have been properly matched.
        true
    }

    /// Divides self by its gcd with of other monomial
    pub fn div_by_gcd(&self, other: &Self) -> Self {
        let product = ordered_ops::saturating_sub(
            self.product.iter().cloned(),
            other.product.iter(),
            |x, y| y.id.cmp(&x.id),
            |mut x, y| {
                if x.power > y.power {
                    x.power -= &y.power;
                    Some(x)
                } else {
                    None
                }
            },
        );

        let total_power = product.iter().fold(P::zero(), |mut acc, v| {
            acc += &v.power;
            acc
        });

        Self {
            product,
            total_power,
            _phantom_ordering: std::marker::PhantomData,
        }
    }

    pub fn has_shared_variables(&self, other: &Self) -> bool {
        let mut iter_a = self.product.iter();
        let mut iter_b = other.product.iter();

        let mut next_a = iter_a.next();
        let mut next_b = iter_b.next();
        while let (Some(a), Some(b)) = (next_a, next_b) {
            match a.id.cmp(&b.id) {
                CmpOrd::Equal => {
                    return true;
                }
                CmpOrd::Greater => {
                    next_a = iter_a.next();
                    next_b = Some(b);
                }
                CmpOrd::Less => {
                    next_a = Some(a);
                    next_b = iter_b.next();
                }
            }
        }

        false
    }

    pub fn get_product(&self) -> &[VariablePower<I, P>] {
        &self.product[..]
    }

    pub fn get_total_power(&self) -> &P {
        &self.total_power
    }
}

impl<O, I, P> Monomial<O, I, P>
where
    O: Ordering,
    I: Id,
    P: Exponent + Signed,
{
    /// Return the ratio between two monomials, allowing exponents to be
    /// negative.
    pub fn fraction_division(&self, divisor: &Self) -> Self {
        let mut product = Vec::new();
        ordered_ops::sum(
            self.product.iter().cloned(),
            divisor.product.iter().cloned().map(|mut var| {
                var.power = -var.power;
                var
            }),
            |a, b| b.id.cmp(&a.id),
            |a, b| {
                let mut ret = a.clone();
                ret.power += &b.power;
                if ret.power.is_zero() {
                    None
                } else {
                    Some(ret)
                }
            },
            &mut product,
        );

        let mut total_power = self.total_power.clone();
        total_power -= &divisor.total_power;

        Self {
            product,
            total_power,
            _phantom_ordering: PhantomData,
        }
    }
}

impl<O, I: Clone, P: Clone> Clone for Monomial<O, I, P> {
    fn clone(&self) -> Self {
        Self {
            product: self.product.clone(),
            total_power: self.total_power.clone(),
            _phantom_ordering: PhantomData,
        }
    }
}

// I did't use derive(PartialEq) because total_power
// need not to be part of the comparison.
impl<O, I: PartialEq, P: PartialEq> PartialEq for Monomial<O, I, P> {
    fn eq(&self, other: &Self) -> bool {
        self.product == other.product
    }
}

impl<O, I: Eq, P: Eq> Eq for Monomial<O, I, P> {}

impl<O: Ordering, I: Id, P: Exponent> Ord for Monomial<O, I, P> {
    fn cmp(&self, other: &Self) -> CmpOrd {
        Ordering::ord(self, other)
    }
}

impl<O: Ordering, I: Id, P: Exponent> PartialOrd for Monomial<O, I, P> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ordering::ord(self, other))
    }
}

impl<O, I, P> One for Monomial<O, I, P>
where
    O: Ordering,
    I: Id,
    P: Exponent,
{
    fn one() -> Self {
        Monomial {
            // Empty product means implicitly one
            product: Vec::new(),
            total_power: P::zero(),
            _phantom_ordering: PhantomData,
        }
    }
}

impl<O, I, P> Mul for Monomial<O, I, P>
where
    O: Ordering,
    I: Id,
    P: Exponent,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut product = Vec::new();
        ordered_ops::sum(
            self.product.into_iter(),
            rhs.product.into_iter(),
            |x, y| y.id.cmp(&x.id),
            |mut x, y| {
                x.power += y.power;
                if x.power.is_zero() {
                    None
                } else {
                    Some(x)
                }
            },
            &mut product,
        );
        let mut total_power = P::zero();
        for e in product.iter() {
            total_power += &e.power;
        }

        Monomial {
            product,
            total_power,
            _phantom_ordering: PhantomData,
        }
    }
}

#[derive(Debug)]
pub struct Term<O, I, C, P> {
    coefficient: C,
    monomial: Monomial<O, I, P>,
}

impl<O, I, C, P> Term<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    pub fn new(coefficient: C, id: I, power: P) -> Self {
        if power.is_zero() {
            Self::new_constant(coefficient)
        } else {
            Term {
                coefficient,
                monomial: Monomial {
                    product: vec![VariablePower {
                        id,
                        power: power.clone(),
                    }],
                    total_power: power,
                    _phantom_ordering: PhantomData,
                },
            }
        }
    }

    pub fn new_multi_vars(coefficient: C, mut vars: Vec<VariablePower<I, P>>) -> Self {
        // Order the variables by id in reverse:
        vars.sort_unstable_by(|x, y| y.id.cmp(&x.id));

        let mut total_power = vars.first().map_or(P::zero(), |x| x.power.clone());

        // Join same vars:
        vars.dedup_by(|from, to| {
            total_power += &from.power;

            if from.id != to.id {
                return false;
            }

            to.power += std::mem::replace(&mut from.power, P::zero());
            true
        });

        // Remove any variable whose power is 0
        vars.retain(|e| !e.power.is_zero());

        Self {
            coefficient,
            monomial: Monomial {
                product: vars,
                total_power,
                _phantom_ordering: PhantomData,
            },
        }
    }

    pub fn new_constant(value: C) -> Self {
        Term {
            coefficient: value,
            monomial: Monomial::one(),
        }
    }

    pub fn get_coefficient(&self) -> &C {
        &self.coefficient
    }

    pub fn get_monomial(&self) -> &Monomial<O, I, P> {
        &self.monomial
    }
}

impl<O, I: Clone, C: Clone, P: Clone> Clone for Term<O, I, C, P> {
    fn clone(&self) -> Self {
        Self {
            coefficient: self.coefficient.clone(),
            monomial: self.monomial.clone(),
        }
    }
}

impl<O, I, C, P> PartialEq for Term<O, I, C, P>
where
    I: PartialEq,
    C: PartialEq,
    P: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.coefficient == other.coefficient && self.monomial == other.monomial
    }
}

impl<O, I, C, P> Eq for Term<O, I, C, P>
where
    I: Eq,
    C: Eq,
    P: Eq,
{
}

impl<O, I, C, P> std::ops::Neg for Term<O, I, C, P>
where
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Self;

    fn neg(self) -> Self {
        let mut coefficient = C::zero();
        coefficient -= self.coefficient;

        Self {
            coefficient,
            ..self
        }
    }
}

impl<O, I, C, P> Mul for Term<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut coefficient = self.coefficient;
        coefficient *= &rhs.coefficient;

        Self {
            coefficient,
            monomial: self.monomial * rhs.monomial,
        }
    }
}

#[derive(Debug)]
pub struct Polynomial<O, I, C, P> {
    // Terms are sorted in decreasing order of monomials
    terms: Vec<Term<O, I, C, P>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum ExtendedId<I: Id> {
    Original(I),
    Extra,
}

impl<I: Id> Id for ExtendedId<I> {
    fn to_idx(&self) -> usize {
        match self {
            Self::Extra => 0,
            Self::Original(id) => id.to_idx() + 1,
        }
    }

    fn from_idx(idx: usize) -> Self {
        if idx == 0 {
            Self::Extra
        } else {
            Self::Original(I::from_idx(idx - 1))
        }
    }
}

// TODO optimization: implement term * polynomial multiplication
impl<O, I, C, P> Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    pub fn new_variables(var_ids: impl IntoIterator<Item = I>) -> Vec<Self> {
        var_ids
            .into_iter()
            .map(|id| Self::new_monomial_term(C::one(), id, P::one()))
            .collect()
    }

    pub fn new_monomial_term(coefficient: C, id: I, power: P) -> Self {
        Self {
            terms: vec![Term::new(coefficient, id, power)],
        }
    }

    pub fn new_constant(value: C) -> Self {
        Self {
            terms: if value.is_zero() {
                // No terms means zero implictly
                Vec::new()
            } else {
                vec![Term::new_constant(value)]
            },
        }
    }

    pub fn new_var(id: I) -> Self {
        Self::new_monomial_term(C::one(), id, P::one())
    }

    pub fn one() -> Self {
        Self::new_constant(C::one())
    }

    pub fn from_terms(mut terms: Vec<Term<O, I, C, P>>) -> Self {
        terms.sort_unstable_by(|a, b| b.monomial.cmp(&a.monomial));
        terms.dedup_by(|from, to| {
            if from.monomial != to.monomial {
                return false;
            }

            to.coefficient += std::mem::replace(&mut from.coefficient, C::zero());
            true
        });
        terms.retain(|e| !e.coefficient.is_zero());
        Self { terms }
    }

    pub fn get_terms(&self) -> &[Term<O, I, C, P>] {
        &self.terms[..]
    }

    pub fn is_constant(&self) -> bool {
        match self.terms.get(0) {
            None => true,
            Some(t) => t.monomial.product.is_empty(),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// If the polynomial uses exactly one variable, returns the variable id.
    pub fn try_get_univariate_id(&self) -> Option<I> {
        let mut ret = None;
        for term in self.terms.iter() {
            for var in term.monomial.product.iter() {
                match &ret {
                    None => {
                        ret = Some(var.id.clone());
                    }
                    Some(id) => {
                        if *id != var.id {
                            return None;
                        }
                    }
                }
            }
        }

        ret
    }

    /// Make all terms of the polynomial the same given degree by introducing a new variable
    /// and multiplying it to each term the appropriate number of times.
    pub fn homogenize(self) -> Polynomial<O, ExtendedId<I>, C, P> {
        // Calculate the degree of the polynomial:
        let degree = self
            .terms
            .iter()
            .map(|t| &t.monomial.total_power)
            .max()
            .unwrap_or(&P::zero())
            .clone();

        self.homogenize_to_degree(&degree).unwrap()
    }

    /// Make all terms of the polynomial the same given degree by introducing a
    /// new variable and multiplying it to each term the appropriate number of times.
    /// Target degree must be <= the degree of the polynomial.
    ///
    /// The original polynomial can be recovered by setting the new variable value to 1.
    /// TODO: implement dehomogenize
    pub fn homogenize_to_degree(
        self,
        degree: &P,
    ) -> Result<Polynomial<O, ExtendedId<I>, C, P>, &'static str> {
        let mut terms = Vec::new();

        // Process each term
        for term in self.terms {
            // Transfer existing variables to the new type:
            let mut product: Vec<_> = term
                .monomial
                .product
                .into_iter()
                .map(|v| VariablePower {
                    id: ExtendedId::Original(v.id),
                    power: v.power,
                })
                .collect();

            // Create the new variable with appropriate degree, if needed.
            match degree.cmp(&term.monomial.total_power) {
                CmpOrd::Less => {
                    return Err("can't homogenize a polynomial to a smaller degree");
                }
                CmpOrd::Equal => (/* term already at target degree */),
                CmpOrd::Greater => {
                    let mut new_var_deg = degree.clone();
                    new_var_deg -= &term.monomial.total_power;
                    product.push(VariablePower {
                        id: ExtendedId::Extra,
                        power: new_var_deg,
                    });
                }
            }

            // Push the new term.
            terms.push(Term {
                coefficient: term.coefficient,
                monomial: Monomial {
                    product,
                    total_power: degree.clone(),
                    _phantom_ordering: Default::default(),
                },
            });
        }

        // Homogenization might change the order among terms, so sort:
        terms.sort_unstable_by(|a, b| a.monomial.cmp(&b.monomial));

        Ok(Polynomial { terms })
    }

    fn sum_terms(
        a: impl Iterator<Item = Term<O, I, C, P>>,
        b: impl Iterator<Item = Term<O, I, C, P>>,
        output: &mut Vec<Term<O, I, C, P>>,
    ) {
        ordered_ops::sum(
            a,
            b,
            |x, y| y.monomial.cmp(&x.monomial),
            |mut x, y| {
                x.coefficient += y.coefficient;
                if x.coefficient.is_zero() {
                    None
                } else {
                    Some(x)
                }
            },
            output,
        )
    }
}

impl<O, I, C, P> Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing + From<P>,
    P: Exponent,
{
    pub fn derivative(mut self, variable: &I) -> Self {
        self.terms.retain_mut(|term| {
            let idx = match term.monomial.product[..]
                .binary_search_by_key(&Reverse(variable), |v| Reverse(&v.id))
            {
                Err(_) => {
                    // This term is constant, obliterate it:
                    return false;
                }
                Ok(idx) => idx,
            };

            let var = &mut term.monomial.product[idx];
            term.coefficient *= &C::from(var.power.clone());
            var.power -= &P::one();
            if var.power.is_zero() {
                term.monomial.product.remove(idx);
            }

            true
        });

        self
    }
}

impl<O, I: Clone, C: Clone, P: Clone> Clone for Polynomial<O, I, C, P> {
    fn clone(&self) -> Self {
        Self {
            terms: self.terms.clone(),
        }
    }
}

impl<O, I, C, P> Eq for Polynomial<O, I, C, P>
where
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
}

impl<O, I, C, P> PartialEq for Polynomial<O, I, C, P>
where
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.terms == rhs.terms
    }
}

impl<O, I, C, P> Ord for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    /// Compare by leading monomials. Non-constant > non-zero constant > zero.
    fn cmp(&self, rhs: &Self) -> CmpOrd {
        match (self.terms.get(0), rhs.terms.get(0)) {
            (Some(a), Some(b)) => a.monomial.cmp(&b.monomial),
            (None, Some(_)) => CmpOrd::Less,
            (Some(_), None) => CmpOrd::Greater,
            (None, None) => CmpOrd::Equal,
        }
    }
}

impl<O, I, C, P> PartialOrd for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    fn partial_cmp(&self, rhs: &Self) -> Option<CmpOrd> {
        Some(self.cmp(rhs))
    }
}

impl<O, I, C, P> num_traits::Zero for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    fn zero() -> Self {
        Polynomial { terms: Vec::new() }
    }

    fn is_zero(&self) -> bool {
        // Assumes the polynomial is normalized:
        self.terms.is_empty()
    }
}

impl<O, I, C, P> std::ops::Add for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn add(self, rhs: Polynomial<O, I, C, P>) -> Self::Output {
        let mut terms = Vec::new();
        Self::sum_terms(self.terms.into_iter(), rhs.terms.into_iter(), &mut terms);
        Self { terms }
    }
}

impl<O, I, C, P> std::ops::Add<C> for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn add(mut self, rhs: C) -> Self::Output {
        let size = self.terms.len();
        let last = &mut self.terms[size - 1];
        if last.monomial.product.is_empty() {
            last.coefficient += rhs;
        } else {
            self.terms.push(Term::new_constant(rhs));
        }

        self
    }
}

impl<O, I, C, P> std::ops::Neg for Polynomial<O, I, C, P>
where
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Self;

    fn neg(mut self) -> Self {
        for term in self.terms.iter_mut() {
            let tmp = std::mem::replace(&mut term.coefficient, C::zero());
            term.coefficient -= tmp;
        }
        self
    }
}

impl<O, I, C, P> std::ops::Sub for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn sub(self, rhs: Polynomial<O, I, C, P>) -> Self::Output {
        self + (-rhs)
    }
}

impl<O, I, C, P> std::ops::Sub<C> for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn sub(mut self, rhs: C) -> Self::Output {
        let size = self.terms.len();
        let last = &mut self.terms[size - 1];
        if last.monomial.product.is_empty() {
            last.coefficient -= rhs;
        } else {
            let mut neg = C::zero();
            neg -= rhs;
            self.terms.push(Term::new_constant(neg));
        }

        self
    }
}

impl<O, I, C, P> Mul<Polynomial<O, I, C, P>> for &Monomial<O, I, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn mul(self, mut rhs: Polynomial<O, I, C, P>) -> Self::Output {
        for term in rhs.terms.iter_mut() {
            term.monomial = std::mem::replace(&mut term.monomial, Monomial::one()) * self.clone();
        }

        rhs
    }
}

impl<O, I, C, P> Mul for &Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn mul(self, rhs: &Polynomial<O, I, C, P>) -> Self::Output {
        let mut new_terms = std::collections::BTreeMap::new();

        let (outer, inner) = if self.terms.len() > rhs.terms.len() {
            (&rhs.terms, &self.terms)
        } else {
            (&self.terms, &rhs.terms)
        };

        for a in outer {
            for b in inner {
                let new_term = a.clone() * b.clone();

                let entry = new_terms.entry(new_term.monomial);
                match entry {
                    std::collections::btree_map::Entry::Vacant(e) => {
                        if !new_term.coefficient.is_zero() {
                            e.insert(new_term.coefficient);
                        }
                    }
                    std::collections::btree_map::Entry::Occupied(mut e) => {
                        *e.get_mut() += new_term.coefficient;
                        if e.get().is_zero() {
                            e.remove();
                        }
                    }
                }
            }
        }

        let terms: Vec<_> = new_terms
            .into_iter()
            .rev()
            .map(|(monomial, coefficient)| Term {
                coefficient,
                monomial,
            })
            .collect();
        Self::Output { terms }
    }
}

impl<O, I, C, P> Mul for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;
    fn mul(self, rhs: Polynomial<O, I, C, P>) -> Self::Output {
        &self * &rhs
    }
}

impl<O, I, C, P> Mul<C> for &Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
{
    type Output = Polynomial<O, I, C, P>;

    fn mul(self, rhs: C) -> Self::Output {
        self * &Polynomial::new_constant(rhs)
    }
}

impl<O, I, C, P, T> num_traits::pow::Pow<T> for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: CommutativeRing,
    P: Exponent,
    T: Clone + num_traits::Zero + std::ops::Rem + std::ops::DivAssign + std::convert::From<u8>,
    <T as std::ops::Rem>::Output: num_traits::One + PartialEq,
{
    type Output = Polynomial<O, I, C, P>;
    fn pow(mut self, mut rhs: T) -> Self {
        let mut ret = Polynomial::new_constant(C::one());

        if !rhs.is_zero() {
            loop {
                let rem = rhs.clone() % T::from(2u8);
                rhs /= T::from(2u8);
                if num_traits::One::is_one(&rem) {
                    ret = ret * self.clone();
                }

                if rhs.is_zero() {
                    break;
                }
                self = self.clone() * self;
            }
        }

        ret
    }
}

impl<I: Id, E: Exponent + std::fmt::Display> std::fmt::Display for VariablePower<I, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.id.display(f)?;
        if !self.power.is_one() {
            write!(f, "^{}", self.power)?;
        }

        Ok(())
    }
}

impl<O, I, P> std::fmt::Display for Monomial<O, I, P>
where
    I: Id,
    P: Exponent + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.product.iter();
        if let Some(mut v) = iter.next() {
            loop {
                write!(f, "{}", v)?;
                v = if let Some(v) = iter.next() {
                    f.write_char('*')?;
                    v
                } else {
                    break;
                }
            }
            Ok(())
        } else {
            write!(f, "1")
        }
    }
}

impl<O, I, C, P> std::fmt::Display for Term<O, I, C, P>
where
    I: Id,
    C: CommutativeRing + std::fmt::Display,
    P: Exponent + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.coefficient.is_one(), self.monomial.product.is_empty()) {
            (false, false) => write!(f, "{}*{}", self.coefficient, self.monomial),
            (false, true) => std::fmt::Display::fmt(&self.coefficient, f),
            (true, false) => std::fmt::Display::fmt(&self.monomial, f),
            (true, true) => write!(f, "1"),
        }
    }
}

impl<O, I, C, P> std::fmt::Display for Polynomial<O, I, C, P>
where
    I: Id,
    C: CommutativeRing + std::fmt::Display,
    P: Exponent + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.terms.iter();
        match iter.next() {
            None => {
                f.write_char('0')?;
                return Ok(());
            }
            Some(t) => {
                t.fmt(f)?;
            }
        }

        for t in iter {
            write!(f, " + {}", t)?;
        }

        Ok(())
    }
}

impl CommutativeRing for i32 {}
impl Exponent for u16 {}
impl Exponent for i16 {}
impl Exponent for u32 {}
impl Exponent for i32 {}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use num::Zero;
    use num_traits::Pow;

    use super::*;

    pub type SmallPoly = Polynomial<monomial_ordering::Lex, u8, i32, u16>;

    #[test]
    fn map_build_time() {
        let mut elapsed = Duration::ZERO;
        for _ in 0..100 {
            // Build a random sparse polynomial
            let mut terms = Vec::new();
            for _ in 0..2000 {
                let mut monomial = Vec::new();
                for i in 0u8..100 {
                    if rand::random() {
                        continue;
                    }
                    let power: u16 = rand::random::<u16>() % 52u16;
                    monomial.push(VariablePower::new(i, power));
                }
                terms.push(Term::new_multi_vars(42i32, monomial));
            }
            // Properly sort the terms:
            let p = SmallPoly::from_terms(terms);

            use std::time::Instant;
            let now = Instant::now();

            // Code block to measure.
            let map: std::collections::BTreeMap<_, _>;
            {
                map = p
                    .terms
                    .into_iter()
                    .rev()
                    .map(|term| (term.monomial, term.coefficient))
                    .collect();
            }

            elapsed += now.elapsed();
            if let Some((m, c)) = map.first_key_value() {
                println!("{:#?}, {}", m, c);
            }
        }
        println!("Elapsed: {:.2?}", elapsed);
    }

    #[test]
    fn addition_and_subtraction_ordering() {
        let [z, y, x]: [SmallPoly; 3] = SmallPoly::new_variables([0u8, 1u8, 2u8])
            .try_into()
            .unwrap();
        let a = x.clone() + y.clone() + z.clone() + 42;
        let b = y + 42 + z + x;

        assert_eq!(a, b);
        println!("a = {}", a);

        let c = a.clone() + b;
        println!("c = {}", c);

        assert_eq!(c.terms.len(), 4);
        // For the first 3 terms:
        for i in 0..3 {
            // The coefficient is 2:
            assert_eq!(c.terms[i].coefficient, 2);
            // It has only one variable:
            assert_eq!(c.terms[i].monomial.product.len(), 1);
            // The power of such variable is 1:
            assert_eq!(c.terms[i].monomial.product[0].power, 1);
            // The terms are in decreasing order:
            assert_eq!(c.terms[i].monomial.product[0].id, 2 - i as u8);
        }

        // The last term has no variables and the coefficient is 84:
        assert!(c.terms[3].monomial.product.is_empty());
        assert_eq!(c.terms[3].coefficient, 84);

        // The inverse operation must yield the original polynomial:
        let d = c - a.clone();
        assert_eq!(a, d);
    }

    #[test]
    fn many_terms_addition_and_subtraction() {
        let [x0, x1, x2, x3, x4, x5, x6, x7]: [SmallPoly; 8] =
            SmallPoly::new_variables(0u8..8).try_into().unwrap();

        let a = x0 + x1 + x3.clone() + x4;
        let b = x2 + x3 - x5 + x6 + x7 - 42;

        // Test commutativity:
        let c = a.clone() + b.clone();
        let d = b.clone() + a.clone();

        println!("c = {}", c);

        assert_eq!(c, d);

        // Check the first 8 terms:
        for i in 0..8 {
            let t = &c.terms[i];
            let m = &t.monomial;
            let var = &m.product[0];

            assert_eq!(m.product.len(), 1);
            assert_eq!(var.power, 1);
            assert_eq!(var.id, 7 - i as u8);

            let expected_coef = match var.id {
                3 => 2,
                5 => -1,
                _ => 1,
            };
            assert_eq!(t.coefficient, expected_coef);
        }

        // Check the last term:
        assert_eq!(c.terms[8].coefficient, -42);
        assert!(c.terms[8].monomial.product.is_empty());

        // Test that we get the original polynomials by subtracting:
        let a_restored = c - b.clone();
        let b_restored = d - a.clone();

        println!("a_restored = {}", a_restored);
        println!("b_restored = {}", b_restored);

        assert_eq!(a, a_restored);
        assert_eq!(b, b_restored);
    }

    fn factorable_polynomial() -> SmallPoly {
        let [y, x]: [SmallPoly; 2] = SmallPoly::new_variables([0u8, 1u8]).try_into().unwrap();

        (x.clone() - 1) * (x.clone() - 5) * (x.clone() + 12) * (y.clone() - 42) * (y.clone() + 42)
    }

    #[test]
    fn assemble_factors() {
        let p = factorable_polynomial();

        println!("{}", p);

        let t = SmallPoly::new_monomial_term;

        // According to symbolab.com, answer should be:
        // -1764x^3 + x^3y^2 + 60y^2 - 10584x^2 + 6x^2y^2 - 67xy^2 + 118188x - 105840
        let expected = t(-1764, 1, 3)
            + t(1, 1, 3) * t(1, 0, 2)
            + t(60, 0, 2)
            + t(-10584, 1, 2)
            + t(6, 1, 2) * t(1, 0, 2)
            + t(-67, 1, 1) * t(1, 0, 2)
            + t(118188, 1, 1)
            - 105840;

        assert_eq!(p, expected);
    }

    #[test]
    fn multiply_by_zero() {
        let p = factorable_polynomial();

        let zero = Polynomial::new_constant(0);

        let a = p.clone() * zero.clone();
        let b = zero.clone() * p.clone();
        let c = &p * 0;

        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(a, zero);

        assert_eq!(a, Polynomial { terms: Vec::new() });
    }

    #[test]
    fn multiply_by_constant() {
        let p = factorable_polynomial();

        let a = &p * -42;

        for (a, p) in a.terms.into_iter().zip(p.terms) {
            assert_eq!(a.monomial, p.monomial);
            assert_eq!(a.coefficient, -42 * p.coefficient);
        }
    }

    #[test]
    fn multiply_by_minus_one() {
        let p = factorable_polynomial();
        let a = &p * -1;

        assert_eq!(a, -p);
    }

    #[test]
    fn inverse_division() {
        let [y, x]: [SmallPoly; 2] = SmallPoly::new_variables([0u8, 1u8]).try_into().unwrap();
        let a = x.clone() - y.clone();
        let b = x.clone() * x.clone() + x.clone() * y.clone() + y.clone() * y.clone();

        let c = a * b;
        println!("{}", c);

        assert_eq!(
            c,
            x.clone() * x.clone() * x.clone() - y.clone() * y.clone() * y.clone()
        );
    }

    #[test]
    fn high_power() {
        let x = SmallPoly::new_monomial_term(1, 0, 1);

        assert_eq!(x.pow(47).terms[0].monomial.product[0].power, 47);
    }

    #[test]
    fn factor_power() {
        let [y, x]: [SmallPoly; 2] = SmallPoly::new_variables([0u8, 1u8]).try_into().unwrap();

        let p = (x.clone() * y.clone() - 1).pow(5);
        println!("{}", p);
    }

    #[test]
    fn derivative() {
        let [y, x]: [SmallPoly; 2] = SmallPoly::new_variables([0u8, 1u8]).try_into().unwrap();
        let p = x.clone() * x.clone() + x.clone() * y.clone() + y.clone() * y.clone();
        println!("p: {}", p);

        let dp_dy = p.clone().derivative(&0);
        let dp_dx = p.derivative(&1);
        println!("dp/dy: {}\ndp/dx: {}", dp_dy, dp_dx);

        let expected_dp_dy = x.clone() + &y.clone() * 2i32;
        assert_eq!(dp_dy, expected_dp_dy);

        let expected_dp_dx = &x.clone() * 2i32 + y.clone();
        assert_eq!(dp_dx, expected_dp_dx);
    }

    #[test]
    fn monomial_test_for_shared_variable() {
        let [x0, x1, x2, x3, x4, x5, x6, x7]: [SmallPoly; 8] =
            SmallPoly::new_variables(0u8..8).try_into().unwrap();

        let p = x0.clone() * x2.clone() * x4.clone() * x6.clone();
        let q = x7.clone() * x5.clone() * x3.clone() * x1.clone();

        assert!(!p.terms[0]
            .monomial
            .has_shared_variables(&q.terms[0].monomial));

        let p = p * x7;

        assert!(p.terms[0]
            .monomial
            .has_shared_variables(&q.terms[0].monomial));
    }

    #[test]
    fn monomial_gcd() {
        let [w, z, y, x]: [SmallPoly; 4] =
            SmallPoly::new_variables([0u8, 1, 2, 3]).try_into().unwrap();

        let a = x.clone() * x.clone() * z.clone() * z.clone();
        let b = y.clone() * y.clone() * w.clone() * w.clone();

        // Coprimes:
        let gcd1 = a.terms[0].monomial.clone().gcd(&b.terms[0].monomial);
        let gcd2 = b.terms[0].monomial.clone().gcd(&a.terms[0].monomial);
        assert!(gcd1 == gcd2);
        assert!(gcd1.is_one());
        assert!(gcd1.total_power.is_zero());

        // GCD is y:
        let c = x.clone() * y.clone() * z.clone();

        let gcd1 = b.terms[0].monomial.clone().gcd(&c.terms[0].monomial);
        let gcd2 = c.terms[0].monomial.clone().gcd(&b.terms[0].monomial);
        assert!(gcd1 == gcd2);
        assert!(gcd1 == y.terms[0].monomial);

        // GCD is xz²
        let d = c.clone() * z.clone();

        let result = x.clone() * z.clone() * z.clone();

        let gcd1 = a.terms[0].monomial.clone().gcd(&d.terms[0].monomial);
        let gcd2 = d.terms[0].monomial.clone().gcd(&a.terms[0].monomial);
        assert!(gcd1 == gcd2);
        assert!(gcd1 == result.terms[0].monomial); // TODO: invert the assertion

        // GCD is one of the inputs (xyz):
        let e = a.clone() * b.clone();
        let gcd1 = e.terms[0].monomial.clone().gcd(&c.terms[0].monomial);
        let gcd2 = c.terms[0].monomial.clone().gcd(&e.terms[0].monomial);
        assert!(gcd1 == gcd2);
        assert!(gcd1 == c.terms[0].monomial);
    }
}
