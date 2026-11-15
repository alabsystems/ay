//! A general pseudo-Boolean term.

use malachite_bigint::BigInt;
use num_traits::Zero;

use crate::{
    lit::Lit, pb_constraint::Int, pb_term::PBTerm, prelude::VarNameLookup,
    to_pretty_string::ToPrettyString,
};

/// A general pseudo-Boolean term consists of an integer coefficient and a literal.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct GeneralPBTerm<C>
where
    C: Int,
{
    pub coeff: C,
    pub lit: Lit,
}

impl<C> GeneralPBTerm<C>
where
    C: Int,
{
    /// Construct a new term with coefficient `coeff` and literal `lit`.
    #[inline]
    pub fn new(coeff: C, lit: Lit) -> Self {
        GeneralPBTerm { coeff, lit }
    }

    /// Negate a term.
    ///
    /// The literal in the term is negated and the coefficient is negated.
    #[inline]
    pub fn change_negation(&mut self) {
        self.lit.negate();
        self.coeff = -self.coeff.clone();
    }

    /// Add `term` to `self`. This operation consumes `term` and changes `self`.
    ///
    /// The addition normalizes the term, i.e. the coefficient is non-negative after the addition. The amount that was cancelled due to normalization is returned by the function and should be subtracted from the degree or added to the objective constant.
    ///
    /// This function works for normalized and non-normalized constraints.
    #[inline]
    pub fn add_with(&mut self, term: GeneralPBTerm<C>) -> C {
        match (self.lit.is_negated(), term.lit.is_negated()) {
            (false, false) | (true, true) => {
                self.coeff += term.coeff;
                Zero::zero()
            }
            _ => {
                if self.coeff >= term.coeff {
                    self.coeff -= term.coeff.clone();
                    term.coeff
                } else {
                    self.lit.negate();
                    self.coeff = term.coeff.clone() - self.coeff.clone();
                    term.coeff - self.coeff.clone()
                }
            }
        }
    }

    /// Cast the term to [`i128`] and multiply the coefficient with `factor`.
    #[inline]
    pub fn multiply_to_i128(&self, factor: i128) -> GeneralPBTerm<i128> {
        GeneralPBTerm::new(
            TryInto::<i128>::try_into(self.coeff.clone()).ok().unwrap() * factor,
            self.lit,
        )
    }

    /// Cast the term to [`BigInt`] and multiply the coefficient with `factor`.
    #[inline]
    pub fn multiply_to_bigint(&self, factor: &BigInt) -> GeneralPBTerm<BigInt> {
        GeneralPBTerm::new(self.coeff.clone().into() * factor, self.lit)
    }
}

impl<C> PBTerm for GeneralPBTerm<C>
where
    C: Int,
{
    type CoeffType = C;

    #[inline]
    fn negate(&mut self) {
        self.lit.negate();
    }

    #[inline]
    fn get_lit(&self) -> Lit {
        self.lit
    }

    #[inline]
    fn get_coeff(&self) -> &C {
        &self.coeff
    }

    #[inline]
    fn set_coeff(&mut self, coeff: Self::CoeffType) {
        self.coeff = coeff;
    }

    #[inline]
    fn divide_round_up(&mut self, divisor: &Self::CoeffType) {
        self.coeff = self.coeff.div_ceil(divisor);
    }
}

impl From<GeneralPBTerm<i64>> for GeneralPBTerm<i128> {
    #[inline]
    fn from(value: GeneralPBTerm<i64>) -> Self {
        GeneralPBTerm::new(value.coeff.into(), value.lit)
    }
}

impl From<GeneralPBTerm<i64>> for GeneralPBTerm<BigInt> {
    #[inline]
    fn from(value: GeneralPBTerm<i64>) -> Self {
        GeneralPBTerm::new(value.coeff.into(), value.lit)
    }
}

impl From<GeneralPBTerm<i128>> for GeneralPBTerm<BigInt> {
    #[inline]
    fn from(value: GeneralPBTerm<i128>) -> Self {
        GeneralPBTerm::new(value.coeff.into(), value.lit)
    }
}

/// **ATTENTION:** The order of term is defined with respect to the literal of the term. The coefficient is ignored for this check.
impl<N: Int> PartialOrd for GeneralPBTerm<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// **ATTENTION:** The order of term is defined with respect to the literal of the term. The coefficient is ignored for this check.
impl<N: Int> Ord for GeneralPBTerm<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.lit.cmp(&other.lit)
    }
}

impl<N: Int> ToPrettyString for GeneralPBTerm<N> {
    #[inline]
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        format!("{} {}", self.coeff, self.lit.to_pretty_string(var_names))
    }
}
