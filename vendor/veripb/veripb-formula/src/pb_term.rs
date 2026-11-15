//! Trait for pseudo-Boolean terms.

use crate::{lit::Lit, pb_constraint::Int};

/// A pseudo-Boolean term consists of a coefficient and a literal.
pub trait PBTerm {
    /// Coefficient type of the [`PBTerm`].
    type CoeffType: Int;

    /// Get the coefficient of the [`PBTerm`].
    fn get_coeff(&self) -> &Self::CoeffType;

    /// Set the coefficient of the [`PBTerm`] to `coeff`.
    fn set_coeff(&mut self, coeff: Self::CoeffType);

    /// Get the literal of the [`PBTerm`].
    fn get_lit(&self) -> Lit;

    /// Negate the [`PBTerm`], which negates the literal of the term.
    fn negate(&mut self);

    /// Divide the coefficient of [`PBTerm`] by `divisor` rounding up to the next biggest integer.
    fn divide_round_up(&mut self, divisor: &Self::CoeffType);
}
