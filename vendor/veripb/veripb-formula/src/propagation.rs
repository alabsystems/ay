//! Common types used for unit propagation.

use std::num::NonZeroUsize;

/// Return type for the propagation on a constraint (with respect to a partial assignment).
#[derive(Debug, Clone, Copy)]
pub enum ConstraintPropagationResult {
    /// The constraint did not propagate anything and is not falsified by the partial assignment.
    NoPropagation,
    /// The constraint propagated literals and is not falsified by the partial assignment.
    Propagated,
    /// The constraint is falsified by the partial assignment.
    Conflict,
}

/// Hint for which constraint should be propagated in a reverse unit propagation (RUP) check.
#[derive(Debug, Clone, Copy)]
pub enum RUPHint {
    /// The constraint with the given ID should be propagated.
    ConstraintId(NonZeroUsize),
    /// The negated constraint should be propagated.
    NegatedPremise,
}
