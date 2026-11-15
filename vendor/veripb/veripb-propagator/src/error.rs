//! Error types for propagator.

use thiserror::Error;

/// Error type for the propagation engine.
#[derive(Debug, Error)]
pub enum PropagatorError {
    #[error(
        "This constraint has already been attached to a propagator. The constraint needs to be detached before it can be attached again."
    )]
    AttachingAttached,

    #[error("This constraint is not been attached. Hence it cannot be detached from a propagator.")]
    DetachingUnattached,

    #[error("This constraint has been attached to a different propagator.")]
    AttachedToOtherPropagator,

    #[error("No propagator for this type of constraint in the propagation set!")]
    TypeOfPropagatorNotInSet,

    #[error("The given solution is conflicting with constraint {0} in the database.")]
    SolutionConflictingWithConstraint(usize),

    #[error(
        "The given solution is conflicting with on constraint on the saved trail. Use the option '--trace-failed' to see which constraints propagate which literals. A wrong cutting planes ('pol') derivation earlier in the proof can also cause this; add '--trace-pol' (with a trace option such as '--trace-lines') to trace pol derivations."
    )]
    SolutionConflictingWithSavedTrail,

    #[error("The trail already contains the negated literal")]
    TrailContainsNegatedLit,
}
