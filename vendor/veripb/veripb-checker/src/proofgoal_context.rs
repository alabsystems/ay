//! Proofgoal subproof [`Subcontext`](crate::context::Subcontext) structure.

/// [`Subcontext`](crate::context::Subcontext) for proofgoal subproofs.
#[derive(Debug, Default)]
pub struct ProofgoalContext {
    /// Start constraint ID of the subproof.
    pub subproof_start_id: usize,
    /// Whether *this* proofgoal, once discharged, establishes the contradiction
    /// that a proof-by-contradiction subproof owes.
    ///
    /// A proofgoal subproof derives a contradiction from the enclosing
    /// database together with the goal's counterexample premises. That
    /// discharges the enclosing proof-by-contradiction subproof only if those
    /// premises are themselves entailed by the enclosing database — otherwise
    /// the contradiction was bought with an extra assumption and says nothing
    /// about the database alone. This flag records that the premises are
    /// entailed, by the one constraint that distinguishes a
    /// proof-by-contradiction subproof: the negated conclusion the rule pushed
    /// as its `additional_hint`. See [`crate::rules::ProofgoalChecker`].
    pub discharges_pbc_contradiction: bool,
}

impl ProofgoalContext {
    /// Constructs a new proofgoal context.
    #[inline]
    pub fn new(start_id: usize) -> Self {
        ProofgoalContext {
            subproof_start_id: start_id,
            discharges_pbc_contradiction: false,
        }
    }
}
