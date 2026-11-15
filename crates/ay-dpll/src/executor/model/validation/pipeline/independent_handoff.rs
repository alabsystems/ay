// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The independent-gate handoff for a candidate the canonical evaluator could
//! not finish validating.

use ay_model_check::GateVerdict;

use crate::executor::model::Executor;

impl Executor {
    /// Whether the independent gate confirms the current candidate after the
    /// canonical evaluator stopped at an array or datatype ground assertion.
    ///
    /// For an ARRAY ground gap, a refusal arms the same reactive re-solves the
    /// emission gate arms for the same verdict ([`Self::arm_gate_refutation_retries`],
    /// [`Self::arm_gate_unconfirmed_retries`]). Before #bv-array-delegation
    /// an array assertion the candidate falsifies or cannot evaluate could be
    /// counted as verified (bit-blast coverage, or the array solver's #8785
    /// delegation), so the candidate travelled on to the emission gate. That
    /// gate's refusal armed the retry. Refused here instead, the candidate
    /// must still earn the retry. Measured on `r1_and_nestedconst_sat`
    /// (QF_AUFBV): its first candidate leaves `y` unset against
    /// `(= y (select (select m k) #x...3))`, and its preprocessing-free
    /// re-solve publishes a model z3 accepts. Arming only schedules a re-solve
    /// that passes every gate again; this candidate stays the caller's
    /// fail-closed Unknown. A datatype-only gap never reached the emission gate
    /// and arms nothing, as before.
    pub(super) fn independent_handoff_confirms(&mut self, array_ground_gap: bool) -> bool {
        let verdict = self.confirm_sat_with_independent_gate();
        if matches!(verdict, GateVerdict::ConfirmedSat) {
            return true;
        }
        if !array_ground_gap || self.evaluation_stop_origin().is_some() {
            return false;
        }
        match verdict {
            GateVerdict::ModelViolates { assertion } => {
                // A published stop is answered Unknown by the caller.
                let _ = self.arm_gate_refutation_retries(assertion);
            }
            GateVerdict::CannotConfirm { .. } => self.arm_gate_unconfirmed_retries(),
            GateVerdict::ConfirmedSat => {}
        }
        false
    }
}
