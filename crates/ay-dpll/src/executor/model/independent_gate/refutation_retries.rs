// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The reactive re-solves a gate verdict against the current candidate arms,
//! shared by the emission gate and the validation handoff.

use ay_core::TermId;

use crate::executor::Executor;

impl Executor {
    /// Arm every reactive re-solve that a `ModelViolates` verdict on the
    /// current candidate is evidence for. `false` means an evaluation stop was
    /// published, and the caller must answer Unknown.
    ///
    /// Arming only redirects search on a re-solve: each retry is latched to
    /// fire once in `check_sat_guarded`, and its verdict passes every gate
    /// again. The candidate refuted here is still downgraded by the caller.
    pub(in crate::executor) fn arm_gate_refutation_retries(&mut self, assertion: TermId) -> bool {
        // #qfax-cegar: this rejection is the same evidence class the
        // strict-oracle hook feeds on — derive the sound
        // pattern-blocking clause here too, so the dispatch's
        // stage-4 refinement fires on gate-caught violations
        // (previously only strict-oracle rejections derived).
        self.derive_qfax_refinement_clause(assertion);
        if self.publish_evaluation_stop() {
            return false;
        }
        self.last_rejected_array_assertion = Some(assertion);
        // #array-refutation-retry: arms the single written-index
        // re-solve in `check_sat_guarded`.
        self.array_model_refuted = true;
        // #uflia-cong-repair-arm: a UFLIA-lane refutation is the exact
        // trigger for the reactive congruence-repair re-solve. Record
        // it (scoped to the UFLIA lane so no other theory's refutation
        // arms a wasteful retry); `check_sat_guarded` reads this to arm
        // `discover_congruence_repair_eqs` and re-solve ONCE. This only
        // redirects search on a re-solve; the caller's downgrade is
        // unaffected.
        if self.uflia_congruence_lane {
            self.uflia_congruence_gate_rejected = true;
        }
        // #abv-subst-model-retry: a refutation of a model built by the
        // substitution-carrying eager BV lane arms the single
        // preprocessing-free re-solve (`check_sat_guarded`), the same
        // reactive pattern as the UFLIA arm above. Scoped to
        // `bv_subst_lane` so no other theory's refutation triggers a
        // wasteful retry.
        if self.bv_subst_lane {
            self.bv_subst_model_rejected = true;
        }
        self.arm_qfax_isolated_retry();
        true
    }

    /// Arm the re-solve that a `CannotConfirm` verdict on the current
    /// candidate is evidence for.
    ///
    /// #qfax-isolated-lane-retry: an UNCONFIRMABLE model from the
    /// LIA-less isolated QF_AUFLIA ladder is the same recoverable
    /// evidence class as a strict refutation of one — the ladder
    /// leaves Int-sorted witnesses (`i = (sk A B)`) without an
    /// arithmetic slot, which is precisely a coverage gap — so it
    /// arms the same single combiner re-solve. Scoped to the lane
    /// and retry-once; a still-unconfirmed re-solve stays Unknown.
    pub(in crate::executor) fn arm_gate_unconfirmed_retries(&mut self) {
        self.arm_qfax_isolated_retry();
    }

    /// #qfax-isolated-lane-retry: a gate refutation of a model the
    /// LIA-less isolated QF_AUFLIA ladder published arms the single
    /// combiner re-solve (`check_sat_guarded`), the same reactive
    /// pattern as the BV arm. Scoped to `qfax_isolated_lane` so no
    /// other route's rejection buys a second solve.
    fn arm_qfax_isolated_retry(&mut self) {
        if self.qfax_isolated_lane {
            self.qfax_isolated_model_rejected = true;
        }
    }
}
