// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-authority gate for semantic quantified UNSAT results.

use super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

impl Executor {
    /// Publish a sound quantified-instance refutation only when no proof
    /// artifact is mandatory. These bounded inner solves currently prove the
    /// mathematical verdict but do not translate their standalone assumptions
    /// back to authored `forall_inst` steps. Mandatory proof modes fail closed;
    /// best-effort/no-proof modes use the same proof-suppressed publisher as the
    /// sealed consequence certificate.
    pub(super) fn quantified_semantic_unsat_or_unknown(
        &mut self,
        missing_proof_reason: UnknownReason,
    ) -> Result<SolveResult> {
        if self.translated_unsat_proof_required() {
            // (#bv-mbqi-false-instance-authority, P3b) Before discarding the
            // verdict, consult the checked SAT-refutation sidecar for the
            // EXACT public query. The refutation-driven re-solve can mint a
            // sidecar whose every original clause — including a pushed
            // eval-folded-`false` instance — is strict-authenticated against
            // the authored roots; that token IS a translated authored-scope
            // refutation, and clearing it below would destroy the only
            // artifact this gate exists to demand. The token re-verifies
            // epoch, source stamp, ordered roots, and assumptions at this
            // exact moment, so a disposable inner solve's artifact can never
            // pass. The final publication still runs the ordinary
            // certification funnel, which re-validates the same sidecar.
            // Covered by the #quant-unit-authority kill switch: with the
            // switch off this gate is byte-for-byte the pre-P3b downgrade.
            //
            // (#bitblast-original-clause-authority) When no trace-bound
            // sidecar exists — the UFBV bit-blast route's original gate
            // clauses reference SAT variables absent from `var_to_term`, so
            // one can never mint for that family — a recorded qpf
            // premise-forced instance is re-derived trace-free at this exact
            // moment instead: authored-root membership, strict `forall_inst`
            // substitution replay, and an independently re-lowered,
            // fully-replayed Bool/BV+UF-leaf refutation of the exact
            // instance. Same kill switch, fail-closed on every leg.
            if crate::quant_unit_authority::quant_unit_authority_enabled()
                && (self.checked_sat_refutation_authorizes_current_query()
                    || self.checked_qpf_instance_refutation_authorizes_current_query())
            {
                self.last_unknown_reason = None;
                return Ok(SolveResult::unsat());
            }
            self.clear_cegqi_inner_unsat_artifacts();
            self.last_unknown_reason = Some(missing_proof_reason);
            Ok(SolveResult::Unknown)
        } else {
            Ok(self.publish_quantified_verdict_only_unsat())
        }
    }
}
