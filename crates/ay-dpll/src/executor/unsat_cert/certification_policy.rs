// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Presentation policy and bounded diagnostics for UNSAT certification.

use ay_core::TermId;

use super::{probe_cert_reject, Executor};
use crate::executor_types::{Result, SolveResult};

impl Executor {
    /// Whether independently certified UNSAT must also carry an accepted
    /// authored-scope presentation.
    ///
    /// Internal proof tracking is not a user proof request. Only explicit
    /// proof output, SMT-LIB `:produce-proofs`, or strict verification makes a
    /// missing translation verdict-relevant; self-check also requires a
    /// checked refutation, though an independent sidecar can meet that demand.
    pub(in crate::executor) fn strict_unsat_presentation_required(&self) -> bool {
        self.proof_artifact_required
            || self.self_check()
            || self.verification_level().has_proof_checking()
            || self.strict_proofs_enabled()
            || self.produce_proofs_option_enabled()
    }

    /// Whether an independent sidecar is barred by a promised Alethe artifact.
    ///
    /// Bare self-check asks for independently verified truth, not the exported
    /// document. The checked SAT-refutation sidecar is that refutation, so only
    /// artifact/export/checking modes block it (#letleak wall 3).
    pub(super) fn independent_sidecar_blocked_by_presentation(&self) -> bool {
        let produce_proofs = self.produce_proofs_option_enabled();
        probe_cert_reject(|| {
            format!(
                "presentation_promised legs: artifact_required={} proof_checking={} strict_proofs={} produce_proofs_opt={}",
                self.proof_artifact_required,
                self.verification_level().has_proof_checking(),
                self.strict_proofs_enabled(),
                produce_proofs,
            )
        });
        self.proof_artifact_required
            || self.verification_level().has_proof_checking()
            || self.strict_proofs_enabled()
            || produce_proofs
    }

    fn produce_proofs_option_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-proofs"),
            Some(ay_frontend::OptionValue::Bool(true))
        )
    }

    pub(super) fn probe_unsat_certificate_entry(&self) {
        probe_cert_reject(|| {
            format!(
                "mint_unsat_certificate ENTER: strict_required={} self_check={} sidecar_present={}",
                self.strict_unsat_presentation_required(),
                self.self_check(),
                self.last_checked_sat_refutation.is_some(),
            )
        });
    }

    /// Attribute step (4)'s final accepting/declining nested solve.
    pub(super) fn probe_reconfirmation_outcome(
        &self,
        nested: &Executor,
        verdict: &Result<SolveResult>,
        problem: &[TermId],
    ) {
        probe_cert_reject(|| {
            format!(
                "RECONFIRM(4): verdict={:?} unknown_origin={:?} unknown_reason={:?} \
                 last_proof={} tracker_steps={} problem_terms={}",
                verdict.as_ref().map(ToString::to_string),
                nested.last_unknown_origin,
                nested.last_unknown_reason,
                nested.last_proof.as_ref().map_or_else(
                    || "None".to_string(),
                    |proof| format!("Some({} steps)", proof.steps.len())
                ),
                nested.proof_tracker.num_steps(),
                problem.len(),
            )
        });
        if !matches!(verdict, Ok(result) if result.is_unsat()) {
            probe_cert_reject(|| {
                format!(
                    "RECONFIRM(4) DECLINED scope: {}",
                    self.bounded_cert_reject_probe_terms(problem)
                )
            });
        }
    }
}
