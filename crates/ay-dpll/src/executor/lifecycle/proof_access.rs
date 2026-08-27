// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Executor;
use ay_core::Proof;

impl Executor {
    /// Enable mandatory, unbudgeted proof collection without recording an
    /// explicit translated-artifact demand.
    ///
    /// Self-check requires independently verified UNSAT truth, while exported
    /// Alethe is a separate presentation contract. Routing self-check through
    /// [`Self::set_produce_proofs`] would set `proof_artifact_required` and
    /// reject independent certification lanes that already proved the result.
    /// An explicit proof request still makes the artifact mandatory regardless
    /// of call order.
    pub fn set_mandatory_proof_collection(&mut self) {
        self.proof_output_requested = true;
        self.proof_tracker.enable();
        self.ctx.set_retain_parsed_assertions(true);
        self.proof_reconstruction_step_budget = None;
    }

    /// Whether an epoch/source/roots/assumptions-bound SAT sidecar supplies
    /// self-check's independently verified refutation authority.
    pub(in crate::executor) fn checked_refutation_satisfies_self_check(&self) -> bool {
        self.checked_sat_refutation_authorizes_current_query()
    }

    /// Emit bounded diagnostics before retiring a checked SAT sidecar.
    pub(in crate::executor) fn report_checked_refutation_clear(&self, boundary: &str) {
        if ay_core::misc_cli_flags().debug_cert && self.last_checked_sat_refutation.is_some() {
            eprintln!("CERT/sidecar cleared by {boundary} exec={self:p}");
        }
    }

    /// Proof from the last UNSAT result.
    ///
    /// Returns `None` unless proof output was requested when the last UNSAT solve
    /// began. Later option changes cannot expose or hide that solve's retained
    /// artifact. Proof checking can use an internal refutation without making it
    /// part of the public proof surface.
    #[must_use]
    pub fn last_proof(&self) -> Option<&Proof> {
        let proof_output_requested = self
            .unsat_query_epoch
            .as_ref()
            .is_some_and(|epoch| epoch.proof_output_is_current(self));
        if self.last_result_is_unsat()
            && proof_output_requested
            && !self.last_unsat_proof_reconstruction_suppressed
        {
            self.last_proof.as_ref()
        } else {
            None
        }
    }

    /// Test-only view of the native certificate retained for mandatory
    /// internal publication checking. Unlike [`Self::last_proof`], this does
    /// not pretend an unrequested proof is part of the public artifact surface.
    #[cfg(test)]
    pub(crate) fn retained_internal_proof_for_test(&self) -> Option<&Proof> {
        self.last_proof.as_ref()
    }

    /// Why the last refutation carries no derivation, when it carries none.
    ///
    /// Diagnostic only — no gate, verdict, certificate, or export consults it.
    /// It exists so the one-line `(step t0 (cl) :rule hole)` artifact is
    /// attributable: three unrelated conditions produce that exact document,
    /// and a corpus census over emitted artifacts could not tell them apart.
    #[must_use]
    pub fn last_proof_decline(&self) -> Option<crate::executor::ProofDeclineMechanism> {
        self.last_proof_decline
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::{Logic, Solver, Sort};
    use crate::{SolveResult, VerificationLevel};

    fn install_unsat_proof(executor: &mut Executor) {
        executor.last_result = Some(SolveResult::unsat());
        executor.last_proof = Some(Proof::new());
    }

    #[test]
    fn last_proof_uses_solve_time_output_request() {
        let mut unrequested = Executor::new();
        unrequested.begin_public_solve(false);
        install_unsat_proof(&mut unrequested);
        assert!(unrequested.last_proof().is_none());

        unrequested.set_verification_level(VerificationLevel::ProofChecked);
        assert!(unrequested.last_proof().is_none());
        unrequested.set_produce_proofs(true);
        assert!(unrequested.unsat_query_epoch.is_some());
        assert!(unrequested.last_proof().is_none());
        assert!(unrequested.last_proof.is_some(), "anti-vacuity");

        let mut output = Executor::new();
        output.set_produce_proofs(true);
        output.begin_public_solve(false);
        install_unsat_proof(&mut output);
        output.set_produce_proofs(false);
        output.set_verification_level(VerificationLevel::Trusted);
        assert!(output.last_proof().is_some());
        output.last_unsat_proof_reconstruction_suppressed = true;
        assert!(output.last_proof().is_none());
        output.last_unsat_proof_reconstruction_suppressed = false;
        assert!(output.last_proof().is_some());
        output.last_proof = None;
        assert!(output.last_proof().is_none());
        output.last_proof = Some(Proof::new());
        output.last_result = Some(SolveResult::Sat);
        assert!(output.last_proof().is_none());
        output.last_result = Some(SolveResult::unsat());
        assert!(output.last_proof().is_some());
        assert!(output.last_proof.is_some());
        output.advance_query_authority_epoch();
        assert!(output.last_proof().is_none());
        assert!(output.last_proof.is_some(), "staling must retain raw state");
        assert!(output
            .try_export_last_proof_alethe_for_problem_scope()
            .is_none());
        assert!(output
            .try_export_last_proof_alethe_for_problem_scope_to(&mut Vec::new())
            .is_none());
    }

    #[test]
    fn proof_checking_solve_does_not_expose_proof_without_output_request() {
        for level in [
            VerificationLevel::ProofChecked,
            VerificationLevel::FullyVerified,
        ] {
            let mut solver = Solver::new(Logic::QfUf);
            solver.set_verification_level(level);
            let proposition = solver.declare_const("p", Sort::Bool);
            let not_proposition = solver.not(proposition);
            solver.assert_term(proposition);
            solver.assert_term(not_proposition);

            assert!(!solver.is_producing_proofs());
            let details = solver.check_sat_with_details();
            assert!(details.result.is_unsat());
            assert!(details.verification.unsat_proof_strictly_verified);
            assert!(!details.verification.unsat_proof_available);
            assert!(solver.last_proof().is_none());
        }
    }

    #[test]
    fn enabling_wire_proofs_after_unsat_does_not_expose_get_proof() {
        let commands = ay_frontend::parse(
            "(set-logic QF_UF) (declare-const p Bool) (assert p) \
             (assert (not p)) (check-sat) \
             (set-option :produce-proofs true) (get-proof)",
        )
        .expect("post-hoc proof script must parse");
        let mut executor = Executor::new();
        let outputs = executor
            .execute_all(&commands)
            .expect("post-hoc proof script must execute");

        assert_eq!(outputs, ["unsat", "(error \"proof was not generated\")"]);
        assert!(executor.last_proof.is_some(), "anti-vacuity");
    }

    #[test]
    fn disabling_wire_proofs_after_unsat_only_closes_wire_surface() {
        let commands = ay_frontend::parse(
            "(set-logic QF_UF) (set-option :produce-proofs true) \
             (declare-const p Bool) (assert p) (assert (not p)) (check-sat) \
             (set-option :produce-proofs false) (get-proof)",
        )
        .expect("solve-time proof script must parse");
        let mut executor = Executor::new();
        let outputs = executor
            .execute_all(&commands)
            .expect("solve-time proof script must execute");

        assert_eq!(
            outputs,
            [
                "unsat",
                "(error \"proof generation is not enabled, set :produce-proofs to true\")",
            ]
        );
        assert!(executor.last_proof().is_some());
        assert!(executor
            .try_export_last_proof_alethe_for_problem_scope()
            .is_some());
    }
}
