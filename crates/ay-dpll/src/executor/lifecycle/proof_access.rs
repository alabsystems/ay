// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Executor;
use ay_core::Proof;

impl Executor {
    /// The memo of the exact-division sweeps the last proof build saw fail
    /// (`ay_proof::ExactDivisionSweepMemo`), for diagnostics and tests.
    #[must_use]
    pub fn exact_division_sweep_memo(&self) -> &ay_proof::ExactDivisionSweepMemo {
        &self.exact_division_sweeps
    }

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

    /// Whether the SCRIPT asked for strict proofs with
    /// `(set-option :check-proofs-strict true)` (the current value of that
    /// option on this executor's context).
    ///
    /// A host that publishes verdicts and certificates (the `ay` binary)
    /// reads this beside its own strict-proofs flag, so that the in-script and
    /// the command-line spellings of strict proofs are one admission decision
    /// on the published document. The executor's own funnel judges the
    /// in-memory derivation only; it cannot see a step the Alethe printer
    /// downgrades to `hole`.
    #[must_use]
    pub fn script_strict_proofs_requested(&self) -> bool {
        self.strict_proofs_enabled()
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

    /// What the proof held when the last-resort empty-clause closer last ran.
    ///
    /// #closer-population. Diagnostic only, on the same terms as
    /// [`Self::last_proof_decline`]. `None` means that closer did not run at
    /// all on this query — a derivation strategy above it closed the proof, or
    /// nothing reached the closer.
    ///
    /// The one question it answers is the one an artifact cannot: whether the
    /// closer restated the solve's verdict over a proof that ALREADY HELD a
    /// derivation, or over one that held nothing but the authored assumptions.
    /// By the time a document exists the closer's own chain is all that is
    /// left, so the two are indistinguishable downstream.
    #[must_use]
    pub fn last_trust_closure_census(&self) -> Option<crate::executor::TrustClosureCensus> {
        self.last_trust_closure_census
    }

    /// What the exact semantic-certificate mint held when it last published.
    ///
    /// #semantic-token census. Diagnostic only, on the same terms as
    /// [`Self::last_proof_decline`]. `None` means no exact semantic
    /// certificate was minted on this query.
    ///
    /// The question it answers is the one the decline tag
    /// `checked-semantic-certificate-unrendered` invites and cannot settle:
    /// whether the object it names is a derivation over the authored
    /// assertion, or a leaf token over a residue term construction produced
    /// from it.
    #[must_use]
    pub fn last_semantic_token_census(&self) -> Option<&crate::executor::SemanticTokenCensus> {
        self.last_semantic_token_census.as_ref()
    }

    /// What was on the other side of the bound when an "unbounded" decline
    /// fired on this query.
    ///
    /// #unbounded-population. Diagnostic only, on the same terms as
    /// [`Self::last_proof_decline`]. `None` when neither
    /// `authored-source-root-unbounded` nor
    /// `authored-surface-override-plan-unbounded` was recorded.
    #[must_use]
    pub fn last_unbounded_census(&self) -> Option<crate::executor::UnboundedCensus> {
        self.last_unbounded_census
    }

    /// The recorded decline, screened against the derivation actually retained.
    ///
    /// #evidence-stage-3. A decline is recorded where it happens — inside the
    /// closer, inside a poison, inside a publication lane — and a later repair
    /// pass may replace the very step it names (`rebuild_finite_enum_pigeonhole_
    /// refutation` replaces the whole proof; the promoters retype heads). A
    /// stale record would then attach a "no derivation" label to a document
    /// that has one, which is the same species of false statement this stage
    /// exists to remove.
    ///
    /// So: report the record only when the retained proof still carries the gap
    /// it describes. A proof that became trust-free superseded its own decline.
    /// When no proof is retained at all there is nothing to supersede it, and
    /// the record stands.
    ///
    /// "The gap it describes" has two shapes, and the screen asks for the one
    /// the record names. A closure or document record names a STEP, and a
    /// trust-free derivation has superseded it. An authored-surface record
    /// (`ProofDeclineMechanism::describes_authored_assume_surface`) names a
    /// LEAF — an `assume` for which no authored spelling was produced — and a
    /// trust-free derivation whose terminal `assume` is still not an
    /// assertion of the problem carries that gap intact. Measured on
    /// AUFDTLIRA `P630-039 bug.ads_32_25_range_check`
    /// (#probe-ite-lift-promoter): the override plan recorded
    /// `authored-surface-override-plan-unbounded`, the cascade later
    /// committed a trust-free, hole-free derivation whose single `assume` is
    /// the canonical root, and the step-only screen dropped the record — so
    /// the CLI's fallback labelled a document with no trust step
    /// `terminal-trust-step-on-path`, and the unbounded census that keys on
    /// the real mechanism went unprinted with it.
    ///
    /// Deliberately NOT conflated with the disclosure's `ay_self_checkable`,
    /// which is a statement about the FILE. This is a statement about the
    /// in-memory derivation, and the two are allowed to disagree — that
    /// disagreement is precisely the printer-downgrade class.
    #[must_use]
    pub fn live_proof_decline(&self) -> Option<crate::executor::ProofDeclineMechanism> {
        let mechanism = self.last_proof_decline?;
        let Some(proof) = self.last_proof() else {
            return Some(mechanism);
        };
        if !ay_proof::terminal_trust_report(proof).is_trust_free() {
            return Some(mechanism);
        }
        (mechanism.describes_authored_assume_surface()
            && self.unsat_proof_terminal_foreign_assume())
        .then_some(mechanism)
    }

    /// Which re-decision by AY's own code corroborated the last published
    /// `unsat`, when one did (evidence E1; see `last_command_unsat_evidence`).
    ///
    /// Diagnostic only. This is reproducibility evidence and never
    /// checkability evidence; see `executor::proof::corroboration`.
    #[must_use]
    pub fn last_unsat_corroboration(&self) -> Option<crate::executor::UnsatCorroboration> {
        self.last_unsat_corroboration.get()
    }

    /// The typed stop a metered strict walk observed, if one did since the
    /// last certification began (see the field's note).
    pub(crate) fn certification_stop(&self) -> Option<crate::api::proofs::EnvelopeStop> {
        self.certification_stop.get()
    }

    /// Keep the first stop a metered strict walk observed.
    pub(in crate::executor) fn note_certification_stop(
        &self,
        stop: crate::api::proofs::EnvelopeStop,
    ) {
        if self.certification_stop.get().is_none() {
            self.certification_stop.set(Some(stop));
        }
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

    /// A trust-free refutation of `p ∧ ¬p` from two `assume` leaves, retained
    /// as the last public proof. With `authored` the two leaves are on the
    /// assertion stack the public solve was bound to; without it nothing was
    /// asserted and both leaves are foreign — the measured P630 shape (a
    /// trust-free, hole-free derivation whose `assume` is not the problem's
    /// text).
    fn trust_free_two_leaf_refutation(authored: bool) -> Executor {
        let mut executor = Executor::new();
        let p = executor.ctx.terms.mk_var("p", Sort::Bool);
        let not_p = executor.ctx.terms.mk_not(p);
        if authored {
            executor.ctx.assertions.push(p);
            executor.ctx.assertions.push(not_p);
        }
        executor.set_produce_proofs(true);
        executor.begin_public_solve(false);
        let mut proof = Proof::new();
        let assume_p = proof.add_assume(p, None);
        let assume_not_p = proof.add_assume(not_p, None);
        proof.add_resolution(Vec::new(), p, assume_p, assume_not_p);
        executor.last_result = Some(SolveResult::unsat());
        executor.last_proof = Some(proof);
        assert!(executor.last_proof().is_some(), "anti-vacuity");
        assert!(ay_proof::terminal_trust_report(executor.last_proof().unwrap()).is_trust_free());
        assert_eq!(executor.unsat_proof_terminal_foreign_assume(), !authored);
        executor
    }

    /// #probe-ite-lift-promoter, disclosure. A trust-free derivation whose
    /// terminal `assume` is not an assertion of the problem still carries the
    /// gap an authored-surface record names, so that record is live; a record
    /// about a closure step is superseded by the same proof; and once the
    /// leaves are authored, the surface record is superseded too.
    #[test]
    fn authored_surface_record_stands_over_a_trust_free_proof_with_a_foreign_assume() {
        use crate::executor::ProofDeclineMechanism as M;

        let mut foreign = trust_free_two_leaf_refutation(false);
        foreign.record_proof_decline(M::AuthoredSurfaceOverridePlanUnbounded);
        assert_eq!(
            foreign.live_proof_decline(),
            Some(M::AuthoredSurfaceOverridePlanUnbounded),
            "the surface record names the foreign assume the proof still carries"
        );
        foreign.record_proof_decline(M::AuthoredAssumeSurfaceUnavailable);
        assert_eq!(
            foreign.live_proof_decline(),
            Some(M::AuthoredAssumeSurfaceUnavailable)
        );
        // A record about a STEP is superseded by a trust-free derivation,
        // whatever its leaves.
        foreign.record_proof_decline(M::AssumeFamilyTrustClosure);
        assert_eq!(foreign.live_proof_decline(), None);
        foreign.record_proof_decline(M::PreprocessorFoldToFalseUnrecorded);
        assert_eq!(foreign.live_proof_decline(), None);
        // With no retained proof at all, nothing supersedes any record.
        foreign.record_proof_decline(M::AssumeFamilyTrustClosure);
        foreign.last_proof = None;
        assert_eq!(
            foreign.live_proof_decline(),
            Some(M::AssumeFamilyTrustClosure)
        );

        // Leaves that ARE the problem's assertions leave no surface gap, so
        // the surface record is superseded as well.
        let mut authored = trust_free_two_leaf_refutation(true);
        authored.record_proof_decline(M::AuthoredSurfaceOverridePlanUnbounded);
        assert_eq!(authored.live_proof_decline(), None);
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
