// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed proof-source and arithmetic-certificate lifecycle boundaries.

use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};

use super::super::Executor;
use super::decline::ProofDeclineMechanism;

const MAX_PROOF_SOURCE_ROOTS: usize = 100_000;

impl Executor {
    /// Get the last serialized LRAT certificate, if proof export captured one.
    pub(crate) fn last_lrat_certificate(&self) -> Option<&[u8]> {
        if self.last_unsat_proof_reconstruction_suppressed {
            None
        } else {
            self.last_lrat_certificate.as_deref()
        }
    }

    /// Revoke both the detector candidate and the query-sealed authority.
    ///
    /// These values are meaningful only beside the exact current UNSAT proof;
    /// keeping either across a proof/result boundary risks retaining a large
    /// stale clique or accidentally reviving authority after a later solve.
    pub(in crate::executor) fn clear_finite_enum_proof_state(&mut self) {
        self.last_finite_enum_pigeonhole = None;
        self.last_checked_finite_enum_pigeonhole = None;
    }

    /// Suppress translated proof publication and revoke every finite-enum
    /// proof candidate/capability in the same state transition.
    pub(in crate::executor) fn suppress_unsat_proof_reconstruction(&mut self) {
        self.last_unsat_proof_reconstruction_suppressed = true;
        self.clear_finite_enum_proof_state();
    }

    /// Whether generic proof reconstruction would reject the authored surface
    /// before cloning or recursively traversing it.
    #[cfg(test)]
    pub(super) fn proof_sources_are_oversized(&self) -> bool {
        self.proof_source_decline().is_some()
    }

    /// WHY generic proof reconstruction rejects the authored surface, if it
    /// does.
    ///
    /// This used to be a bare `bool`, and the caller turned it into the
    /// one-line `(step t0 (cl) :rule hole)` poison. Three unrelated
    /// conditions reach that artifact and a corpus census could not tell them
    /// apart — see [`super::decline`] for the measured split. Nothing about
    /// the decision moves here: the same three tests run in the same order and
    /// a decline is still a decline. Only the answer carries its reason.
    pub(super) fn proof_source_decline(&self) -> Option<ProofDeclineMechanism> {
        let provenance_is_bounded =
            self.proof_problem_assertion_provenance
                .as_ref()
                .is_none_or(|provenance| {
                    provenance.problem_assertions.len() <= MAX_PROOF_SOURCE_ROOTS
                        && provenance.original_problem_assertions.len() <= MAX_PROOF_SOURCE_ROOTS
                        && provenance.assertion_sources.len() <= MAX_PROOF_SOURCE_ROOTS
                });
        if !(provenance_is_bounded
            && self.ctx.assertions.len() <= MAX_PROOF_SOURCE_ROOTS
            && self.ctx.assertions_parsed().len() <= MAX_PROOF_SOURCE_ROOTS)
        {
            return Some(ProofDeclineMechanism::AuthoredSourceRootCount);
        }
        // This preflight performs exactly ONE traversal of the parsed
        // stack, so it charges one. It used to charge sixteen — the worst
        // reachable clone/format count of every LATER pass, billed here
        // whether or not any of them ran. Those passes now charge
        // themselves against the same shared envelope, which keeps the
        // aggregate ceiling identical while ending the pre-charge: a
        // 25-assertion / 48 KB QF_UF instance whose whole source stack
        // costs 2.9 MiB was refused a proof outright because 16x2.9 MiB
        // exceeded a 32 MiB budget nothing was going to spend.
        if self.proof_source_work.spend(
            crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourcePass::UnsatProofBuild,
            self.ctx.assertions_parsed(),
        ) {
            return None;
        }
        // The spend refused. Separate the two ways it can: a root nothing can
        // render at any budget, versus roots that are all individually
        // renderable and simply do not fit in what is left of the envelope.
        // The remedies are opposite — the first needs a per-root bound that
        // reflects real rendering work, the second needs a bigger or
        // better-spent envelope — and only this distinction tells a census
        // which one a given instance wants.
        if self
            .ctx
            .assertions_parsed()
            .iter()
            .any(|root| !crate::executor::proof_repair::proof_trust_surgery_surface_audit::surface_source_is_bounded(root))
        {
            Some(ProofDeclineMechanism::AuthoredSourceRootUnbounded)
        } else {
            Some(ProofDeclineMechanism::AuthoredSourceAggregateBudget)
        }
    }

    /// Install the canonical fail-closed terminal trust proof and revoke any
    /// narrow proof authority that could otherwise survive beside it.
    ///
    /// `mechanism` is recorded for disclosure only; it changes nothing about
    /// the artifact, which stays exactly as fail-closed as before.
    pub(super) fn install_uncertifiable_proof_poison(&mut self, mechanism: ProofDeclineMechanism) {
        // A terminal trust leaf keeps the UNSAT result behind the normal
        // mandatory certificate gate, which will honestly publish `unknown`
        // rather than an externally mismatched proof.
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        self.clear_finite_enum_proof_state();
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.proof_check_result = None;
        self.last_proof = Some(proof);
        self.record_proof_decline(mechanism);
    }

    /// Record WHY this query's refutation carries no derivation.
    pub(in crate::executor) fn record_proof_decline(&mut self, mechanism: ProofDeclineMechanism) {
        self.last_proof_decline = Some(mechanism);
    }

    /// Reconstruct arithmetic certificates and immediately demote any step
    /// that still lacks the annotation required by its declared kind.
    pub(super) fn reconstruct_missing_farkas_and_demote(
        &mut self,
        proof: &mut Proof,
        hidden_equality_assertions: &[TermId],
    ) {
        crate::executor::proof_repair::proof_farkas::reconstruct_missing_farkas_coefficients(
            &mut self.ctx.terms,
            proof,
            &self.ctx.assertions,
            hidden_equality_assertions,
        );
        Self::demote_uncertified_arithmetic_lemmas_to_trust(proof);
    }

    /// Revalidate every positional certificate after syntax rewriting and
    /// immediately demote annotations that no longer certify their clause.
    pub(super) fn sanitize_rewritten_farkas_and_demote(&self, proof: &mut Proof) {
        crate::executor::proof_repair::proof_farkas_validation::sanitize_farkas_annotations(
            &self.ctx.terms,
            proof,
        );
        Self::demote_uncertified_arithmetic_lemmas_to_trust(proof);
    }

    /// Keep certificate-requiring arithmetic lemmas honest after best-effort
    /// Farkas reconstruction. A `LraFarkas`/plain `LiaGeneric` step without
    /// coefficients would export as if a certificate existed, so leave it as
    /// Generic/trusted and let proof-quality/terminal-trust detection report it.
    pub(super) fn demote_uncertified_arithmetic_lemmas_to_trust(proof: &mut Proof) {
        for step in &mut proof.steps {
            let ProofStep::TheoryLemma {
                kind, farkas, lia, ..
            } = step
            else {
                continue;
            };
            if farkas.is_some() || lia.is_some() {
                continue;
            }
            if matches!(
                kind,
                TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric
            ) {
                *kind = TheoryLemmaKind::Generic;
            }
        }
    }
}
