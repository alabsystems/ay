// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed proof-source and arithmetic-certificate lifecycle boundaries.

use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};

use super::super::Executor;

const MAX_PROOF_SOURCE_ROOTS: usize = 100_000;

impl Executor {
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
    pub(super) fn proof_sources_are_oversized(&self) -> bool {
        let provenance_is_bounded =
            self.proof_problem_assertion_provenance
                .as_ref()
                .is_none_or(|provenance| {
                    provenance.problem_assertions.len() <= MAX_PROOF_SOURCE_ROOTS
                        && provenance.original_problem_assertions.len() <= MAX_PROOF_SOURCE_ROOTS
                        && provenance.assertion_sources.len() <= MAX_PROOF_SOURCE_ROOTS
                });
        !(provenance_is_bounded
            && self.ctx.assertions.len() <= MAX_PROOF_SOURCE_ROOTS
            && self.ctx.assertions_parsed().len() <= MAX_PROOF_SOURCE_ROOTS
            && crate::executor::proof_repair::proof_trust_surgery_surface_audit::surface_sources_have_bounded_work(
                self.ctx
                    .assertions_parsed()
                    .iter()
                    // Proof assembly/rebuild has several mutually exclusive
                    // snapshots, plus a handful of shared source collections.
                    // Charge the worst reachable clone/format count up front so
                    // each later recursive clone remains inside one aggregate
                    // source-work envelope.
                    .flat_map(|parsed| [parsed; 16]),
            ))
    }

    /// Install the canonical fail-closed terminal trust proof and revoke any
    /// narrow proof authority that could otherwise survive beside it.
    pub(super) fn install_uncertifiable_proof_poison(&mut self) {
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
