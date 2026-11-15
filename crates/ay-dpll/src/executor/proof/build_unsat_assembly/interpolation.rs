// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The refutation an interpolation proof session keeps for the Craig
//! interpolation extractor ([`Executor::set_interpolation_proofs`]).
//!
//! Measured on the Workstream D IMC query corpus (LRA-Lin, `k <= 2`), the
//! artifact pipeline left the extractor a usable refutation on 9 of 42
//! decided queries. Most of the rest lost it to presentation passes that
//! serve an external checker: `apply_input_syntax_rewrites_to_proof` replaced
//! the whole refutation by one premiseless `trust` step when the
//! surface-override plan exceeded its bounds on the `let`-shaped transition
//! relations (`authored-surface-override-plan-unbounded`), the authored-surface
//! restoration suppressed it (`authored-source-authority-invalid`), or the
//! demotion pass turned the `assume` of a preprocessed assertion — the QF_LRA
//! lane Shannon-lifts arithmetic `ite`s and splits equalities — into a `trust`
//! step because it is not an authored root.
//!
//! None of that is evidence the extractor can use. It reads the solver's own
//! refutation, colours preprocessed leaves through the sources the lane
//! recorded (`InterpolationRecords::leaf_sources`), and every interpolant it serves is
//! validated by its consumer. So right after the empty clause is derived and
//! the arithmetic lemmas' Farkas certificates are reconstructed (an
//! uncertified lemma is demoted and the extractor refuses it), this pass keeps
//! a pruned copy. The artifact pipeline then continues on the original
//! unchanged: its own first step re-runs the same idempotent reconstruction,
//! so certification and every verdict are exactly those of best-effort
//! production.

use super::*;

impl Executor {
    pub(super) fn capture_interpolation_proof(&mut self, proof: &mut Proof) {
        if !self.interpolation.enabled {
            return;
        }
        let hidden_equality_assertions = self.collect_hidden_problem_equality_assertions();
        self.reconstruct_missing_farkas_and_demote(proof, &hidden_equality_assertions);
        if !Self::proof_derives_empty_clause(proof) {
            return;
        }
        let mut snapshot = proof.clone();
        crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut snapshot);
        self.interpolation.last_proof = Some(snapshot);
    }

    /// The capture for a refutation the artifact pipeline refuses before
    /// assembling anything (`proof_source_decline`: an authored root exceeds
    /// the surface-rendering bounds — `cav12/array_max-5`'s IMC queries).
    /// Those bounds are about rendering the authored surface, which this
    /// refutation never does, so it is seeded and derived exactly as
    /// `build_unsat_proof` would have. The caller installs the artifact's
    /// poison right after; nothing else reads the SAT records consumed here.
    pub(super) fn capture_interpolation_proof_without_assembly(&mut self) {
        if !self.interpolation.enabled || self.proof_assembly_stop_requested() {
            return;
        }
        let mut proof = if self.proof_tracker.num_steps() > 0 {
            self.seed_proof_from_tracker()
        } else {
            self.seed_proof_from_assertions()
        };
        self.derive_empty_clause(&mut proof);
        if self.proof_assembly_stop_requested() {
            return;
        }
        self.capture_interpolation_proof(&mut proof);
    }
}
