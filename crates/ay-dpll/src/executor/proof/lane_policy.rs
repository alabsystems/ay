// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-sensitive solver-lane admission policy.

use ay_core::TermId;

use super::super::Executor;

impl Executor {
    /// Immutable, concrete source roots that may authorize a replacement
    /// proof: the frozen assertion epoch plus the exact caller-supplied
    /// `check-sat-assuming` literals. There is deliberately no fallback to
    /// `ctx.assertions`, whose live stack may contain solver-generated axioms
    /// or folded artifacts.
    pub(in crate::executor) fn exact_concrete_authored_scope(&self) -> Vec<TermId> {
        let source = self
            .proof_problem_assertion_provenance
            .as_ref()
            .map_or_else(
                || self.ctx.concrete_authored_assertion_terms(),
                |provenance| provenance.original_problem_assertions.clone(),
            );
        // Membership through a set, not `Vec::contains` (#strict-proof-dedup,
        // second instance). This dedup is O(n^2) over the authored assertion
        // count, and the authored-replacement cascade in `build_unsat_proof`
        // rebuilds this scope in EVERY member — up to ~24 times per certified
        // UNSAT publication. On QF_DT vlsat3_b83 (156,679 authored asserts)
        // that is the dominant certification cost after the pigeonhole fix.
        // Order is preserved exactly; the set only answers "already present" —
        // the same shape as the fix measured at 26% on
        // `problem_assertions_for_strict_proof` (proof/check.rs).
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut exact = Vec::with_capacity(source.len());
        for term in source {
            if seen.insert(term) {
                exact.push(term);
            }
        }
        if let Some(assumptions) = &self.last_assumptions {
            for &term in assumptions {
                if seen.insert(term) {
                    exact.push(term);
                }
            }
        }
        exact
    }

    /// Whether an UNVETTED no-proof refutation lane may run (#proof-capability
    /// B2, dormant-lane audit).
    ///
    /// Two UNSAT-originating shortcuts gate on this predicate:
    /// `try_word_eq_constant_propagation` (strings), and
    /// `try_lia_eager_assume_unsat_probe` (LIA). Both were written
    /// against the OLD meaning of `!produce_proofs_enabled()` ("the user
    /// opted out of proofs") and are DEAD on today's certified public path,
    /// where `begin_public_solve` always arms the tracker. Competition
    /// shedding (`competition_shedding_active`) turns the tracker off, which
    /// would have flipped both gates LIVE for the first time under
    /// public publication — switching ON refutation shortcuts that have
    /// never been publicly exercised is not cost shedding. The v1 decision
    /// keeps both exactly as dead as today in every configuration:
    ///
    /// - false whenever `produce_proofs_enabled()` — unchanged: these lanes
    ///   have no proof reconstruction and must not originate an uncertified
    ///   `Unsat` into a proof-carrying solve;
    /// - false whenever `competition_shedding_active()` — new: shedding must
    ///   not activate unvetted refutation lanes.
    ///
    /// In every non-competition configuration `competition_shedding_active()`
    /// is false, so this predicate is exactly `!produce_proofs_enabled()` —
    /// byte-identical behavior to the gates it replaced. A lane may move off
    /// this predicate only after it is individually vetted for raw
    /// publication; it then earns its own named gate.
    pub(in crate::executor) fn unvetted_no_proof_lane_allowed(&self) -> bool {
        !self.produce_proofs_enabled() && !self.competition_shedding_active()
    }

    /// Whether a CHECKED certificate is demanded for this solve, so theory
    /// engine routing must stay on the proof-capable arms.
    ///
    /// This is the predicate the routing sites consult (`solve_lra`'s
    /// incremental-engine / eager arms, `solve_lia`'s eager split loop, and
    /// the CEGAR pending-lemma loop in `cegar_refine_solve`). It is the same
    /// demand set that decides whether a missing proof changes the verdict
    /// ([`Self::strict_unsat_presentation_required`]): an explicit artifact
    /// request (`--proof`, `set_produce_proofs(true)`), `--self-check`,
    /// `--strict-proofs` / `:check-proofs-strict`, API proof checking, or an
    /// in-script `(set-option :produce-proofs true)`.
    ///
    /// It is deliberately NOT [`Self::is_producing_proofs`]. That accessor is
    /// also true for the synthesized best-effort artifact
    /// (`set_best_effort_produce_proofs`), whose contract is "write a
    /// certificate if one falls out of the search, never change the verdict".
    /// Routing on it demoted every best-effort session to the lazy arms:
    /// measured on QF_AUFLIA storecomm_t1_pp_sf_ai_00060_001, the demoted
    /// route runs 268 LRA-check rounds and times out at 22 s where the eager
    /// route refutes in 0.09 s — a verdict lost to an OPTIONAL sidecar. With
    /// this predicate the routing is identical between a shedding solve and
    /// any solve where no proof artifact is required; the sidecar is still
    /// rendered best-effort from whatever the tracker recorded.
    pub(in crate::executor) fn checked_certificate_demanded(&self) -> bool {
        self.strict_unsat_presentation_required()
    }
}
