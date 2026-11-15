// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Faithful reconstruction of bit-vector identities folded during elaboration.

use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TheoryLemmaKind};

use super::bvand_commutative_congruence::add_crosswise_congruence_proof;
use super::{
    add_bvand_commutative_congruence_proof, build_bv_pterm, build_qfbv_pterm, match_eq_negation,
    Executor,
};

mod frontier;
mod guarded;
mod limb;

/// Where one UNSAT publication flow runs the guarded-collapse planner.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum GuardedCollapseStage {
    /// At the head of `run_authored_replacement_cascade`. The incumbent may
    /// still carry trust leaves that later cascade members and derivation
    /// passes lower, so a strict rejection here is not final.
    Cascade,
    /// Immediately before `finalize_unsat_proof` publishes the proof.
    Final,
    /// Immediately before the strict checker is asked to promote the proof's
    /// Generic bit-vector lemmas, where the cascade will run the collapse
    /// over the same roots whatever the promotion decides
    /// (`guarded/before_promotion.rs`).
    BeforePromotion,
    /// Where the residual-trust rescue or the Generic BV promotion would pay
    /// for an exact divider to decide an authored `bvurem` obligation; the
    /// BvUremBound joint is asked deciding with none
    /// (`guarded/urem_bound/before_division.rs`).
    BeforeExactDivision,
}

impl GuardedCollapseStage {
    /// Whether the stage runs ahead of the proof producer that settles the
    /// incumbent's facts, so a candidate must print clean on its own
    /// (`guarded_repair_worth_checking`).
    fn precedes_the_producer(self) -> bool {
        matches!(self, Self::BeforePromotion | Self::BeforeExactDivision)
    }
}

impl Executor {
    pub(super) fn finalize_bv_source_proof(&mut self, mut proof: Proof) {
        // A final-boundary install runs after `build_unsat_assembly`'s authored
        // surface restoration and purges the spellings of what it prints. Its
        // roots are raw re-interns of macro-EXPANDED authored assertions, so
        // `(assert (= v0 one))` shipped `(assume t0 (= v0 #b1))`, which no
        // problem premise matches. Re-spell exactly those roots; the purge of
        // everything else is the lane's own, deliberate presentation.
        if !self.skips_trust_elimination_repairs()
            && self.promote_bv_guarded_collapse(&mut proof, GuardedCollapseStage::Final)
        {
            self.respell_nullary_macro_roots_of(&proof);
        }
        self.finalize_unsat_proof(proof);
    }

    pub(super) fn promote_bv_identity_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        let parsed = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((lhs, rhs)) = match_eq_negation(asrt) else {
                continue;
            };
            // Rebuild the folded sides faithfully. The Boolean layer handles
            // BV-valued `ite` nodes nested below concat/extract operations.
            let (Some(l_id), Some(r_id)) = (
                build_bv_pterm(&mut self.ctx.terms, lhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, lhs)),
                build_bv_pterm(&mut self.ctx.terms, rhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, rhs)),
            ) else {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE rebuild (bv+qfbv both failed on a side)"
                        .to_string()
                });
                continue;
            };
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "bv-identity-collapse: rebuilt both sides OK".to_string()
            });
            // Both sides must share a Boolean/BV sort for `=` to be
            // well-formed. Boolean is load-bearing for direct BV predicate
            // identities such as `(bvult x 1) = (x = 0)`; the recursive
            // congruence builder and the final independent bit-blast replay
            // still authenticate the complete equality before it is used.
            if self.ctx.terms.sort(l_id) != self.ctx.terms.sort(r_id)
                || !matches!(self.ctx.terms.sort(l_id), Sort::Bool | Sort::BitVec(_))
            {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE sort gate".to_string()
                });
                continue;
            }
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [l_id, r_id], Sort::Bool);
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);
            // Export must preserve both rebuilt terms through surface overrides.
            if !self.rebuilt_terms_print_faithfully(&[neg_t, eq_t]) {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE print-faithfulness".to_string()
                });
                continue;
            }

            let mut candidate = Proof::new();
            let assume_id = candidate.add_assume(neg_t, None);
            let Some(lemma_id) = self.bv_identity_lemma(&mut candidate, eq_t, l_id, r_id) else {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE no lemma route (walker None + recognizer refused)"
                        .to_string()
                });
                continue;
            };
            candidate.add_resolution(vec![], eq_t, assume_id, lemma_id);

            // This is the whole parsed top-level assertion, faithfully rebuilt
            // above. Preserve that narrower provenance as well as assumption
            // authority so authored-surface restoration can identify the root
            // even when elaboration folded its original TermId to false.
            self.record_raw_authored_problem_assertion(neg_t);
            self.purge_surface_overrides_for_certified_proof(&candidate);
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "bv-identity-collapse: SUCCESS candidate installed".to_string()
            });
            *proof = candidate;
            return;
        }
    }

    /// The first lemma route that proves the rebuilt equality `eq_t`
    /// (`l_id = r_id`) inside `candidate`, tried in a fixed order; `None` when
    /// every route declines.
    fn bv_identity_lemma(
        &mut self,
        candidate: &mut Proof,
        eq_t: TermId,
        l_id: TermId,
        r_id: TermId,
    ) -> Option<ProofId> {
        if l_id == r_id {
            return Some(candidate.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_t],
                Vec::new(),
                Vec::new(),
            ));
        }
        if ay_proof::recognize_mul_overflow_division(&self.ctx.terms, &[eq_t]) {
            return Some(candidate.add_theory_lemma_with_kind(
                "bv",
                vec![eq_t],
                TheoryLemmaKind::BvMulOverflowDivision,
            ));
        }
        if let Some(step) =
            add_bvand_commutative_congruence_proof(&mut self.ctx.terms, candidate, l_id, r_id)
        {
            return Some(step);
        }
        if ay_proof::recognize_arith_clause_tautology(&self.ctx.terms, &[eq_t]) {
            return Some(candidate.add_theory_lemma_with_kind(
                "bv",
                vec![eq_t],
                TheoryLemmaKind::ArithClauseTautology,
            ));
        }
        // Only once the positional walk and the ring lane have declined: a
        // pure ring identity keeps the ring lane's single lemma
        // (`bvand_commutative_congruence/crossed.rs`).
        if let Some(step) =
            add_crosswise_congruence_proof(&mut self.ctx.terms, candidate, l_id, r_id)
        {
            return Some(step);
        }
        if let Some(step) = self.bv_frontier_identity(candidate, l_id, r_id) {
            return Some(step);
        }
        if let Some(step) = self.bv_limb_identity(candidate, l_id, r_id) {
            return Some(step);
        }
        self.recognize_bv_bitblast_until_stopped(&[eq_t]).then(|| {
            candidate.add_theory_lemma_with_kind("bv", vec![eq_t], TheoryLemmaKind::BvBitBlast)
        })
    }
}
