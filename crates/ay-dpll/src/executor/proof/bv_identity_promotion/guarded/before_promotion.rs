// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The guarded collapse, asked before the strict checker is asked to promote
//! the proof's Generic bit-vector lemmas.
//!
//! `promote_semantically_checked_bv_lemmas` hands each Generic lemma to the
//! strict checker's proof producer, and the authored cascade, whose head is
//! the guarded collapse, runs only after it. For a multi-literal lemma that
//! order can be all cost: the known-wire-gap screen reports such a lemma as a
//! gap even once it is promoted (unless a named lowering prints it), so the
//! cascade still runs the collapse over the authored roots whatever the
//! producer decided. Measured 2026-10-08 on `bv_circuit_source`'s coroutine
//! row (a 60 s query): the proof's one Generic lemma is a 20-literal
//! array-eliminated clause (13,525 variables, 61,077 clauses); the producer
//! spent 48 s refusing it, 8.3 s monolithically and the rest in a sweep that
//! never closed, and the collapse then certified the authored root through the
//! checker's array lane in 0.4 s, after the search had already spent 31 s.
//! Asked first, the collapse publishes the same document and the row answers
//! in 30-43 s, depending on host load (73-80 s with a longer timeout before;
//! `unknown` at its own 60 s). So do the row with a pure bit-vector side
//! assertion ahead of it, and with its four conjuncts asserted separately,
//! which the stage meets after roots it must pass over (28-36 s; `unknown`
//! before).
//!
//! The collapse is therefore asked first, at
//! [`GuardedCollapseStage::BeforePromotion`], exactly where the cascade is
//! certain to ask it the same question about the same roots
//! ([`Executor::guarded_collapse_follows_any_promotion`]): the promotion
//! cannot make the proof publishable, nothing between the promotion and the
//! cascade's head can replace the proof (an authored `false`, the pure
//! bit-vector ground closure), and some authored root reads an array.
//! The stage walks the roots in the cascade's own order and takes each
//! decision the cascade would take whatever the promotion decided:
//!
//! * a root without an array read, an arithmetic or a shadowed-store root is
//!   decided by its own candidate alone, as in the cascade;
//! * an array-read candidate that prints clean on its own
//!   (`wire_repair_candidate_prints_clean`) is checked and, accepted,
//!   installed;
//! * one that does not is skipped, as the cascade skips it, unless a
//!   document is observable; then the cascade weighs it against the promoted
//!   incumbent's facts (`guarded_repair_worth_checking`), which only the
//!   promotion settles. Rejected by the strict checker, it is skipped, as the
//!   cascade skips it either way; accepted, it ends the stage, and that root
//!   and every later one meet the cascade in its own order
//!   ([`Executor::guarded_decision_awaits_promotion`]).
//!
//! The one decision that can differ is the clean array-read candidate's: the
//! cascade keeps an observable incumbent whose promoted lemmas render clean,
//! where the stage installs a clean, strictly checked authored-root
//! refutation instead. After an install the cascade's head also meets that
//! refutation as a publishable incumbent, and may already try the cheaper
//! named re-derivation (`rederive.rs`) the final boundary tries in either
//! order. Measured over `group_proofs`, `group_bv`, `group_arrays`,
//! `group_api` and the `bv_*` binaries: of their 3,408 assembled proofs and
//! 556 published documents only the coroutine row's changed, and the stage
//! installed on one other query, the very proof the cascade installed there
//! before. Every installed candidate passes the unchanged strict check, and
//! a proof the stage does not replace goes through the promotion exactly as
//! before.

use super::{bounded_source, source, Executor, GuardedCollapseStage, MAX_GUARDED_ROOTS};
use ay_core::{Proof, ProofStep, TheoryLemmaKind};

impl Executor {
    /// The guarded collapse at [`GuardedCollapseStage::BeforePromotion`], when
    /// [`Self::guarded_collapse_follows_any_promotion`] says the cascade will
    /// ask it about the same roots whatever the promotion decides.
    pub(in crate::executor::proof) fn promote_bv_guarded_collapse_before_promotion(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.guarded_collapse_follows_any_promotion(proof) {
            let _replaced =
                self.promote_bv_guarded_collapse(proof, GuardedCollapseStage::BeforePromotion);
        }
    }

    /// Whether the authored cascade will run the guarded collapse over the
    /// authored roots after promoting `proof`'s Generic lemmas, whatever the
    /// promotion decides: some authored root reads an array, the promotion
    /// leaves a known wire gap ([`Self::bv_promotion_leaves_known_wire_gap`]),
    /// and neither the authored-`false` replacement nor the pure bit-vector
    /// ground closure, which run between them, can apply.
    pub(in crate::executor::proof) fn guarded_collapse_follows_any_promotion(
        &mut self,
        proof: &Proof,
    ) -> bool {
        let parsed = self.ctx.assertions_parsed();
        parsed.len() <= MAX_GUARDED_ROOTS
            && parsed.iter().any(|assertion| {
                source::expand(&self.ctx, assertion).and_then(|expanded| bounded_source(&expanded))
                    == Some(true)
            })
            && !self.boolean_constant_premises_authored().1
            && self.bv_promotion_leaves_known_wire_gap(proof)
            && !self.pure_bit_vector_ground_closure_applies()
    }

    /// Whether every Generic lemma of `proof` is a multi-literal clause only
    /// the proof producer decides, and `proof` would keep a known wire gap
    /// with each of them promoted. A proof with any other Generic lemma is
    /// left to the usual order: whether ITS promotion makes the proof
    /// publishable is the promotion's question.
    pub(in crate::executor::proof) fn bv_promotion_leaves_known_wire_gap(
        &self,
        proof: &Proof,
    ) -> bool {
        let mut generic = Vec::new();
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::Generic,
                ..
            } = step
            else {
                continue;
            };
            if clause.len() < 2
                || !ay_proof::bv_bitblast_requires_proof_producer(&self.ctx.terms, clause)
            {
                return false;
            }
            generic.push(index);
        }
        if generic.is_empty() {
            return false;
        }
        let mut promoted = proof.clone();
        for index in generic {
            if let Some(ProofStep::TheoryLemma { theory, kind, .. }) = promoted.steps.get_mut(index)
            {
                *theory = "bv".to_string();
                *kind = TheoryLemmaKind::BvBitBlast;
            }
        }
        self.proof_has_known_wire_gap(&promoted)
    }

    /// Whether `candidate` passes the wire-repair admission rule in the view
    /// its installation leaves (`guarded_candidate_prints_without_gap`
    /// explains the purge); the override map is restored exactly.
    pub(super) fn guarded_candidate_prints_clean(&mut self, candidate: &Proof) -> bool {
        let current = self.last_proof_term_overrides.clone();
        self.purge_surface_overrides_for_certified_proof(candidate);
        let clean = self.wire_repair_candidate_prints_clean(candidate);
        self.last_proof_term_overrides = current;
        clean
    }

    /// Whether the cascade's decision about an array-read `candidate` that
    /// does not print clean turns on the promoted incumbent. With no document
    /// observable it never does: the cascade skips such a candidate. While
    /// one is, the cascade checks it unless the incumbent is complete and
    /// presents clean, so the decision turns on the incumbent exactly when
    /// the strict checker accepts the candidate.
    pub(super) fn guarded_decision_awaits_promotion(&self, candidate: &Proof) -> bool {
        self.proof_document_observable() && self.check_proof_strict_until_stopped(candidate).is_ok()
    }
}

#[cfg(test)]
#[path = "before_promotion_tests.rs"]
mod tests;
