// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Record a preprocessor fold-to-`false` as a CHECKABLE refutation of the
//! authored roots, when the bounded Bool/Int/BV interpreter can re-derive it.
//!
//! ## Why this exists
//!
//! `authored_conjunct_eval` recovers the fold's argument when some conjunct is
//! false by SYNTACTIC evaluation — reflexivity, or a declaration-backed
//! datatype tester/selector. That covers the QF_DT shapes it was written for
//! and nothing else. The shape that reaches VerifierConsumer does not have a self-false
//! conjunct at all; the whole authored assertion is closed and false:
//!
//! ```text
//! (assert (or (< 2 0) (>= 2 32)))                 ; shift-amount range check
//! (assert (not (bvule #x0000…0 #x0000…1)))        ; folded bare claim
//! ```
//!
//! Neither is an `and`-tree with a `(not X)` leaf, so `conjunct_eval_closer`
//! never sees a candidate, the erasure runs, and the document becomes
//! `(step t0 (cl) :rule hole)`. Downstream that costs the VERDICT: an explicit
//! `:produce-proofs` request cannot be satisfied by independent query
//! authority (see `nested_row_auxiliary_hole_fails_closed_when_alethe_artifact_is_required`),
//! so the mandatory certification funnel rejects the presentation by name and
//! `certify_unsat_for_publication` withdraws a correct UNSAT to `unknown`.
//!
//! ## What is recorded
//!
//! `TheoryLemmaKind::BvLiaTautology` is not a producer assertion. Its strict
//! validator (`ay-proof/src/checker/bv_lia_query_tautology.rs`) recovers the
//! roots from the clause's explicit outer negations and RE-DERIVES their joint
//! unsatisfiability with the checker's own bounded interpreter, refusing
//! anything it cannot decide. So this promoter's output is a proof the
//! UNCHANGED strict checker verifies end to end:
//!
//! ```text
//! (assume h_1 A_1) … (assume h_n A_n)
//! (step  l   (cl (not A_1) … (not A_n)) :rule bv_lia_tautology)   ; re-derived
//! (step  …   (cl) :rule th_resolution :premises (l h_1 … h_n))
//! ```
//!
//! versus the `hole` the same skeleton carries in `rescue_bv_bitblast_collapse`.
//! This is `0a64b7e651`'s architecture — make a specific promoter fire so the
//! last-resort rescue never runs — applied to the fold-to-`false` erasure.
//!
//! ## What this is NOT
//!
//! No gate, mode policy, or checker rule was touched. The promoter commits a
//! candidate only when `check_proof_strict_with_datatypes` accepts it WHOLE and
//! it derives the empty clause; every other outcome leaves the erasure exactly
//! as it was, including the `hole`. Its `assume` leaves are the author's own
//! assertions re-interned RAW from the parsed surface and required to print
//! back as authored — never the normalized re-elaboration, which is how the
//! folded constant got in. An unsound query cannot survive: the validator's own
//! interpreter answers `Satisfiable` and the candidate is discarded.

use super::*;

impl Executor {
    /// Replace an about-to-be-erased proof with a `BvLiaTautology`-anchored
    /// refutation of the authored roots. `true` when a strictly-checked
    /// replacement was committed.
    pub(super) fn replace_with_exact_authored_bv_lia_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        // One traversal of the parsed stack, charged against the same
        // query-local envelope every other source-touching pass shares.
        if !self.proof_source_work.spend(
            crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourcePass::AuthoredConjunctEvalRebuild,
            self.ctx.assertions_parsed(),
        ) {
            return false;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        if parsed.is_empty() {
            return false;
        }

        // (1) Re-intern the authored assertions RAW. An assertion that will not
        // rebuild node-by-node is simply not a candidate premise; dropping it
        // only shrinks the question asked below, which is the safe direction.
        let mut roots: Vec<(TermId, &FrontendTerm)> = Vec::new();
        if roots.try_reserve_exact(parsed.len()).is_err() {
            return false;
        }
        for assertion in &parsed {
            let Some(root) = self.raw_intern_surface(assertion) else {
                continue;
            };
            if matches!(self.ctx.terms.sort(root), Sort::Bool) {
                roots.push((root, assertion));
            }
        }
        if roots.is_empty() {
            return false;
        }

        // (2) The checker's OWN bounded interpreter must re-derive the
        // refutation. This is the accepting step, and it is the same routine
        // the strict validator will run again on the committed lemma — so a
        // query it cannot decide, or decides `Satisfiable`, stops here.
        //
        // Try each authored root ALONE before the whole set. A fold-to-`false`
        // fires because ONE assertion is self-refuting, and the rest of the
        // query is frequently outside the bounded fragment: the VerifierConsumer bare-claim
        // obligation pairs the closed `(not (bvule #x0 #x1))` with
        // `(= r (bvlshr x #x1))` over free 64-bit variables, which the
        // interpreter declines — so asking about the pair threw away a
        // refutation it could decide in isolation. A subset that is UNSAT makes
        // the superset UNSAT, so the narrower lemma is the STRONGER claim, and
        // the committed proof then resolves only the assumes it actually uses.
        let all: Vec<TermId> = roots.iter().map(|&(root, _)| root).collect();
        let refuted: Option<Vec<(TermId, &FrontendTerm)>> = roots
            .iter()
            .find(|&&(root, _)| {
                ay_proof::authenticate_bv_lia_unsat_query(&self.ctx.terms, &[root], None).is_ok()
            })
            .map(|&pair| vec![pair])
            .or_else(|| {
                ay_proof::authenticate_bv_lia_unsat_query(&self.ctx.terms, &all, None)
                    .ok()
                    .map(|_| roots.clone())
            });
        let Some(selected) = refuted else {
            return false;
        };

        // (2b) Only the premises that will actually become `assume` leaves have
        // to round-trip. Rendering each through the SAME override-aware printer
        // the exporter uses, re-parsing, and requiring the author's own parsed
        // assertion back is what stops a normalized rebuild from producing the
        // one outcome strictly worse than the hole: a document whose `assume`
        // cannot be matched to any original problem premise.
        let mut roots: Vec<TermId> = Vec::new();
        if roots.try_reserve_exact(selected.len()).is_err() {
            return false;
        }
        for &(root, assertion) in &selected {
            if !self.rebuilt_root_prints_as_authored(root, assertion) {
                return false;
            }
            roots.push(root);
        }

        // (3) Build the candidate. `validate_bv_lia_tautology` requires every
        // clause literal to be an EXPLICIT outer negation so its inverse
        // mapping back to the roots is unambiguous; `mk_not_raw` must therefore
        // not fold, and a folded literal fails closed here.
        let mut clause: Vec<TermId> = Vec::new();
        if clause.try_reserve_exact(roots.len()).is_err() {
            return false;
        }
        for &root in &roots {
            let negated = self.ctx.terms.mk_not_raw(root);
            if !matches!(self.ctx.terms.get(negated), TermData::Not(inner) if *inner == root) {
                return false;
            }
            clause.push(negated);
        }

        let mut candidate = Proof::new();
        let assume_ids: Vec<ProofId> = roots
            .iter()
            .map(|&root| candidate.add_assume(root, None))
            .collect();
        let lemma = candidate.add_theory_lemma_with_kind(
            "BV/LIA",
            clause.clone(),
            TheoryLemmaKind::BvLiaTautology,
        );

        // Resolve the lemma against each authored assume in turn, peeling one
        // literal per step, so the terminal clause is empty.
        let mut current = lemma;
        let mut residual = clause;
        for (&assume_id, &root) in assume_ids.iter().zip(roots.iter()) {
            let Some(position) = residual
                .iter()
                .position(|&literal| matches!(self.ctx.terms.get(literal), TermData::Not(inner) if *inner == root))
            else {
                return false;
            };
            let _ = residual.remove(position);
            current = candidate.add_rule_step(
                AletheRule::ThResolution,
                residual.clone(),
                vec![current, assume_id],
                Vec::new(),
            );
        }

        // (4) Commit only what the UNCHANGED strict checker accepts whole.
        if !residual.is_empty()
            || !Self::proof_derives_empty_clause(&candidate)
            || !self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            return false;
        }
        *proof = candidate;
        true
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{AletheRule, Proof, TheoryLemmaKind};

    /// FALSIFY-ONCE for step (4). The promoter's whole soundness argument is
    /// that `BvLiaTautology` is re-derived by the strict checker rather than
    /// taken on the producer's word. Plant the byte-identical candidate over a
    /// SATISFIABLE authored assertion — `(or (< 2 0) (>= 2 1))`, whose second
    /// disjunct is true — and watch `check_proof_strict_with_datatypes` reject
    /// it. If this ever passes, the promoter is a false-proof machine.
    #[test]
    fn a_planted_tautology_lemma_over_a_satisfiable_root_is_rejected() {
        let commands = ay_frontend::parse(
            "(set-logic QF_LIA)\n(assert (or (< 2 0) (>= 2 1)))\n(assert (or (< 2 0) (>= 2 32)))",
        )
        .expect("fixture must parse");
        let mut executor = crate::Executor::new();
        executor
            .execute_all(&commands)
            .expect("fixture must elaborate");
        // Re-intern from the AUTHORED surface, exactly as the promoter does:
        // `ctx.assertions` holds the post-fold window, where the refutable root
        // has already become the constant `false`.
        let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
        assert_eq!(parsed.len(), 2, "fixture precondition: two authored roots");
        let satisfiable = executor
            .raw_intern_surface(&parsed[0])
            .expect("the satisfiable root must re-intern");
        let refutable = executor
            .raw_intern_surface(&parsed[1])
            .expect("the refutable root must re-intern");
        // Authorize both re-interned roots as problem premises, which is the
        // scope the promoter runs inside; otherwise the checker stops at
        // `UnauthorizedAssumption` before it ever reaches the lemma.
        executor.ctx.assertions = vec![satisfiable, refutable];
        let not_satisfiable = executor.ctx.terms.mk_not_raw(satisfiable);
        let not_refutable = executor.ctx.terms.mk_not_raw(refutable);

        // The exact three-step shape the promoter commits, one root each.
        let candidate = |root, negated| {
            let mut proof = Proof::new();
            let assume_id = proof.add_assume(root, None);
            let lemma = proof.add_theory_lemma_with_kind(
                "BV/LIA",
                vec![negated],
                TheoryLemmaKind::BvLiaTautology,
            );
            proof.add_rule_step(
                AletheRule::ThResolution,
                Vec::new(),
                vec![lemma, assume_id],
                Vec::new(),
            );
            proof
        };

        let honest =
            executor.check_proof_strict_with_datatypes(&candidate(refutable, not_refutable));
        assert!(
            honest.is_ok_and(|quality| quality.is_complete()),
            "control: the same shape over a genuinely false root must CHECK, or \
             this test proves nothing about the planted one"
        );

        let planted =
            executor.check_proof_strict_with_datatypes(&candidate(satisfiable, not_satisfiable));
        assert!(
            planted.is_err(),
            "a BvLiaTautology claiming a SATISFIABLE root is unsound; the strict \
             checker re-derives the query itself and must reject it"
        );
    }
}
