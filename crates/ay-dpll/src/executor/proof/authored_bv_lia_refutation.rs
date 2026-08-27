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
//! authority (that rule is pinned today by
//! `nested_row_auxiliary_refutation_publishes_under_an_explicit_proof_request`,
//! whose script once failed closed for exactly this reason until the
//! ROW-under-equality bridge closed its hole),
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
//!
//! ## The premise-scope gate, and why the strict checker is not it
//!
//! Printing back as authored is NOT the same property as being one of the
//! premises the Alethe exporter is handed. `alethe_printer`'s
//! `NonProblemAssume` — "preprocessing results must be derived, never silently
//! promoted to authored input" — tests exact `TermId` membership in the
//! exporter's premise set (`validate_reachable_assumes_in_problem_scope`), and
//! a raw re-intern the premise scope has not admitted fails it however
//! faithfully it prints.
//!
//! The strict checker cannot stand in for that test, because its premise set is
//! a strict SUPERSET of the exporter's:
//! `complete_problem_assertions_for_strict_proof` is
//! `proof_export_scope_assertions()` PLUS `self_check_authored_assertions` PLUS
//! `declared_obligation_extension()`. A root admitted only by one of those two
//! extensions passes `check_proof_strict_with_datatypes` and is then refused at
//! export — the one outcome strictly worse than the hole this promoter
//! replaces. So the promoter runs the EXPORTER'S OWN check against the
//! EXPORTER'S OWN set before it commits, and declines the whole recovery
//! otherwise.
//!
//! NO NEW AUTHORITY, matching `respell_certified_proof_over_authored_surface`:
//! this pass never calls `record_rebuilt_authored_proof_premise`, so it cannot
//! widen the premise scope by one term to make its own `assume` admissible.

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
        // (1b) PREMISE SCOPE. Only a term the exporter's own premise set already
        // admits may become an `assume`. A root the scope has not admitted is
        // not a candidate premise at all — dropping it only shrinks the question
        // asked below, exactly like a root that will not re-intern, which is the
        // safe direction. This pass adds nothing to the scope; it only reads it.
        let scope = self.proof_export_scope_assertions();
        for assertion in &parsed {
            let Some(root) = self.raw_intern_surface(assertion) else {
                continue;
            };
            if matches!(self.ctx.terms.sort(root), Sort::Bool) && scope.contains(&root) {
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
        // (2c) The gate the brief names, stated where the promotion decision is
        // made: every root that will become `(assume h_i A_i)` must be a member
        // of the premise scope. One failure declines the WHOLE recovery — a
        // partial refutation over a subset of the roots is a different (and
        // unproven) claim, so there is nothing to fall back to.
        if selected.iter().any(|&(root, _)| !scope.contains(&root)) {
            return false;
        }

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

        // (4) Commit only what the UNCHANGED strict checker accepts whole, AND
        // what the exporter's own authority check accepts against the exporter's
        // own premise set. Candidate construction interned raw negations, so the
        // scope is recomputed here rather than reused: the committed proof is
        // judged against the set as it stands at commit time.
        if !residual.is_empty()
            || !Self::proof_derives_empty_clause(&candidate)
            || !self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
            || ay_proof::validate_reachable_assumes_in_problem_scope(
                &candidate,
                &self.proof_export_scope_assertions(),
            )
            .is_err()
        {
            return false;
        }
        *proof = candidate;
        true
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{AletheRule, Proof, ProofStep, TermId, TheoryLemmaKind};

    /// The exact three-step shape the promoter commits for one root.
    fn candidate(root: TermId, negated: TermId) -> Proof {
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
    }

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

    /// FALSIFY-ONCE for the premise-scope gate, reporting BOTH observed states.
    ///
    /// The gate's whole claim is that the STRICT CHECKER IS NOT THE EXPORTER.
    /// `complete_problem_assertions_for_strict_proof` is
    /// `proof_export_scope_assertions()` plus `self_check_authored_assertions`
    /// plus `declared_obligation_extension()`, so a root admitted by only one
    /// of those extensions passes `check_proof_strict_with_datatypes` and is
    /// then refused by `alethe_printer` as a `NonProblemAssume`. Before the
    /// gate, the promoter committed exactly that proof: internally certified,
    /// externally unexportable — the one outcome strictly worse than the hole
    /// it replaces.
    ///
    /// The violation is PLANTED by moving the grant out of the export scope and
    /// into the strict-only extension, which changes nothing else about the
    /// query. Both states are asserted:
    ///
    /// * ADMITTED — the grant in the export scope: the promoter COMMITS, and
    ///   the exporter's own authority check accepts the committed proof.
    /// * PLANTED  — the same grant strict-only: the strict checker STILL
    ///   accepts the byte-identical candidate (so the strict checker demonstrably
    ///   is not what stops it), the exporter's own check REJECTS it, and the
    ///   promoter DECLINES, leaving the caller's proof untouched.
    #[test]
    fn a_root_only_the_strict_scope_admits_declines_the_promoter() {
        let commands =
            ay_frontend::parse("(set-logic QF_LIA)\n(assert (or (< 2 0) (>= 2 32)))\n(check-sat)")
                .expect("fixture must parse");
        let mut executor = crate::Executor::new();
        executor.set_produce_proofs(true);
        executor
            .execute_all(&commands)
            .expect("fixture must elaborate");

        let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
        assert_eq!(parsed.len(), 1, "fixture precondition: one authored root");
        let root = executor
            .raw_intern_surface(&parsed[0])
            .expect("the authored root must re-intern");
        assert!(
            !executor.ctx.assertions.contains(&root),
            "fixture precondition: the fold overwrote the authored slot, so the \
             raw re-intern is reachable only through the recorded premise grant"
        );

        // ---- ADMITTED: the grant is in the export scope. -------------------
        assert!(
            executor.proof_export_scope_assertions().contains(&root),
            "fixture precondition: the export scope must already admit the raw \
             re-intern, or the ADMITTED half of this test proves nothing"
        );
        let mut admitted = Proof::new();
        admitted.add_rule_step(AletheRule::Hole, Vec::new(), Vec::new(), Vec::new());
        assert!(
            executor.replace_with_exact_authored_bv_lia_refutation(&mut admitted),
            "ADMITTED: an authored root the export scope admits must still be \
             promoted; the gate may not cost a recovery that works"
        );
        assert!(
            ay_proof::validate_reachable_assumes_in_problem_scope(
                &admitted,
                &executor.proof_export_scope_assertions(),
            )
            .is_ok(),
            "ADMITTED: the committed proof must satisfy the exporter's own \
             authority check"
        );

        // ---- PLANTED: the same grant, strict-only. --------------------------
        // Nothing about the query changes; only WHICH premise set holds the
        // grant. `self_check_authored_assertions` feeds
        // `complete_problem_assertions_for_strict_proof` and NOT
        // `proof_export_scope_assertions`.
        executor.last_proof_rebuild_originals.clear();
        executor.self_check_authored_assertions = Some(vec![root]);
        assert!(
            !executor.proof_export_scope_assertions().contains(&root),
            "planted precondition: the export scope must no longer admit the root"
        );

        let negated = executor.ctx.terms.mk_not_raw(root);
        let planted = candidate(root, negated);
        assert!(
            executor
                .check_proof_strict_with_datatypes(&planted)
                .is_ok_and(|quality| quality.is_complete()),
            "PLANTED: the strict checker must still ACCEPT the byte-identical \
             candidate — that is the whole point: it is not the gate"
        );
        assert!(
            ay_proof::validate_reachable_assumes_in_problem_scope(
                &planted,
                &executor.proof_export_scope_assertions(),
            )
            .is_err(),
            "PLANTED: the exporter's own authority check must refuse it, or the \
             planted state does not model the defect"
        );

        let mut untouched = Proof::new();
        untouched.add_rule_step(AletheRule::Hole, Vec::new(), Vec::new(), Vec::new());
        assert!(
            !executor.replace_with_exact_authored_bv_lia_refutation(&mut untouched),
            "PLANTED: the promoter must DECLINE a root the exporter's premise \
             set has not admitted, not publish an unexportable proof"
        );
        assert!(
            matches!(
                untouched.steps.as_slice(),
                [ProofStep::Step {
                    rule: AletheRule::Hole,
                    ..
                }]
            ),
            "PLANTED: a declined recovery must leave the erasure exactly as it \
             was, got {:?}",
            untouched.steps
        );
    }
}
