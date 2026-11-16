// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Last-resort QF_BV whole-proof collapse reconstruction.

use ay_core::kani_compat::DetHashSet;
use ay_core::{AletheRule, Proof, ProofId, Sort, TermData, TermId, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;

use super::super::Executor;
use super::{build_qfbv_pterm, term_contains_bitvec};

impl Executor {
    /// Prefer a strict-checkable anchor over an unchecked `hole`. When the
    /// joint negation of the parsed assertions is an independently
    /// recognized BV bit-blast tautology, anchor the refutation on a
    /// `BvBitBlast` theory lemma. AY's strict checker re-validates that lemma
    /// by bit-blasting the exact clause and demanding an LRAT refutation it
    /// replays (see `ay_proof::checker::bv_bitblast`), so the reconstructed
    /// proof is trust-free for AY's own self-check / strict-proofs gate —
    /// the honest `hole` was only ever needed because the *pinned external*
    /// checker has no rule for this bit-blast lane. On the Alethe wire a
    /// general `BvBitBlast` lemma still prints as the same honest `hole`
    /// (`alethe_printer` lowers only the exactly-reconstructible subset), so
    /// no external document regresses: carcara continues to accept the
    /// document as *holey*, never *valid*, and never as a false certificate.
    ///
    /// Fail-closed at two gates: the lemma clause must be `recognize_bv_bitblast`
    /// (which re-derives the conflict, never trusting a label), AND the
    /// assembled bit-blast document must itself re-check strict-complete
    /// before it is committed. If either declines, fall back to the honest
    /// attributed `hole` exactly as before.
    fn strict_bv_bitblast_collapse_candidate(
        &self,
        assertion_ids: &[TermId],
        negated: &[TermId],
    ) -> Option<Proof> {
        if !self.recognize_bv_bitblast_until_stopped(negated) {
            return None;
        }

        let mut candidate = Proof::new();
        let assume_ids: Vec<ProofId> = assertion_ids
            .iter()
            .map(|&t| candidate.add_assume(t, None))
            .collect();
        let mut current = candidate.add_theory_lemma_with_kind(
            "bv",
            negated.to_vec(),
            TheoryLemmaKind::BvBitBlast,
        );
        let mut residual = negated.to_vec();
        for (&assume_id, &opposite) in assume_ids.iter().zip(negated.iter()) {
            residual.retain(|&literal| literal != opposite);
            current = candidate.add_rule_step(
                AletheRule::ThResolution,
                residual.clone(),
                vec![current, assume_id],
                Vec::new(),
            );
        }
        if residual.is_empty()
            && Self::proof_derives_empty_clause(&candidate)
            && self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            Some(candidate)
        } else {
            None
        }
    }

    /// BV bit-blast whole-proof collapse rescue (C5). See the call-site comment
    /// in `build_unsat_proof` for the full rationale. Fires ONLY when the proof
    /// is the degenerate single-empty-trust collapse (both legacy and
    /// `:rule false` encodings) and every parsed problem assertion faithfully
    /// rebuilds inside the QF_BV boolean/bitvector fragment with at least one
    /// genuinely BV-sorted node. When the exact joint negation is recognized
    /// and strict-replayed, the anchor is a `BvBitBlast` lemma. Otherwise the
    /// original fallback emission remains:
    ///   assume A_1 … assume A_n            (faithful raw rebuilds; carcara
    ///                                       checks them against the problem)
    ///   hole   (cl (not A_1) … (not A_n))  (the joint-UNSAT the bit-blast +
    ///                                       SAT lane established; carcara has
    ///                                       no rule for ay's blasting, so the
    ///                                       spec `hole` placeholder is the
    ///                                       honest encoding — attributed,
    ///                                       counted, and still rejected by
    ///                                       the strict-proofs gate)
    ///   resolution chain ⟹ (cl)
    /// SOUND: introduces no claim beyond the verdict already established (the
    /// hole clause is logically the same statement as the empty-clause trust
    /// step it replaces, now anchored to the real problem assertions).
    /// Fail-closed: any rebuild miss keeps the original proof untouched.
    pub(super) fn rescue_bv_bitblast_collapse(&mut self, proof: &mut Proof) {
        // LAST RESORT ONLY: fire on the still-degenerate collapse, never on a
        // proof one of the specific promoters above already reconstructed.
        //
        // This gate was briefly generalised to
        // `proof_needs_schema_collapse_reconstruction` — "any proof deriving the
        // empty clause" — to match the specific promoters. That predicate is
        // right for THEM (they replace a proof with a strict-checkable typed
        // lemma, so seeing more candidates can only add certificates) and wrong
        // for this rescue, whose product is an `assume`-anchored `hole`. With the
        // wide gate the rescue ran on every empty-clause QF_BV proof and
        // OVERWROTE the `BvBitBlast` certificate `promote_bv_identity_collapse`
        // had just built a few lines earlier — trading a fully strict-checked
        // refutation (and its Lean firewall artifact) for an unchecked hole.
        // Measured on `(not (= (bvand x x) x))`: the promoted proof became
        // `[assume A, hole (¬A), resolution]`, failed strict checking with
        // `HoleStep`, and was then replaced downstream by a content-free
        // `assume false` refutation.
        //
        // The degenerate shape is exactly "no specific promoter reconstructed
        // it": each promoter replaces the proof with `assume (not THEOREM)` for
        // a real authored theorem, which is not an assumed Boolean constant.
        if !Self::proof_is_single_empty_trust(proof) {
            return;
        }
        // The word-level ground closure first: on a pure bit-vector query it
        // decides by congruence and slice identities what the joint-negation
        // lemma below re-decides by bit-blasting every circuit at once, which
        // spends the query's whole budget on a multiplier (external-codegen's x86-64
        // `imul` overflow bodies, measured on 84dbf0bdb: 30 s, `unknown`).
        // A decline leaves `proof` untouched for the rescue below.
        if self.try_pure_bit_vector_ground_closure_first(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        if parsed.is_empty() {
            return;
        }
        let mut assertion_ids: Vec<TermId> = Vec::with_capacity(parsed.len());
        for asrt in &parsed {
            let Some(t) = build_qfbv_pterm(&mut self.ctx.terms, asrt) else {
                return; // outside the QF_BV fragment — keep the trust proof
            };
            if !matches!(self.ctx.terms.sort(t), Sort::Bool) {
                return;
            }
            assertion_ids.push(t);
        }

        // #trust-lemma-dup-assume, this lane's instance. The parsed assertion
        // list can hold the SAME term more than once (the identical assertion
        // asserted twice). Every occurrence contributes ONE literal to
        // `negated`, but a clause is a SET: the checker decodes the head and
        // every resolvent through `clause_as_set`, which sorts and dedups.
        //
        // Both emissions below break on a repeated literal, in mirror-image
        // ways. The fallback chain removes ONE occurrence per step
        // (`remaining.remove(0)`), so the FIRST resolution against a repeated
        // literal records a resolvent that still carries the duplicate the
        // checker's resolution already eliminated — the step is rejected as
        // `invalid resolution derivation`. The strict `th_resolution` anchor
        // uses `retain`, which drops ALL copies at once, so the LATER
        // duplicate resolves against a premise with no complement left, which
        // is not a resolution either. Only the strict path is gated by its own
        // re-check and so merely loses its anchor; the fallback PUBLISHES its
        // invalid chain, and the mandatory certification gate then correctly
        // refuses the whole refutation.
        //
        // Measured on `repros/unsat-cert/chc_array_pred_invalid_resolution.smt2`,
        // whose parsed assertions hold `(= i #b0..0)` twice: step t16 resolved
        // premise t15 (two copies of `(not (= i 0))`) against that assumption
        // and kept one copy, so the recorded resolvent had four literals where
        // the checker derives three.
        //
        // Deduplicating by term fixes both: every head literal is unique, so
        // exactly one occurrence is removed per step under BOTH positional and
        // set semantics. Nothing is weakened and no claim is widened — a
        // repeated literal is redundant in a clause, so the head states the
        // same proposition over the same assumptions, and every step is still
        // replayed by the untouched checker.
        {
            let mut seen = DetHashSet::default();
            assertion_ids.retain(|&t| seen.insert(t));
        }

        // Scope guard: this rescue is the BV lane's. Require at least one
        // BitVec-sorted node among the rebuilt assertions so pure-Boolean
        // collapses keep their (honest) trust step for other passes/lanes.
        if !assertion_ids
            .iter()
            .any(|&t| term_contains_bitvec(&self.ctx.terms, t))
        {
            return;
        }

        let negated: Vec<TermId> = assertion_ids
            .iter()
            .map(|&t| self.ctx.terms.mk_not_raw(t))
            .collect();
        // Faithfulness guard on the negations (mk_not_raw must not fold).
        for (&n, &t) in negated.iter().zip(assertion_ids.iter()) {
            if !matches!(self.ctx.terms.get(n), TermData::Not(inner) if *inner == t) {
                return;
            }
        }

        // A strict-checkable anchor is what makes this rescue's document
        // PUBLISHABLE, so every term it prints must survive the printer's
        // surface-override table -- the same gate every collapse promoter
        // applies to its raw rebuilds (see `rebuilt_terms_print_faithfully`).
        // A folded array read attaches the whole read's authored spelling to
        // the composite leaf it collapsed to, and the raw rebuild legitimately
        // uses that leaf in unfolded positions, so the `assume` would no longer
        // be the problem's assertion. Keep the honest `hole` below in that
        // case: mandatory strict certification then withholds the UNSAT rather
        // than publish a document AY cannot stand behind.
        let printed: Vec<TermId> = assertion_ids
            .iter()
            .chain(negated.iter())
            .copied()
            .collect();
        let strict_anchor = if self.rebuilt_terms_print_faithfully(&printed) {
            // Where the anchor would pay for an exact divider, an authored
            // `bvurem` obligation the BvUremBound theorem closes is certified
            // first (`bv_identity_promotion/guarded/urem_bound/before_division.rs`).
            if self.promote_urem_bound_before_rescue_anchor(proof, &negated) {
                return;
            }
            self.strict_bv_bitblast_collapse_candidate(&assertion_ids, &negated)
        } else {
            None
        };
        if let Some(candidate) = strict_anchor {
            *proof = candidate;
            return;
        }

        proof.steps.clear();
        proof.named_steps.clear();
        let assume_ids: Vec<ProofId> = assertion_ids
            .iter()
            .map(|&t| proof.add_assume(t, None))
            .collect();
        let mut current =
            proof.add_rule_step(AletheRule::Hole, negated.clone(), Vec::new(), Vec::new());
        let mut remaining = negated;
        for (idx, &assume_id) in assume_ids.iter().enumerate() {
            // Drop (not A_idx): resolved against assume A_idx. The removed
            // literal's id is known by construction and deliberately unused.
            let _ = remaining.remove(0);
            current =
                proof.add_resolution(remaining.clone(), assertion_ids[idx], current, assume_id);
        }
        debug_assert_eq!(remaining.as_slice(), &[] as &[TermId]);
        let _ = current;
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{AletheRule, ProofStep, TheoryLemmaKind};
    use ay_frontend::parse;

    use super::Executor;

    /// The last-resort QF_BV collapse rescue must anchor a bit-blastable conflict on
    /// a strict-checkable `BvBitBlast` lemma, not an unchecked `hole`.
    ///
    /// A Boolean-structured QF_BV conflict (a model-checker-style mc-join guard over
    /// `bvuge`) is established by the eager bit-blast + SAT lane, but its
    /// reconstructed proof degenerates to the single empty-clause collapse that no
    /// specific promoter reconstructs, so `rescue_bv_bitblast_collapse` is the
    /// fallback that runs. When the joint negation of the parsed assertions is an
    /// independently recognized bit-blast tautology, that rescue must emit a
    /// strict-checkable `BvBitBlast` theory lemma (AY re-derives the conflict by
    /// bit-blasting the exact clause and demanding an LRAT refutation it replays),
    /// leaving no `hole`/`trust` on the empty-clause path — so AY's own strict
    /// checker certifies the refutation trust-free. (On the Alethe wire a general
    /// `BvBitBlast` lemma still prints as an honest `hole`; the improvement is
    /// entirely in AY's strict acceptance path, never a false external certificate.)
    #[test]
    fn mc_join_bv_collapse_rescue_emits_checkable_bitblast_not_hole() {
        let input = r#"(set-option :produce-proofs true)(set-logic QF_BV)
            (declare-const cond Bool)
            (declare-const value (_ BitVec 32))
            (declare-const ge Bool)
            (assert (= ge (or (not cond) cond)))
            (assert (=> (not cond) (= value (_ bv2 32))))
            (assert (=> cond (= value (_ bv1 32))))
            (assert (and ge (not (bvuge value (_ bv1 32)))))
            (check-sat)"#;
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
        let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::BvBitBlast,
                    ..
                }
            )),
            "the bit-blastable mc-join collapse must carry a strict-checkable \
             BvBitBlast lemma; got {:#?}",
            proof.steps
        );
        assert!(
            !proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Hole,
                    ..
                }
            )),
            "no unchecked hole may remain once the conflict is bit-blastable; got {:#?}",
            proof.steps
        );
        assert!(
            ay_proof::terminal_trust_report(proof).is_trust_free(),
            "the reconstructed BV proof must be trust-free for AY's strict checker; \
             got {:#?}",
            proof.steps
        );
        exec.check_proof_strict_with_datatypes(proof)
            .expect("the reconstructed BvBitBlast proof must replay strictly");
    }

    /// REGRESSION (#trust-lemma-dup-assume, this lane). A parsed assertion list
    /// holding the SAME assertion twice must still emit a resolution chain the
    /// untouched checker accepts.
    ///
    /// Before the dedup, `negated` carried the repeated literal twice, the
    /// fallback chain removed ONE occurrence per step, and the FIRST resolution
    /// against the repeat recorded a resolvent still carrying a literal the
    /// checker's set-semantics resolution had already eliminated — published as
    /// `step tN has invalid resolution derivation`. Measured end to end on
    /// `repros/unsat-cert/chc_array_pred_invalid_resolution.smt2` (step t16).
    #[test]
    fn a_duplicated_parsed_assertion_still_emits_a_checkable_resolution_chain() {
        use ay_core::term::Symbol;
        use ay_core::{Proof, Sort};
        use ay_frontend::command::Term as FrontendTerm;

        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("dupbv_x", Sort::bitvec(32));
        let y = exec.ctx.terms.mk_var("dupbv_y", Sort::bitvec(32));
        let lt = exec
            .ctx
            .terms
            .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
        let parsed = FrontendTerm::App(
            "bvult".to_string(),
            vec![
                FrontendTerm::Symbol("dupbv_x".to_string()),
                FrontendTerm::Symbol("dupbv_y".to_string()),
            ],
        );
        // The identical assertion, asserted twice: the defect's precondition.
        exec.ctx.add_assertion_with_parsed(lt, parsed.clone());
        exec.ctx.add_assertion_with_parsed(lt, parsed);

        // The degenerate single-empty-trust collapse is what arms the rescue.
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        exec.rescue_bv_bitblast_collapse(&mut proof);

        let head_literals: Vec<usize> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::Hole,
                    clause,
                    ..
                } => Some(clause.len()),
                _ => None,
            })
            .collect();
        assert!(
            head_literals.iter().all(|&n| n == 1),
            "the head must carry one literal per DISTINCT assertion, got {head_literals:?} in {:#?}",
            proof.steps
        );

        let (_summary, error) = ay_proof::check_proof_partial(&proof, &exec.ctx.terms);
        assert!(
            error.is_none(),
            "the emitted chain must replay: {error:?}\n{:#?}",
            proof.steps
        );
    }

    /// NEGATIVE CONTROL. The fix must not have taught the checker to tolerate
    /// the bad shape: the exact pre-fix emission — a head carrying the repeated
    /// literal twice and a chain removing one occurrence per step — must still
    /// be REFUSED as an invalid resolution derivation.
    #[test]
    fn the_pre_fix_duplicated_head_chain_is_still_refused() {
        use ay_core::{Proof, Sort, TermStore};

        let mut terms = TermStore::new();
        let a = terms.mk_var("negctl_a", Sort::Bool);
        let not_a = terms.mk_not_raw(a);

        let mut proof = Proof::new();
        let first = proof.add_assume(a, None);
        let second = proof.add_assume(a, None);
        let head =
            proof.add_rule_step(AletheRule::Hole, vec![not_a, not_a], Vec::new(), Vec::new());
        // Removes ONE copy; the checker resolves over SETS and removes both.
        let partial_step = proof.add_resolution(vec![not_a], a, head, first);
        proof.add_resolution(Vec::new(), a, partial_step, second);

        let (_summary, error) = ay_proof::check_proof_partial(&proof, &terms);
        assert!(
            matches!(
                error,
                Some(ay_proof::ProofCheckError::InvalidResolution { .. })
            ),
            "a genuinely invalid resolution must still be refused, got {error:?}"
        );
    }

    /// REGRESSION (AY-03), on the query that surfaced it in the field.
    ///
    /// compiler_consumer 321aaeda7 (ay 075a482ae) logged `internal proof checker rejected
    /// UNSAT proof, error=step t48 has invalid resolution derivation` (a 95-step
    /// proof) while verifying unicode-ident-1.0.24 `is_xid_start`. Re-running
    /// that obligation through ay 075a482ae's `engines::solve_pdr_proof`
    /// rejected a 95-step proof the same way at t50, and the fixture holds
    /// that proof's 47 `assume` steps: 45 distinct assertions, with
    /// `(bvule 0 ch)` and `(bvule ch 4294967295)` each asserted twice.
    ///
    /// Hand-check of that t50 from the dump. Premise t49 carries
    /// `(not (bvule 0 ch))` twice and t2 is `assume (bvule 0 ch)`. The recorded
    /// conclusion keeps one copy, so as a set it has 43 literals. The set
    /// resolvent on that pivot has 42: the same literals minus
    /// `(not (bvule 0 ch))`. The step is a multiset resolution, a sound
    /// weakening but not the resolution the checker validates. So the producer
    /// was at fault, not the checker. ca0dd42ad fixed the producer by
    /// deduplicating these assertions, and backporting that dedup onto
    /// 075a482ae removed the rejection for this obligation.
    ///
    /// This drives the rescue on the real assertion list (two separate repeats,
    /// interleaved with 128-bit BV terms) and requires the untouched checker to
    /// accept what it emits.
    #[test]
    fn unicode_ident_pdr_query_with_repeated_assertions_rescues_to_a_checkable_chain() {
        use ay_core::Proof;
        use ay_frontend::command::Command;

        let input =
            include_str!("../../../tests/fixtures/unicode_ident_pdr_duplicate_assertions.smt2");
        // Elaborate the declarations and assertions without solving: the
        // rescue is driven directly, on the degenerate collapse that arms it.
        let commands: Vec<Command> = parse(input)
            .expect("fixture must parse")
            .into_iter()
            .filter(|command| !matches!(command, Command::CheckSat))
            .collect();
        let mut exec = Executor::new();
        exec.execute_all(&commands)
            .expect("fixture declarations and assertions must elaborate");
        assert_eq!(
            exec.ctx.assertions_parsed().len(),
            47,
            "the fixture's repeated assertions must reach the rescue as authored"
        );

        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        exec.rescue_bv_bitblast_collapse(&mut proof);
        assert!(
            !Executor::proof_is_single_empty_trust(&proof),
            "the rescue must fire on this QF_BV assertion list; got {:#?}",
            proof.steps
        );

        let (_summary, error) = ay_proof::check_proof_partial(&proof, &exec.ctx.terms);
        assert!(
            error.is_none(),
            "the rescued refutation must replay through the untouched checker, got {error:?}"
        );
    }
}
