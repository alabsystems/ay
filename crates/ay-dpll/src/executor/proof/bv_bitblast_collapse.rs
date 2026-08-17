// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Last-resort QF_BV whole-proof collapse reconstruction.

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
        if !ay_proof::recognize_bv_bitblast(&self.ctx.terms, negated) {
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

        if let Some(candidate) =
            self.strict_bv_bitblast_collapse_candidate(&assertion_ids, &negated)
        {
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
        debug_assert!(remaining.is_empty());
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
}
