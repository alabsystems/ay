// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed false-assumption and duplicate-distinct collapse repair.

use super::*;

/// Whether the final fail-closed repair may bind an otherwise unsupported
/// collapse to its authored premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PremiseBindingFallback {
    Disallowed,
    Allowed,
}

impl PremiseBindingFallback {
    const fn is_allowed(self) -> bool {
        matches!(self, Self::Allowed)
    }
}

impl Executor {
    /// Attempt only independently checkable false-collapse reconstructions.
    pub(in crate::executor) fn try_rebuild_false_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        authored_originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        self.try_rebuild_false_collapse_with_policy(
            proof,
            originals,
            authored_originals,
            PremiseBindingFallback::Disallowed,
        )
    }

    /// Attempt checkable reconstruction, then the authored-premise binding
    /// fallback when the proof language cannot express the source theory.
    pub(in crate::executor) fn try_bind_false_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        authored_originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        self.try_rebuild_false_collapse_with_policy(
            proof,
            originals,
            authored_originals,
            PremiseBindingFallback::Allowed,
        )
    }

    /// Preprocessor fold-to-`false` collapse repair (#trust-count→0,
    /// carcara-invalid→valid). When the PREPROCESSOR itself derives the
    /// contradiction (e.g. `(assert (distinct x x))`, `(assert (= 1 2))`,
    /// `(assert (and p (not p)))`), the exported proof degenerates to the
    /// 3-step shape
    ///
    /// ```text
    /// (assume t0 X)
    /// (step t1 (cl (not X)) :rule false :args (X))   ; NOT the Alethe `false`
    /// (step t2 (cl) :rule resolution :premises (t0 t1))
    /// ```
    ///
    /// whose `:rule false` step misuses the Alethe `false` rule (`⊢ (cl (not
    /// false))`) and is rejected by external checkers. This pass recognizes
    /// the whole-proof shape and re-proves `(cl (not X))` from the ORIGINAL
    /// assertion `X`'s own structure with certified steps:
    ///
    /// - **`(distinct .. t .. t ..)` with a syntactically duplicated operand**
    ///   — `distinct_elim` + `equiv_pos2` (+ `and_pos` for the n-ary
    ///   conjunction form) down to `(not (= t t))`, refuted by
    ///   `eq_reflexive`.
    /// - **ground linear-arithmetic literal falsity** — derive the complement
    ///   of an authored `=`, `<`, `<=`, `>`, or `>=` atom (optionally under one
    ///   `not`) through either a sign-resolved, independently re-verified
    ///   `la_generic` row or a primitive checked `evaluate` derivation.
    /// - **a closed ground linear DISJUNCTION** — `(or (< 2 0) (>= 2 32))`,
    ///   every disjunct false on its own: `or` elimination onto a clause, one
    ///   independently re-verified one-row `la_generic` per disjunct, and one
    ///   resolution each down to the empty clause.
    /// - **`(and .. p .. (not p) ..)` with a syntactically complementary
    ///   conjunct pair** — two `and_pos` extractions resolved to `⊥`.
    ///
    /// Fail-closed: any other assertion shape (or a failed certificate)
    /// leaves the proof byte-identical, keeping the honest defective step
    /// visible rather than fabricating an unchecked derivation.
    ///
    /// The collapse's assume holds the FOLDED canonical term (`false`), so
    /// shape dispatch uses the parsed ORIGINAL assertion whose canonical form
    /// is that assumed term. Repairs either use the immutable, index-aligned
    /// authored root directly or reconstruct exact raw source syntax; a
    /// normalized re-elaboration is never admitted as premise authority.
    fn try_rebuild_false_collapse_with_policy(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        authored_originals: &[(TermId, FrontendTerm)],
        premise_binding_fallback: PremiseBindingFallback,
    ) -> bool {
        let Some(FalseCollapseShape {
            assume,
            assume_count,
            false_step,
            trust_false,
            lia_lemma,
        }) = self.recognize_false_collapse_shape(proof)
        else {
            return false;
        };
        // Substitution-chain shape: equality assumes closed by ONE
        // `lia_generic` lemma (an external checker HOLE). Re-prove from the
        // original equalities with a synthesized, re-verified `la_generic`
        // certificate (fail-closed: any non-equality original keeps the
        // proof unchanged).
        if lia_lemma {
            if trust_false || false_step.is_some() || assume_count == 0 {
                return false;
            }
            return self.rebuild_consumed_equalities_collapse(proof, originals);
        }
        // Shape C: the preprocessor consumed the assertions entirely — the
        // proof is the bare `(cl false) :rule trust` (no assume, no
        // derivation). Re-prove from the ORIGINAL arithmetic-equality
        // assertions with a synthesized, re-verified Farkas certificate.
        if trust_false {
            // Any accompanying `false` step must be the proper-form wiring
            // `(cl (not false))` for `(cl false)`'s refutation.
            let wiring_ok = match false_step {
                None => true,
                Some((lit, arg)) => {
                    matches!(
                        self.ctx.terms.get(arg),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) && atom_of(&self.ctx.terms, lit) == arg
                        && lit != arg
                }
            };
            if assume_count == 0 && wiring_ok {
                return self.rebuild_consumed_equalities_collapse(proof, originals)
                    || self.rebuild_congruence_collapse(proof, originals)
                    // Last resort (#dt-premise-binding): neither certified
                    // rebuild applies (e.g. a DATATYPE refutation — Alethe has
                    // no datatype rules, and neither does any checker). Still
                    // bind the premises: see the doc comment.
                    || (premise_binding_fallback.is_allowed()
                        && self.rebuild_premise_binding_collapse(proof, originals));
            }
            return false;
        }
        if assume_count != 1 {
            return false;
        }
        let (Some(x), Some((neg_lit, arg))) = (assume, false_step) else {
            return false;
        };
        if arg != x || atom_of(&self.ctx.terms, neg_lit) != x || neg_lit == x {
            return false;
        }

        self.try_rebuild_false_collapse_from_originals(proof, x, originals, authored_originals)
    }

    /// `(distinct ..)` with a syntactically duplicated operand: derive
    /// `(not (= t t))` via `distinct_elim` + `equiv_pos2` (+ `and_pos` for
    /// n-ary) and refute it with `eq_reflexive`.
    pub(super) fn rebuild_duplicate_distinct_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut args = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.ctx.elaborate_surface_subterm(op) else {
                return false;
            };
            args.push(t);
        }
        let args = &args[..];
        // Re-intern the folded `distinct` application RAW: the new assume
        // must print like the problem file. Fail-closed if the interner
        // folds it (the derivation would not match the premise).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("distinct"), args, Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "distinct" && a.len() == args.len()
        ) {
            return false;
        }
        let n = args.len();
        let Some((di, dj)) = (0..n)
            .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
            .find(|&(i, j)| args[i] == args[j])
        else {
            return false;
        };
        // Carcara's `distinct_elim` special-cases >2 Bool operands (they
        // collapse to `false`, a different bridge): out of scope.
        if n > 2 && matches!(self.ctx.terms.sort(args[0]), Sort::Bool) {
            return false;
        }
        let terms = &mut self.ctx.terms;
        let dup = args[di];
        let eq_dup = terms.mk_app(Symbol::named("="), [dup, dup], Sort::Bool);
        if !matches!(
            terms.get(eq_dup),
            TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == dup && a[1] == dup
        ) {
            return false;
        }
        let not_eq_dup = terms.mk_not_raw(eq_dup);
        let not_x = terms.mk_not_raw(x);

        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        if n == 2 {
            // (= (distinct t t) (not (= t t)))
            let equiv = terms.mk_app(Symbol::named("="), [x, not_eq_dup], Sort::Bool);
            let not_equiv = terms.mk_not_raw(equiv);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, not_eq_dup],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_x, not_eq_dup], equiv, ep, de);
            let r2 = new_proof.add_resolution(vec![not_eq_dup], x, r1, assume_id);
            let er = new_proof.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_dup],
                Vec::new(),
                Vec::new(),
            );
            new_proof.add_resolution(Vec::new(), eq_dup, r2, er);
        } else {
            // (= (distinct x1..xn) (and (not (= xi xj)) ..)) in `i < j` order.
            let mut conjs: Vec<TermId> = Vec::with_capacity(n * (n - 1) / 2);
            let mut dup_pos = 0usize;
            let mut k = 0usize;
            for i in 0..n {
                for j in (i + 1)..n {
                    let eq = terms.mk_app(Symbol::named("="), [args[i], args[j]], Sort::Bool);
                    conjs.push(terms.mk_not_raw(eq));
                    if (i, j) == (di, dj) {
                        dup_pos = k;
                    }
                    k += 1;
                }
            }
            let and_term = terms.mk_app(Symbol::named("and"), conjs.clone(), Sort::Bool);
            if !matches!(
                terms.get(and_term),
                TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
            ) {
                return false;
            }
            let not_and = terms.mk_not_raw(and_term);
            let equiv = terms.mk_app(Symbol::named("="), [x, and_term], Sort::Bool);
            let not_equiv = terms.mk_not_raw(equiv);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, and_term],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_x, and_term], equiv, ep, de);
            let r2 = new_proof.add_resolution(vec![and_term], x, r1, assume_id);
            #[allow(clippy::cast_possible_truncation)]
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(dup_pos as u32),
                vec![not_and, conjs[dup_pos]],
                Vec::new(),
                Vec::new(),
            );
            let r3 = new_proof.add_resolution(vec![conjs[dup_pos]], and_term, ap, r2);
            let er = new_proof.add_rule_step(
                AletheRule::EqReflexive,
                vec![eq_dup],
                Vec::new(),
                Vec::new(),
            );
            new_proof.add_resolution(Vec::new(), eq_dup, r3, er);
        }
        *proof = new_proof;
        true
    }
}
