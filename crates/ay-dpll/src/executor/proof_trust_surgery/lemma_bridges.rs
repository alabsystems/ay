// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independently checked arithmetic and equality bridge lemmas.

use super::*;

impl Executor {
    /// Whether `(cl (not eq) (not p) concl)` is a valid `[1, 1, 1]`
    /// `la_generic` lemma per the independent Farkas checker (the equality
    /// `eq` and atom `p` asserted true, `concl` asserted false).
    pub(super) fn triple_lemma_valid(&self, eq: TermId, p: TermId, concl: TermId) -> bool {
        self.triple_lemma_valid_with(eq, p, concl, &FarkasAnnotation::from_ints(&[1, 1, 1]))
    }

    /// [`Self::triple_lemma_valid`] against EXPLICIT Farkas coefficients (the
    /// coefficients the emitter will print, so validation and export cannot
    /// diverge).
    fn triple_lemma_valid_with(
        &self,
        eq: TermId,
        p: TermId,
        concl: TermId,
        farkas: &FarkasAnnotation,
    ) -> bool {
        let lits: Vec<TheoryLit> = [eq, p]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .chain(std::iter::once(match self.ctx.terms.get(concl) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(concl, false),
            }))
            .collect();
        // `_linear`, NOT `_full`: the lemma exports as `la_generic`, and
        // external checkers perform no congruence reasoning inside
        // `la_generic` — the opaque ite term must cancel purely linearly.
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            farkas,
        )
        .is_ok()
    }

    /// Emit a `la_generic` theory lemma `(cl a b c)` carrying `farkas`. Only
    /// called for triples already validated by [`Self::triple_lemma_valid`]
    /// / [`Self::triple_lemma_valid_with`] against THESE coefficients.
    fn add_triple_lemma(
        new_proof: &mut Proof,
        a: TermId,
        b: TermId,
        c: TermId,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b, c],
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Emit ONLY the then-side transfer lemma of a guarded then-projection
    /// plan (`(cl (not eq_then) (not orig) lifted_then)`), carrying the exact
    /// coefficients recognition verified.
    pub(super) fn add_guarded_then_transfer_lemma(
        proof: &mut Proof,
        plan: &IteLiftPlan,
        not_eq_then: TermId,
        not_orig: TermId,
    ) -> ProofId {
        Self::add_triple_lemma(
            proof,
            not_eq_then,
            not_orig,
            plan.lifted_then,
            plan.then_coeffs.clone(),
        )
    }

    pub(super) fn add_ite_transfer_lemmas(
        proof: &mut Proof,
        plan: &IteLiftPlan,
        not_eq_then: TermId,
        not_eq_else: TermId,
        not_orig: TermId,
        not_bound: Option<TermId>,
    ) -> (ProofId, ProofId) {
        match not_bound {
            None => (
                Self::add_triple_lemma(
                    proof,
                    not_eq_then,
                    not_orig,
                    plan.lifted_then,
                    plan.then_coeffs.clone(),
                ),
                Self::add_triple_lemma(
                    proof,
                    not_eq_else,
                    not_orig,
                    plan.lifted_else,
                    plan.else_coeffs.clone(),
                ),
            ),
            Some(bound) => (
                Self::add_quad_lemma(
                    proof,
                    not_eq_then,
                    not_orig,
                    bound,
                    plan.lifted_then,
                    plan.then_coeffs.clone(),
                ),
                Self::add_quad_lemma(
                    proof,
                    not_eq_else,
                    not_orig,
                    bound,
                    plan.lifted_else,
                    plan.else_coeffs.clone(),
                ),
            ),
        }
    }

    /// Whether `(cl (not eq) (not p) (not q) concl)` is a valid
    /// `[1, 1, 1, 1]` `la_generic` lemma per the independent Farkas checker
    /// (the equality `eq` and atoms `p`, `q` asserted true, `concl` asserted
    /// false).
    pub(super) fn quad_lemma_valid(&self, eq: TermId, p: TermId, q: TermId, concl: TermId) -> bool {
        self.quad_lemma_valid_with(eq, p, q, concl, &FarkasAnnotation::from_ints(&[1, 1, 1, 1]))
    }

    /// [`Self::quad_lemma_valid`] against EXPLICIT Farkas coefficients.
    pub(in crate::executor::proof_repair) fn quad_lemma_valid_with(
        &self,
        eq: TermId,
        p: TermId,
        q: TermId,
        concl: TermId,
        farkas: &FarkasAnnotation,
    ) -> bool {
        let lits: Vec<TheoryLit> = [eq, p, q]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(l, true),
            })
            .chain(std::iter::once(match self.ctx.terms.get(concl) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(concl, false),
            }))
            .collect();
        // `_linear`, NOT `_full` (see `triple_lemma_valid`).
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &lits,
            farkas,
        )
        .is_ok()
    }

    /// Emit a `la_generic` theory lemma `(cl a b c d)` carrying `farkas`.
    /// Only called for quads already validated by [`Self::quad_lemma_valid`]
    /// / [`Self::quad_lemma_valid_with`] against THESE coefficients.
    fn add_quad_lemma(
        new_proof: &mut Proof,
        a: TermId,
        b: TermId,
        c: TermId,
        d: TermId,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b, c, d],
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Whether `(cl a b)` is a valid `[1, 1]` `la_generic` lemma per the
    /// independent Farkas checker (Int strengthening included).
    /// NORMALIZED-ASSUME MISMATCH fallback (the CAV09 QF_LIA class):
    /// [`Self::surface_bound_raw_term`] handles only pure orientation flips;
    /// here the canonical export REWROTE the linear atom itself — unary-minus
    /// spelling for `(* (- 1) x)`, elided `(* 1 x)` monomials, dropped
    /// `(* 0 x)` monomials, duplicate monomials folded into `(* x k)`,
    /// reordered sums, singleton-sum collapse. The surface comparison is
    /// re-interned PRINT-FAITHFULLY (so the `assume` spells exactly like the
    /// problem file) and bridged to the canonical literal with a certified
    /// `[1, 1]` `la_generic` orientation lemma: a raw linear atom and its
    /// canonicalization are mutually implying linear facts.
    ///
    /// Fail-closed (`None`) unless (a) the surface elaborates to EXACTLY the
    /// canonical literal (alignment gate) and (b) the independent Farkas
    /// checker certifies the bridge lemma up front.
    fn surface_linear_raw_term(
        &mut self,
        surf: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        if !surface_source_is_bounded(surf) {
            return None;
        }
        let stripped = strip_frontend_annotations(surf);
        let (inner, negated) = match stripped {
            FrontendTerm::App(op, operands) if op == "not" && operands.len() == 1 => {
                (strip_frontend_annotations(&operands[0]), true)
            }
            _ => (stripped, false),
        };
        let FrontendTerm::App(head, operands) = inner else {
            return None;
        };
        if operands.len() != 2 || !matches!(head.as_str(), "<=" | "<" | ">=" | ">") {
            return None;
        }
        // Alignment gate: same atom, different spelling — nothing else.
        if self.ctx.elaborate_surface_subterm(stripped)? != canonical {
            return None;
        }
        let a = self.raw_intern_surface(&operands[0])?;
        let b = self.raw_intern_surface(&operands[1])?;
        let raw_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(head.as_str()), [a, b], Sort::Bool);
        let raw = if negated {
            self.ctx.terms.mk_not_raw(raw_atom)
        } else {
            raw_atom
        };
        if raw == canonical {
            return Some((raw, None));
        }
        let raw_complement = complement_of(&mut self.ctx.terms, raw);
        if !self.pair_lemma_valid(canonical, raw_complement) {
            return None;
        }
        Some((raw, Some(raw_atom)))
    }

    /// [`Self::surface_bound_raw_term`] with the normalized-linear-atom
    /// fallback ([`Self::surface_linear_raw_term`]).
    pub(super) fn surface_bound_or_linear_raw_term(
        &mut self,
        surf: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        match self.surface_bound_raw_term(surf, canonical) {
            Some((raw, None)) if raw == canonical => {
                // The ELABORATED operands reproduced the canonical term, but
                // that alone does not prove the assume would print like the
                // problem file: elaboration may have canonicalized the linear
                // operands (the CAV09 class). Only a print-faithful re-intern
                // decides; when it differs, take the certified bridge.
                if let Some(hit) = self.surface_linear_raw_term(surf, canonical) {
                    return Some(hit);
                }
                Some((raw, None))
            }
            Some(hit) => Some(hit),
            None => self.surface_linear_raw_term(surf, canonical),
        }
    }

    pub(super) fn pair_lemma_valid(&self, a: TermId, b: TermId) -> bool {
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);
        let lits: Vec<TheoryLit> = [a, b]
            .iter()
            .map(|&l| match self.ctx.terms.get(l) {
                TermData::Not(inner) => TheoryLit::new(*inner, true),
                _ => TheoryLit::new(l, false),
            })
            .collect();
        ay_core::proof_validation::verify_farkas_conflict_lits_full(&self.ctx.terms, &lits, &farkas)
            .is_ok()
    }

    /// Emit a `[1, 1]` `la_generic` theory lemma `(cl a b)`. Only called for
    /// pairs already validated by [`Self::pair_lemma_valid`].
    pub(super) fn add_pair_lemma(new_proof: &mut Proof, a: TermId, b: TermId) -> ProofId {
        new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![a, b],
            farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Certified orientation bridge for a top-level binary-equality flip
    /// `r` → `c` (#C2b): emits `(cl (= x y)) :rule eq_symmetric` composed
    /// with `equiv_pos1`/`equiv_pos2` and one resolution into the clause
    /// `(cl (not r) c)` (positive literals) / `(cl e' c)` with `r = (not e)`,
    /// `c = (not e')` (negated literals — the clause the caller resolves on
    /// pivot `e`). Returns `(outer resolution pivot, bridge step)`. Callers
    /// guarantee the top-level equality-flip shape.
    pub(super) fn add_eq_flip_bridge(
        &mut self,
        new_proof: &mut Proof,
        r: TermId,
        c: TermId,
    ) -> (TermId, ProofId) {
        // (x, y): derive (cl (not x) y); pivot: the literal the OUTER
        // resolution eliminates from the caller's working clause.
        let (x, y, pivot) = match (self.ctx.terms.get(r), self.ctx.terms.get(c)) {
            (TermData::Not(e), TermData::Not(e_flip)) => {
                let (e, e_flip) = (*e, *e_flip);
                (e_flip, e, e)
            }
            _ => (r, c, r),
        };
        let equiv = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let sym =
            new_proof.add_rule_step(AletheRule::EqSymmetric, vec![equiv], Vec::new(), Vec::new());
        let not_equiv = self.ctx.terms.mk_not_raw(equiv);
        let not_x = self.ctx.terms.mk_not_raw(x);
        // The `=` intern may have reoriented the equivalence itself: pick the
        // equiv_pos side whose conclusion is (cl (not x) y) either way.
        let interned_straight = matches!(
            self.ctx.terms.get(equiv),
            TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2 && args[0] == x
        );
        let ep = if interned_straight {
            new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_x, y],
                Vec::new(),
                Vec::new(),
            )
        } else {
            new_proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equiv, y, not_x],
                Vec::new(),
                Vec::new(),
            )
        };
        let bridge = new_proof.add_resolution(vec![not_x, y], equiv, ep, sym);
        (pivot, bridge)
    }
}
