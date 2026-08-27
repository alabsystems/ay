// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive an `EqDiffVar` atom fold from the DEFINITION that licensed it.
//!
//! # The gap this closes
//!
//! `EqDiffVar` (`preprocess/eq_diffvar`) mints a fresh `d`, asserts the pair
//! `(<= d lin)` / `(<= lin d)`, and rewrites every occurrence of a
//! multi-variable equality atom `P` to the var-CONST atom `Q = (= d rhs)`.
//! `#eq-diffvar-uncertifiable` made the PAIR checkable — each bound is now an
//! `AletheRule::FreshDefBound` step the strict checker re-validates through
//! `ay_proof`'s `FreshDefRegistry`. The REWRITE stayed uncertified: the
//! rewritten assertion is not authored, so `demote_non_problem_assumptions`
//! stamps it a premiseless `trust`. `Executor::eq_diffvar_pass_enabled`'s own
//! RESIDUAL GAP note names the repair — derive the rewritten clause from the
//! AUTHORED clause plus the definition — and this module is that derivation.
//!
//! # What is derived, and why an EQUIVALENCE rather than an implication
//!
//! The bridge concludes `(cl (= P Q))`, a term-level equivalence, because the
//! replay lifts it through arbitrary context with `cong`: the folded atoms of
//! `dillig12_m` sit under `not`, inside `ite` BRANCHES, and inside `and`s
//! nested in a 4-ary `or`. A one-directional implication is only sound in
//! positive polarity, and deciding polarity per occurrence would be a second
//! analysis to get right; the equivalence needs none.
//!
//! # The derivation
//!
//! With `BL := (<= d lin)`, `BG := (<= lin d)` and `E := (= P Q)`:
//!
//! ```text
//! BL, BG                                      :rule fresh_def_bound :args (d)
//! (cl ¬BL ¬BG ¬P (<= q1 q2))                  :rule lia_generic  [Farkas]
//! (cl ¬BL ¬BG ¬P (<= q2 q1))                  :rule lia_generic  [Farkas]
//! (cl ¬P (<= q1 q2)), (cl ¬P (<= q2 q1))      resolve the bounds away
//! (cl ¬(<= q1 q2) ¬(<= q2 q1) Q)              :rule la_disequality
//! (cl Q ¬P)                                   resolve            [P ⟹ Q]
//! …the same four steps with P and Q swapped   [Q ⟹ P]
//! (cl E P Q), (cl E ¬P ¬Q)                    :rule equiv_neg2 / equiv_neg1
//! (cl E)                                      three resolutions
//! ```
//!
//! # Soundness
//!
//! Nothing here is taken on the producer's word, and no checker rule is added
//! or widened.
//!
//! * The two bound steps are `fresh_def_bound`, whose whole-proof conditions
//!   (FRESH, INDEPENDENT, SORT, SINGLE DEFINIENS) the strict checker re-runs
//!   from scratch. This module additionally runs the checker's own
//!   `recognize_fresh_def_bound` on the exact step it is about to emit.
//! * The four arithmetic lemmas are ordinary Farkas conflict lemmas. Their
//!   coefficients are not asserted by this module: they are RECONSTRUCTED by a
//!   fresh `ay_lra::LraSolver` over the clause's own negation and then
//!   re-validated against the exact target clause by
//!   `ay_core::proof_validation::verify_farkas_conflict_lits_full`
//!   (`try_lra_farkas_reconstruction` does both). A clause that is not a
//!   rational consequence of the two bounds therefore DECLINES here, which is
//!   exactly what happens when a later pass rewrote `lin` and the recorded
//!   definition no longer describes the definition the proof carries.
//! * The two triangles are `la_disequality`, checked here by the checker's own
//!   `recognize_arith_eq_triangle` before emission.
//! * Everything else is propositional: `equiv_neg1`, `equiv_neg2` and
//!   resolution.
//!
//! Why the equivalence is TRUE, stated once: `EqDiffVar` folds `P` only when
//! `P`'s canonical integer row is `lin = rhs`, i.e. `lhs(P) - rhs(P)` and
//! `lin - rhs` are the same linear form up to a nonzero rational factor `μ`.
//! Under `d = lin` both `P ⟹ Q` and `Q ⟹ P` are then rational consequences,
//! which is precisely what the Farkas reconstruction re-derives. This module
//! never computes `μ`; it lets the solver find the combination and the
//! validator re-check it.
//!
//! # Fail-closed
//!
//! Every guard returns `None`, which fails the enclosing plan and leaves the
//! assertion with today's demotion. The lane can only ever leave a proof as
//! certifiable as it found it.

use ay_core::proof_validation::recognize_fresh_def_bound;

use super::*;

/// One `EqDiffVar` atom fold, resolved against the definitions the finished
/// proof already carries (#4751).
///
/// `definiens` is the `lin` the PASS minted, which is the spelling the folded
/// atom is equivalent under. A later pass may have rewritten the definitional
/// bound itself, and the proof then carries `(<= d lin')`; that bound is
/// DERIVED from this one through the ordinary record bridge (see
/// `plan_derive_clause`'s base case) rather than binding `d` a second time,
/// because two definientia for one symbol are an EQUATION between them and
/// `FreshDefRegistry` rejects a proof carrying both.
#[derive(Clone, Copy)]
pub(crate) struct EqDiffVarAtomPlan {
    pub(super) replacement: TermId,
    pub(super) definiendum: TermId,
    pub(super) definiens: TermId,
    pub(super) stamp: u32,
}

/// Node budget for one atom's equivalence: 2 bound steps, 4 Farkas lemmas,
/// 2 triangles, 12 resolutions and 3 assembly steps, rounded up.
const EQ_DIFFVAR_BRIDGE_NODES: usize = 32;

impl PropagationChainPlanner<'_> {
    /// `(cl (= atom replacement))` for one recorded `EqDiffVar` fold.
    pub(super) fn plan_eq_diffvar_atom_equivalence(
        &mut self,
        cx: &mut PlanCx<'_>,
        atom: TermId,
        plan: EqDiffVarAtomPlan,
    ) -> Option<EqRes> {
        let replacement = plan.replacement;
        if atom == replacement
            || self.arith_equality_operands(atom).is_none()
            || self.arith_equality_operands(replacement).is_none()
        {
            return None;
        }
        cx.spend(EQ_DIFFVAR_BRIDGE_NODES)?;
        let bounds = self.plan_definitional_bounds(cx, plan.definiendum, plan.definiens)?;
        let forward = self.plan_eq_diffvar_implication(cx, atom, replacement, &bounds)?;
        let backward = self.plan_eq_diffvar_implication(cx, replacement, atom, &bounds)?;
        let (equivalence, id) =
            self.plan_equivalence_from_implications(cx, atom, replacement, forward, backward)?;
        Some(EqRes::Changed {
            to: replacement,
            eq_term: equivalence,
            id,
        })
    }

    /// `(cl target (not source))` for two equality atoms related by the
    /// definition the `bounds` carry.
    ///
    /// Both bounds are offered to BOTH lemmas deliberately: which one a
    /// direction actually needs depends on the sign of the normalizing factor
    /// between the two rows, and the reconstruction assigns weight zero to the
    /// one it does not use (`farkas.rs`: "Zero-weight literal: contributes
    /// nothing to the combination"). Resolving an unused bound away is free
    /// and keeps this function free of a sign analysis that would have to be
    /// right.
    fn plan_eq_diffvar_implication(
        &mut self,
        cx: &mut PlanCx<'_>,
        source: TermId,
        target: TermId,
        bounds: &[(TermId, ProofId); 2],
    ) -> Option<ProofId> {
        let (left, right) = self.arith_equality_operands(target)?;
        let forward = self.raw_le(left, right)?;
        let reverse = self.raw_le(right, left)?;
        let not_source = self.terms.mk_not_raw(source);
        let mut discharged = Vec::with_capacity(2);
        for bound in [forward, reverse] {
            let mut clause = Vec::with_capacity(4);
            for &(atom, _) in bounds {
                clause.push(self.terms.mk_not_raw(atom));
            }
            clause.push(not_source);
            clause.push(bound);
            let (farkas, kind) = self.plan_farkas_certificate(&clause)?;
            let mut current = cx.chain.add_theory_lemma_with_farkas_and_kind_opt(
                "LIA",
                clause.clone(),
                Some(farkas),
                kind,
            );
            // Resolve the two definitional bounds away, leaving
            // `(cl (not source) bound)`.
            for &(_, bound_id) in bounds {
                // Drop the bound literal this resolution discharges; the two
                // negated bounds were pushed first, in `bounds` order.
                let _discharged = clause.remove(0);
                current = cx.chain.add_rule_step(
                    AletheRule::ThResolution,
                    clause.clone(),
                    vec![current, bound_id],
                    Vec::new(),
                );
            }
            discharged.push(current);
        }
        let not_forward = self.terms.mk_not_raw(forward);
        let not_reverse = self.terms.mk_not_raw(reverse);
        let triangle = vec![not_forward, not_reverse, target];
        if !ay_proof::recognize_arith_eq_triangle(self.terms, &triangle) {
            return None;
        }
        let triangle_id = cx.chain.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_owned(),
            clause: triangle,
            farkas: None,
            kind: TheoryLemmaKind::ArithEqTriangle,
            lia: None,
        });
        let after_forward = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![not_reverse, target, not_source],
            vec![triangle_id, discharged[0]],
            Vec::new(),
        );
        Some(cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![target, not_source],
            vec![after_forward, discharged[1]],
            Vec::new(),
        ))
    }

    /// A validated Farkas certificate for one implication clause.
    ///
    /// The certificate is never asserted by this module. Two routes produce a
    /// candidate and BOTH end at the checker's own
    /// `verify_farkas_conflict_lits_full`, which is the same call the strict
    /// `lra_farkas` validator makes, so a certificate accepted here is accepted
    /// there and one rejected here would have been rejected there:
    ///
    /// 1. three fixed unit vectors, tried first. These clauses have a rigid
    ///    shape — two definitional bounds, a negated equality atom and a bound
    ///    atom — and the combination that refutes them uses one bound, the
    ///    equality and the target with weight 1 and the other bound with weight
    ///    0. Which bound is the unused one depends on the sign of the factor
    ///    relating the two linear forms, hence three candidates rather than one.
    /// 2. `try_lra_farkas_reconstruction`, a fresh `ay_lra::LraSolver` over the
    ///    clause's negation, for every scaling the unit vectors do not cover.
    ///
    /// Route 1 exists purely for cost: route 2 builds and runs a simplex solver
    /// per clause, four times per folded atom, on a lane that runs on every
    /// proof rewrite. Deleting route 1 changes no verdict — route 2 accepts a
    /// superset — only latency.
    fn plan_farkas_certificate(
        &self,
        clause: &[TermId],
    ) -> Option<(ay_core::FarkasAnnotation, TheoryLemmaKind)> {
        let conflict: Vec<ay_core::TheoryLit> = clause
            .iter()
            .map(|&literal| match self.terms.get(literal) {
                TermData::Not(inner) => ay_core::TheoryLit::new(*inner, true),
                _ => ay_core::TheoryLit::new(literal, false),
            })
            .collect();
        for candidate in [[1, 1, 1, 1], [1, 0, 1, 1], [0, 1, 1, 1]] {
            if candidate.len() != clause.len() {
                break;
            }
            let farkas = ay_core::FarkasAnnotation::from_ints(&candidate);
            if ay_core::proof_validation::verify_farkas_conflict_lits_full(
                self.terms, &conflict, &farkas,
            )
            .is_ok()
            {
                return Some((farkas, TheoryLemmaKind::LraFarkas));
            }
        }
        let mut farkas = None;
        let mut kind = TheoryLemmaKind::Generic;
        super::super::proof_farkas::try_lra_farkas_reconstruction(
            self.terms,
            clause,
            &mut farkas,
            &mut kind,
        )
        .then(|| farkas.map(|farkas| (farkas, kind)))
        .flatten()
    }

    /// The two `fresh_def_bound` steps for `definiendum := definiens`, memoized
    /// on the bound atom so one plan emits each at most once.
    fn plan_definitional_bounds(
        &mut self,
        cx: &mut PlanCx<'_>,
        definiendum: TermId,
        definiens: TermId,
    ) -> Option<[(TermId, ProofId); 2]> {
        let upper = self.raw_le(definiendum, definiens)?;
        let lower = self.raw_le(definiens, definiendum)?;
        let upper_id = self.plan_fresh_def_bound(cx, upper, definiendum)?;
        let lower_id = self.plan_fresh_def_bound(cx, lower, definiendum)?;
        Some([(upper, upper_id), (lower, lower_id)])
    }

    /// One `fresh_def_bound` step, admitted only by the CHECKER's own
    /// recognizer run on the exact step about to be emitted.
    pub(super) fn plan_fresh_def_bound(
        &mut self,
        cx: &mut PlanCx<'_>,
        atom: TermId,
        definiendum: TermId,
    ) -> Option<ProofId> {
        if let Some(&memoized) = cx.clause_memo.get(&atom) {
            return Some(memoized);
        }
        let clause = vec![atom];
        let args = vec![definiendum];
        recognize_fresh_def_bound(self.terms, &clause, 0, &args).ok()?;
        let id = cx
            .chain
            .add_rule_step(AletheRule::FreshDefBound, clause, Vec::new(), args);
        cx.clause_memo.insert(atom, id);
        Some(id)
    }

    /// `(<= left right)` as the RAW binary application the `la_disequality`
    /// and Farkas validators read positionally. `mk_le` would constant-fold
    /// and apply `to_real` rewrites, either of which changes the operands the
    /// triangle rule demands, so the node is built directly and re-read.
    fn raw_le(&mut self, left: TermId, right: TermId) -> Option<TermId> {
        let atom = self
            .terms
            .mk_app(Symbol::named("<="), [left, right], Sort::Bool);
        match self.terms.get(atom) {
            TermData::App(symbol, args)
                if symbol.name() == "<=" && args.as_slice() == [left, right] =>
            {
                Some(atom)
            }
            _ => None,
        }
    }

    /// The operands of a binary equality over a shared `Int`/`Real` sort — the
    /// exact precondition `validate_arith_eq_triangle` enforces.
    fn arith_equality_operands(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(symbol, args) = self.terms.get(term) else {
            return None;
        };
        if symbol.name() != "=" || args.len() != 2 {
            return None;
        }
        let (left, right) = (args[0], args[1]);
        let sort = self.terms.sort(left);
        (sort == self.terms.sort(right) && matches!(sort, Sort::Int | Sort::Real))
            .then_some((left, right))
    }
}
