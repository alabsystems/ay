// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Provenance-authenticated repair of formula-level arithmetic ITE leaves.
//!
//! Rebuilds substitution-derived ITE leaves from exact preprocessing sources,
//! checked ITE rules, and independently replayed Farkas implications.

use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, Sort, Symbol, TermId, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_farkas_validation::blocking_clause_to_conflict;
use super::proof_surface_syntax::strip_frontend_annotations;
use super::proof_trust_surgery_provenance::{
    branch_resolution_shape_unambiguous, complement_of, retained_original_rows_are_signable,
    source_set_is_exactly_authored, surface_arithmetic_ite_matches, surface_source_is_bounded,
    OriginalSourceIndex, SurgeryPlanningBudget,
};
use super::Executor;

/// A provenance-authenticated formula-level ITE consequence whose branch
/// implications are independently synthesized and replayed as Farkas proofs.
pub(super) struct ProvenanceItePlan {
    pub(super) orig: TermId,
    pub(super) defining_source: Option<TermId>,
    pub(super) cond: TermId,
    pub(super) source_then: TermId,
    pub(super) source_else: TermId,
    pub(super) lifted_then: TermId,
    pub(super) lifted_else: TermId,
    pub(super) goal: TermId,
    pub(super) supports: Vec<TermId>,
    pub(super) source: ProvenanceIteSource,
    pub(super) then_lemma: ProvenanceFarkasLemma,
    pub(super) else_lemma: ProvenanceFarkasLemma,
}

pub(super) enum ProvenanceIteSource {
    /// The authored premise itself is a formula-level ITE.
    Formula,
    /// The authored surface is `(= d (ite c u v))`; derive the formula-level
    /// branch equalities with the existing checked `ite_intro` bridge.
    Defined {
        ite_term: TermId,
        ite_def: TermId,
        and_term: TermId,
        intro_eq: TermId,
    },
}

pub(super) struct ProvenanceFarkasLemma {
    pub(super) clause: Vec<TermId>,
    pub(super) farkas: FarkasAnnotation,
    /// Exact authored supports whose non-zero certificate rows remain in this
    /// branch lemma. Zero rows are removed before export.
    pub(super) supports: Vec<TermId>,
}

impl Executor {
    /// Recognize a formula-level arithmetic ITE consequence using only the
    /// exact, unique preprocessing source set recorded for this goal.
    pub(super) fn plan_provenance_ite_lift(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<ProvenanceItePlan> {
        if clause.len() != 1 {
            return None;
        }
        let goal = clause[0];
        let TermData::Ite(cond, lifted_then, lifted_else) = *self.ctx.terms.get(goal) else {
            return None;
        };

        // No provenance delegates to the legacy syntactic planner. Two source
        // sets are ambiguous: this planner cannot know which derivation
        // produced the trust leaf and therefore fails closed.
        let source_sets = self
            .proof_problem_assertion_provenance
            .as_ref()?
            .assertion_sources
            .get(&goal)?;
        let [source_set] = source_sets.as_slice() else {
            return None;
        };
        // Every source must be one exact re-elaborated authored original, with
        // no duplicate canonical entry that could choose another surface form.
        if !source_set_is_exactly_authored(source_set, source_index) {
            return None;
        }
        let source_set = source_set.clone();
        let mut candidates = Vec::new();
        for &orig in &source_set {
            let (_, parsed) = source_index.get(originals, orig)?;
            if !planning.spend_surface(orig, parsed) {
                return None;
            }
            let TermData::Ite(source_cond, source_then, source_else) =
                self.ctx.terms.get(orig).clone()
            else {
                continue;
            };
            if source_cond != cond
                || *self.ctx.terms.sort(orig) != Sort::Bool
                || *self.ctx.terms.sort(source_then) != Sort::Bool
                || *self.ctx.terms.sort(source_else) != Sort::Bool
            {
                continue;
            }
            if !surface_arithmetic_ite_matches(
                &mut self.ctx,
                parsed,
                &[source_cond, source_then, source_else],
            ) {
                // `mk_ite` can swap branches under a negated condition. The
                // authored override must have the same immediate order as the
                // canonical ITE consumed by ite1/ite2.
                continue;
            }
            let supports: Vec<TermId> = source_set
                .iter()
                .copied()
                .filter(|&source| source != orig)
                .collect();
            let mut then_rows = vec![source_then];
            then_rows.extend(supports.iter().copied());
            then_rows.push(lifted_then);
            if !planning.spend_farkas_attempt(&self.ctx.terms, &then_rows) {
                return None;
            }
            let Some(then_lemma) =
                self.plan_provenance_farkas_implication(source_then, &supports, lifted_then)
            else {
                continue;
            };
            let mut else_rows = vec![source_else];
            else_rows.extend(supports.iter().copied());
            else_rows.push(lifted_else);
            if !planning.spend_farkas_attempt(&self.ctx.terms, &else_rows) {
                return None;
            }
            let Some(else_lemma) =
                self.plan_provenance_farkas_implication(source_else, &supports, lifted_else)
            else {
                continue;
            };
            if !retained_original_rows_are_signable(
                &mut self.ctx,
                &then_lemma.supports,
                originals,
                source_index,
                planning,
            ) || !retained_original_rows_are_signable(
                &mut self.ctx,
                &else_lemma.supports,
                originals,
                source_index,
                planning,
            ) {
                continue;
            }
            let not_cond = self.ctx.terms.mk_not_raw(cond);
            if !branch_resolution_shape_unambiguous(
                &mut self.ctx.terms,
                goal,
                not_cond,
                source_then,
                lifted_then,
                &then_lemma.clause,
            ) || !branch_resolution_shape_unambiguous(
                &mut self.ctx.terms,
                goal,
                cond,
                source_else,
                lifted_else,
                &else_lemma.clause,
            ) {
                continue;
            }
            candidates.push(ProvenanceItePlan {
                orig,
                defining_source: None,
                cond,
                source_then,
                source_else,
                lifted_then,
                lifted_else,
                goal,
                supports,
                source: ProvenanceIteSource::Formula,
                then_lemma,
                else_lemma,
            });
        }

        // Surface `(= d (ite c u v))` elaborates to the same formula-level
        // ITE, but its Assume must print as the authored equality. Re-intern
        // that exact raw equality and derive its branch facts through
        // `ite_intro`, while still taking every additional premise solely from
        // the exact provenance source set.
        for &canonical in &source_set {
            let (_, parsed) = source_index.get(originals, canonical)?;
            if !planning.spend_surface(canonical, parsed) {
                return None;
            }
            if !surface_source_is_bounded(parsed) {
                continue;
            }
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(op, sides) = stripped else {
                continue;
            };
            if op != "=" || sides.len() != 2 {
                continue;
            }
            for ite_side in [0usize, 1] {
                let ite_surface = strip_frontend_annotations(&sides[ite_side]);
                let def_surface = strip_frontend_annotations(&sides[1 - ite_side]);
                let FrontendTerm::App(ite_op, ite_args) = ite_surface else {
                    continue;
                };
                if ite_op != "ite" || ite_args.len() != 3 {
                    continue;
                }
                let (Some(source_cond), Some(u), Some(v), Some(defined)) = (
                    self.ctx.elaborate_surface_subterm(&ite_args[0]),
                    self.ctx.elaborate_surface_subterm(&ite_args[1]),
                    self.ctx.elaborate_surface_subterm(&ite_args[2]),
                    self.ctx.elaborate_surface_subterm(def_surface),
                ) else {
                    continue;
                };
                if source_cond != cond {
                    continue;
                }
                let ite_term = self.ctx.terms.mk_ite(cond, u, v);
                if *self.ctx.terms.sort(ite_term) == Sort::Bool
                    || !matches!(
                        self.ctx.terms.get(ite_term),
                        TermData::Ite(c, a, b) if *c == cond && *a == u && *b == v
                    )
                {
                    continue;
                }
                let ordered = if ite_side == 0 {
                    [ite_term, defined]
                } else {
                    [defined, ite_term]
                };
                let p_raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), ordered, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(p_raw),
                    TermData::App(Symbol::Named(eq_op), args)
                        if eq_op == "=" && args.as_slice() == ordered
                ) || self.raw_intern_surface(stripped) != Some(p_raw)
                {
                    continue;
                }
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.build_ite_lift_connectives(p_raw, cond, ite_term, u, v)
                else {
                    continue;
                };
                let supports: Vec<TermId> = source_set
                    .iter()
                    .copied()
                    .filter(|&source| source != canonical)
                    .collect();
                let lemma_supports: Vec<TermId> = std::iter::once(p_raw)
                    .chain(supports.iter().copied())
                    .collect();
                let mut then_rows = vec![eq_then];
                then_rows.extend(lemma_supports.iter().copied());
                then_rows.push(lifted_then);
                if !planning.spend_farkas_attempt(&self.ctx.terms, &then_rows) {
                    return None;
                }
                let Some(then_lemma) =
                    self.plan_provenance_farkas_implication(eq_then, &lemma_supports, lifted_then)
                else {
                    continue;
                };
                let mut else_rows = vec![eq_else];
                else_rows.extend(lemma_supports.iter().copied());
                else_rows.push(lifted_else);
                if !planning.spend_farkas_attempt(&self.ctx.terms, &else_rows) {
                    return None;
                }
                let Some(else_lemma) =
                    self.plan_provenance_farkas_implication(eq_else, &lemma_supports, lifted_else)
                else {
                    continue;
                };
                if !retained_original_rows_are_signable(
                    &mut self.ctx,
                    &then_lemma.supports,
                    originals,
                    source_index,
                    planning,
                ) || !retained_original_rows_are_signable(
                    &mut self.ctx,
                    &else_lemma.supports,
                    originals,
                    source_index,
                    planning,
                ) {
                    continue;
                }
                let not_cond = self.ctx.terms.mk_not_raw(cond);
                if !branch_resolution_shape_unambiguous(
                    &mut self.ctx.terms,
                    goal,
                    not_cond,
                    eq_then,
                    lifted_then,
                    &then_lemma.clause,
                ) || !branch_resolution_shape_unambiguous(
                    &mut self.ctx.terms,
                    goal,
                    cond,
                    eq_else,
                    lifted_else,
                    &else_lemma.clause,
                ) {
                    continue;
                }
                candidates.push(ProvenanceItePlan {
                    orig: p_raw,
                    defining_source: Some(canonical),
                    cond,
                    source_then: eq_then,
                    source_else: eq_else,
                    lifted_then,
                    lifted_else,
                    goal,
                    supports,
                    source: ProvenanceIteSource::Defined {
                        ite_term,
                        ite_def,
                        and_term,
                        intro_eq,
                    },
                    then_lemma,
                    else_lemma,
                });
            }
        }
        let mut candidates = candidates.into_iter();
        let plan = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        Some(plan)
    }

    /// Synthesize and independently replay the exact linear implication
    /// `source ∧ supports => conclusion` as a blocking clause.
    pub(super) fn plan_provenance_farkas_implication(
        &mut self,
        source: TermId,
        supports: &[TermId],
        conclusion: TermId,
    ) -> Option<ProvenanceFarkasLemma> {
        self.plan_provenance_farkas(source, supports, Some(conclusion))
    }

    /// Synthesize and replay `source ∧ supports => false` as a minimal
    /// blocking clause. Used by the provenance-OR sibling after decomposing an
    /// authored disjunction into arithmetic cases.
    pub(super) fn plan_provenance_farkas_conflict(
        &mut self,
        source: TermId,
        supports: &[TermId],
    ) -> Option<ProvenanceFarkasLemma> {
        self.plan_provenance_farkas(source, supports, None)
    }

    fn plan_provenance_farkas(
        &mut self,
        source: TermId,
        supports: &[TermId],
        conclusion: Option<TermId>,
    ) -> Option<ProvenanceFarkasLemma> {
        let mut antecedents = Vec::with_capacity(supports.len() + 1);
        antecedents.push(source);
        antecedents.extend_from_slice(supports);
        let mut unique = antecedents.clone();
        unique.sort_unstable();
        unique.dedup();
        if unique.len() != antecedents.len() {
            return None;
        }

        let mut clause: Vec<TermId> = antecedents
            .iter()
            .map(|&term| complement_of(&mut self.ctx.terms, term))
            .collect();
        if let Some(conclusion) = conclusion {
            clause.push(conclusion);
        }

        let mut farkas = None;
        let mut kind = TheoryLemmaKind::Generic;
        if !super::proof_farkas::try_lra_farkas_reconstruction(
            &self.ctx.terms,
            &clause,
            &mut farkas,
            &mut kind,
        ) {
            return None;
        }
        let farkas = farkas?;
        if farkas.coefficients.len() != clause.len() {
            return None;
        }

        // Solver conflicts may retain irrelevant assertions as zero rows.
        // Remove them before export: external `la_generic` checkers require
        // every printed hypothesis to be arithmetic, even when its weight is
        // zero. The source and conclusion are structural resolution pivots,
        // so a plan that does not genuinely use either one fails closed.
        let zero = num_rational::Rational64::from(0);
        if farkas.coefficients.first()? == &zero
            || conclusion.is_some() && farkas.coefficients.last()? == &zero
        {
            return None;
        }
        let conclusion_index = conclusion.map(|_| clause.len().saturating_sub(1));
        let mut pruned_clause = Vec::with_capacity(clause.len());
        let mut pruned_coefficients = Vec::with_capacity(clause.len());
        let mut retained_supports = Vec::new();
        for (index, (&literal, &coefficient)) in
            clause.iter().zip(farkas.coefficients.iter()).enumerate()
        {
            if coefficient == zero {
                continue;
            }
            pruned_clause.push(literal);
            pruned_coefficients.push(coefficient);
            if index > 0 && Some(index) != conclusion_index {
                retained_supports.push(antecedents[index]);
            }
        }
        clause = pruned_clause;
        let farkas = FarkasAnnotation::new(pruned_coefficients);
        let conflict = blocking_clause_to_conflict(&self.ctx.terms, &clause);
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
            || ay_core::proof_validation::resolve_equality_coefficient_signs(
                &self.ctx.terms,
                &conflict,
                &farkas,
            )
            .is_none()
        {
            return None;
        }
        Some(ProvenanceFarkasLemma {
            clause,
            farkas,
            supports: retained_supports,
        })
    }
}
