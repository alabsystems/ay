// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic Alethe assumption prologue construction.

use super::super::*;
use super::model::{RebuildState, SurgeryInput, SurgeryPlans};

impl Executor {
    pub(super) fn build_assumption_prologue(
        &mut self,
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
    ) -> RebuildState {
        let mut state = RebuildState::new(input.step_count());
        Self::hoist_live_assumes(input, plans, &mut state);
        Self::index_hoisted_originals(input, &mut state);
        Self::hoist_surface_plan_sources(plans, &mut state);
        Self::hoist_substituted_equality_sources(plans, &mut state);
        Self::hoist_quantifier_sources(plans, &mut state);
        state
    }

    fn hoist_live_assumes(
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
        state: &mut RebuildState,
    ) {
        for (index, step) in input.proof.steps.iter().enumerate() {
            if !input.live[index] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            // Tautology/EUF-planned assumes are derived during the walk.
            if plans.taut_units.contains_key(&index) || plans.euf_lemmas.contains_key(&index) {
                continue;
            }
            let term = match plans.assume_plans.get(&index) {
                Some(AssumePlan::Distinct { raw, .. }) => *raw,
                Some(AssumePlan::AndBounds { raw_and, .. })
                | Some(AssumePlan::AndDistinct { raw_and, .. }) => *raw_and,
                Some(AssumePlan::Literal { raw, .. }) => *raw,
                Some(AssumePlan::QuantExpansion { forall_term, .. }) => *forall_term,
                None => plans
                    .quant_source_replacements
                    .get(term)
                    .copied()
                    .unwrap_or(*term),
            };
            let id = state.new_proof.add_assume(term, None);
            state.assume_new_id.insert(index, id);
            if !plans.assume_plans.contains_key(&index) {
                state.map[index] = Some(id);
            }
        }
    }

    fn index_hoisted_originals(input: &SurgeryInput<'_>, state: &mut RebuildState) {
        for (index, step) in input.proof.steps.iter().enumerate() {
            if !input.live[index] {
                continue;
            }
            if let ProofStep::Assume(term) = step {
                if let Some(&id) = state.assume_new_id.get(&index) {
                    state.lift_assume.entry(*term).or_insert(id);
                }
            }
        }
    }

    fn hoist_term(state: &mut RebuildState, term: TermId) {
        if !state.lift_assume.contains_key(&term) {
            let id = state.new_proof.add_assume(term, None);
            state.lift_assume.insert(term, id);
        }
    }

    fn hoist_surface_plan_sources(plans: &SurgeryPlans, state: &mut RebuildState) {
        for plan in plans.normalized_authored_ors.values() {
            Self::hoist_term(state, plan.source_or);
        }
        for plan in plans.authored_array_ites.values() {
            Self::hoist_term(state, plan.array_equality);
            Self::hoist_term(state, plan.guard_source);
        }
        for plan in plans.ite_lifts.values() {
            for term in std::iter::once(plan.orig).chain(plan.bound) {
                Self::hoist_term(state, term);
            }
        }
        for plan in plans.provenance_ite_lifts.values() {
            for term in std::iter::once(plan.orig).chain(plan.supports.iter().copied()) {
                Self::hoist_term(state, term);
            }
        }
        for &term in plans.exact_provenance_or_assumes.values() {
            Self::hoist_term(state, term);
        }
        for plan in plans.provenance_or_plans.values() {
            for &term in plan.authored_sources() {
                Self::hoist_term(state, term);
            }
        }
        for plan in plans.or_units.values() {
            for term in std::iter::once(plan.orig)
                .chain(plan.eliminations.iter().map(|&(_, complement)| complement))
            {
                Self::hoist_term(state, term);
            }
        }
    }

    /// Equality-collapse assumptions must precede every emitted step.
    fn hoist_substituted_equality_sources(plans: &SurgeryPlans, state: &mut RebuildState) {
        let mut subst_plans: Vec<&SubstEqPlan> = plans.subst_eqs.values().collect();
        subst_plans.sort_by_key(|plan| plan.lemma[0]);
        for plan in subst_plans {
            for &hypothesis in &plan.hyps {
                Self::hoist_term(state, hypothesis);
            }
        }
    }

    fn hoist_quantifier_sources(plans: &SurgeryPlans, state: &mut RebuildState) {
        for (index, plan) in &plans.assume_plans {
            if let AssumePlan::QuantExpansion { forall_term, .. } = plan {
                if let Some(&id) = state.assume_new_id.get(index) {
                    state.lift_assume.entry(*forall_term).or_insert(id);
                }
            }
        }
        for plan in plans.quant_consequences.values() {
            for term in std::iter::once(plan.forall_term).chain(plan.supports.iter().copied()) {
                Self::hoist_term(state, term);
            }
        }
        for plan in plans.quant_negations.values() {
            for &support in &plan.supports {
                Self::hoist_term(state, support);
            }
        }
    }
}
