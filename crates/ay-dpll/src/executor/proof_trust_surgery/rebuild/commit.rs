// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final authored-premise and rendering-state transaction commit.

use super::super::*;
use super::model::{RebuildState, SurfaceOverrides, SurgeryPlans};

impl Executor {
    pub(super) fn commit_trust_surgery(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        plans: &mut SurgeryPlans,
        state: RebuildState,
    ) -> bool {
        let authored_premises = Self::rebuilt_authored_premises(plans);
        let Ok(mut next_overrides) = self.select_next_surface_overrides(plans) else {
            return false;
        };
        if !self.repair_authored_array_overrides(originals, plans, &mut next_overrides)
            || !self.repair_authored_or_overrides(originals, plans, &mut next_overrides)
            || next_overrides.as_ref().is_some_and(|overrides| {
                !crate::executor::proof_surface_syntax::surface_override_map_is_bounded(overrides)
            })
        {
            return false;
        }
        let Some(authored_append) = prepare_rebuilt_premise_append(
            &mut self.last_proof_rebuild_originals,
            &authored_premises,
        ) else {
            return false;
        };
        *proof = state.new_proof;
        self.last_proof_term_overrides = next_overrides;
        self.last_proof_rebuild_originals.extend(authored_append);
        true
    }

    fn rebuilt_authored_premises(plans: &SurgeryPlans) -> Vec<TermId> {
        let mut premises: Vec<TermId> = plans
            .assume_plans
            .values()
            .filter_map(|plan| match plan {
                AssumePlan::Distinct { raw, .. } | AssumePlan::Literal { raw, .. } => Some(*raw),
                AssumePlan::AndBounds { raw_and, .. } | AssumePlan::AndDistinct { raw_and, .. } => {
                    Some(*raw_and)
                }
                AssumePlan::QuantExpansion { .. } => None,
            })
            .collect();
        premises.extend(
            plans
                .ite_lifts
                .values()
                .filter(|plan| plan.defining_source.is_some())
                .map(|plan| plan.orig),
        );
        premises.extend(
            plans
                .provenance_ite_lifts
                .values()
                .filter(|plan| plan.defining_source.is_some())
                .map(|plan| plan.orig),
        );
        premises.extend(plans.quant_negations.values().map(|plan| plan.forall_term));
        premises.extend(
            plans
                .authored_array_ites
                .values()
                .filter(|plan| plan.guard_source != plan.guard)
                .map(|plan| plan.guard_source),
        );
        premises
    }

    fn select_next_surface_overrides(
        &self,
        plans: &mut SurgeryPlans,
    ) -> Result<Option<SurfaceOverrides>, ()> {
        if plans.keeps_surface_overrides {
            plans.prepared_surface_overrides.take().map(Some).ok_or(())
        } else if plans.has_quant_plans {
            plans
                .prepared_quant_surface_overrides
                .take()
                .map(Some)
                .ok_or(())
        } else if !plans.trichotomies.is_empty() || !plans.assume_plans.is_empty() {
            Ok(None)
        } else {
            Ok(self.last_proof_term_overrides.clone())
        }
    }

    fn repair_authored_array_overrides(
        &mut self,
        originals: &[(TermId, FrontendTerm)],
        plans: &SurgeryPlans,
        next: &mut Option<SurfaceOverrides>,
    ) -> bool {
        if plans.authored_array_ites.is_empty() {
            return true;
        }
        let Some(overrides) = next.as_mut() else {
            return false;
        };
        let authored_roots: HashSet<TermId> = originals.iter().map(|(term, _)| *term).collect();
        for plan in plans.authored_array_ites.values() {
            self.strip_certified_array_fragment(plan, &authored_roots, overrides);
            if plan.guard_source != plan.guard {
                overrides.remove(&plan.guard);
            }
            let Some((_, parsed)) = originals
                .iter()
                .find(|(term, _)| *term == plan.array_equality)
            else {
                return false;
            };
            crate::executor::proof_surface_syntax::collect_root_surface_term_override(
                &mut self.ctx,
                plan.array_equality,
                parsed,
                overrides,
            );
            crate::executor::proof_surface_syntax::collect_deep_array_surface_overrides(
                &mut self.ctx,
                parsed,
                overrides,
            );
        }
        true
    }

    /// Only authored roots may retain spelling inside the independently
    /// certified ROW/congruence/ITE fragment checked immediately before commit.
    fn strip_certified_array_fragment(
        &mut self,
        plan: &AuthoredArrayItePlan,
        authored_roots: &HashSet<TermId>,
        overrides: &mut SurfaceOverrides,
    ) {
        let mut stack = vec![plan.target_or, plan.ite_term];
        stack.extend(plan.congruence_clause.iter().copied());
        stack.extend(plan.row1_clause.iter().copied());
        stack.extend(plan.transitivity_clause.iter().copied());
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if !authored_roots.contains(&term) {
                overrides.remove(&term);
            }
            stack.extend(self.ctx.terms.children(term));
        }
    }

    fn repair_authored_or_overrides(
        &mut self,
        originals: &[(TermId, FrontendTerm)],
        plans: &SurgeryPlans,
        next: &mut Option<SurfaceOverrides>,
    ) -> bool {
        if plans.normalized_authored_ors.is_empty() {
            return true;
        }
        let Some(overrides) = next.as_mut() else {
            return false;
        };
        for plan in plans.normalized_authored_ors.values() {
            let Some((_, parsed)) = originals.iter().find(|(term, _)| *term == plan.source_or)
            else {
                return false;
            };
            if !crate::executor::proof_surface_syntax::collect_surface_term_overrides(
                &mut self.ctx,
                plan.source_or,
                parsed,
                overrides,
            ) {
                return false;
            }
        }
        for plan in plans.normalized_authored_ors.values() {
            overrides.remove(&plan.target_or);
        }
        true
    }
}
