// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transactional assume and retained-rendering policy planning.

use super::super::*;
use super::model::{SurgeryInput, SurgeryPlans};
use crate::executor::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;

struct AssumeScan {
    audit: Option<ProvenanceSurfaceAudit>,
    kept_surface_sensitive: bool,
    print_faithful: HashMap<TermId, bool>,
}

impl Executor {
    pub(super) fn plan_assumes_and_surface_policy(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        quant_plan_count: &mut usize,
        plans: &mut SurgeryPlans,
    ) -> bool {
        plans.has_ite_lift_plans =
            !plans.ite_lifts.is_empty() || !plans.provenance_ite_lifts.is_empty();
        plans.keeps_surface_overrides = self.initially_keeps_surface_overrides(plans);
        let Ok(audit) = self.prepare_initial_surface_audit(input, plans) else {
            return false;
        };
        if !Self::collect_quant_source_replacements(plans) {
            return false;
        }
        let mut scan = AssumeScan {
            audit,
            kept_surface_sensitive: false,
            print_faithful: HashMap::default(),
        };
        if !self.classify_live_assumes(input, authority, quant_plan_count, plans, &mut scan) {
            return false;
        }
        plans.keeps_surface_overrides |=
            !plans.taut_units.is_empty() || !plans.euf_lemmas.is_empty();
        plans.has_quant_plans = !plans.quant_negations.is_empty()
            || !plans.quant_consequences.is_empty()
            || plans
                .assume_plans
                .values()
                .any(|plan| matches!(plan, AssumePlan::QuantExpansion { .. }));
        if !Self::surface_plan_mix_is_allowed(plans, &scan) {
            return false;
        }
        self.finalize_surface_plan(input, plans, scan.audit)
    }

    fn initially_keeps_surface_overrides(&self, plans: &SurgeryPlans) -> bool {
        plans.has_ite_lift_plans
            || !plans.normalized_authored_ors.is_empty()
            || !plans.authored_array_ites.is_empty()
            || !plans.or_units.is_empty()
            || !plans.exact_provenance_or_assumes.is_empty()
            || !plans.provenance_or_plans.is_empty()
            || !plans.subst_eqs.is_empty()
            || !plans.taut_units.is_empty()
            || !plans.euf_lemmas.is_empty()
    }

    fn prepare_initial_surface_audit(
        &mut self,
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
    ) -> Result<Option<ProvenanceSurfaceAudit>, ()> {
        if !plans.keeps_surface_overrides {
            return Ok(None);
        }
        let Some(mut audit) = self.plan_retained_surface_audit(
            input.originals,
            &plans.ite_lifts,
            &plans.provenance_ite_lifts,
            &plans.exact_provenance_or_assumes,
            &plans.provenance_or_plans,
            &plans.or_units,
            &plans.subst_eqs,
        ) else {
            return Err(());
        };
        if !self.register_authored_surface_plans(input, plans, &mut audit)
            || !self.register_deferred_surface_leaves(input, plans, &mut audit)
        {
            return Err(());
        }
        Ok(Some(audit))
    }

    fn register_authored_surface_plans(
        &mut self,
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
        audit: &mut ProvenanceSurfaceAudit,
    ) -> bool {
        for plan in plans.normalized_authored_ors.values() {
            if !audit.require_original(&mut self.ctx, input.originals, plan.source_or) {
                return false;
            }
            audit.protect_operand(&mut self.ctx.terms, plan.source_or);
        }
        for plan in plans.authored_array_ites.values() {
            if !audit.require_original(&mut self.ctx, input.originals, plan.array_equality)
                || !audit.require_original_as(
                    &mut self.ctx,
                    input.originals,
                    plan.guard,
                    plan.guard_source,
                )
            {
                return false;
            }
            audit.protect_operand(&mut self.ctx.terms, plan.array_equality);
            audit.protect_operand(&mut self.ctx.terms, plan.guard_source);
        }
        true
    }

    /// Deferred leaves are later re-tagged from their exact clause trees.
    /// Marking every literal rigid prevents retained spellings from changing
    /// either the later recognizer's authority input or emitted operands.
    fn register_deferred_surface_leaves(
        &mut self,
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
        audit: &mut ProvenanceSurfaceAudit,
    ) -> bool {
        for &index in &plans.deferred_leaves {
            let ProofStep::TheoryLemma { clause, .. } = &input.proof.steps[index] else {
                return false;
            };
            for &literal in clause {
                audit.protect_rigid_operand(&mut self.ctx.terms, literal);
            }
        }
        true
    }

    fn collect_quant_source_replacements(plans: &mut SurgeryPlans) -> bool {
        for plan in plans.quant_negations.values() {
            if let Some(previous) = plans
                .quant_source_replacements
                .insert(plan.source_quantifier, plan.forall_term)
            {
                if previous != plan.forall_term {
                    return false;
                }
            }
        }
        true
    }

    fn classify_live_assumes(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        quant_plan_count: &mut usize,
        plans: &mut SurgeryPlans,
        scan: &mut AssumeScan,
    ) -> bool {
        for (index, step) in input.proof.steps.iter().enumerate() {
            if !input.live[index] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if !self.classify_one_assume(
                input,
                authority,
                quant_plan_count,
                plans,
                scan,
                index,
                *term,
            ) {
                return false;
            }
        }
        true
    }

    fn classify_one_assume(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        quant_plan_count: &mut usize,
        plans: &mut SurgeryPlans,
        scan: &mut AssumeScan,
        index: usize,
        term: TermId,
    ) -> bool {
        if plans.quant_source_replacements.contains_key(&term) {
            return self.spend_quant_source_assume(term, authority);
        }
        if !authority
            .planning_budget()
            .spend_terms(&self.ctx.terms, &[term])
        {
            return false;
        }
        let Some((_, parsed)) = input.source_index.get(input.originals, term) else {
            return self.classify_derived_assume(
                input,
                authority,
                quant_plan_count,
                plans,
                index,
                term,
            );
        };
        let override_policy = if plans.keeps_surface_overrides {
            assume_classification::SurfaceOverridePolicy::Retained
        } else {
            assume_classification::SurfaceOverridePolicy::Rebuilt
        };
        match self.classify_assume(term, parsed, override_policy) {
            Ok(Some(plan)) => {
                plans.assume_plans.insert(index, plan);
                true
            }
            Ok(None) => self.validate_faithful_assume(input, authority, scan, term, parsed),
            Err(()) => false,
        }
    }

    fn classify_derived_assume(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        quant_plan_count: &mut usize,
        plans: &mut SurgeryPlans,
        index: usize,
        term: TermId,
    ) -> bool {
        if let Some(plan) =
            self.classify_quant_expansion(term, input.originals, authority, quant_plan_count)
        {
            plans.assume_plans.insert(index, plan);
            return true;
        }
        if let Some(plan) = self.plan_or_transitivity_tautology(&[term]) {
            plans.taut_units.insert(index, plan);
            return true;
        }
        if let Some(plan) = self.plan_euf_lemma_with_budget(&[term], authority.planning_budget()) {
            if plan.or_term().is_some() {
                plans.euf_lemmas.insert(index, plan);
                return true;
            }
        }
        false
    }

    fn validate_faithful_assume(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        scan: &mut AssumeScan,
        term: TermId,
        parsed: &FrontendTerm,
    ) -> bool {
        if scan
            .audit
            .as_mut()
            .is_some_and(|audit| !audit.require_original(&mut self.ctx, input.originals, term))
        {
            return false;
        }
        let has_surface = self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| overrides.contains_key(&term));
        if !has_surface {
            return true;
        }
        let faithful = if let Some(&cached) = scan.print_faithful.get(&term) {
            cached
        } else {
            if !authority.planning_budget().spend_surface(term, parsed)
                || !authority
                    .planning_budget()
                    .spend_terms(&self.ctx.terms, &[term])
            {
                return false;
            }
            let raw = self.raw_intern_surface(parsed);
            let rendered = raw.map(|raw| (raw, ay_proof::format_term_alethe(&self.ctx.terms, raw)));
            let faithful = rendered.is_some_and(|(raw, rendered)| {
                self.last_proof_term_overrides
                    .as_ref()
                    .and_then(|overrides| overrides.get(&term))
                    == Some(&rendered)
                    && eq_flip_equivalent(&self.ctx.terms, raw, term)
            });
            scan.print_faithful.insert(term, faithful);
            faithful
        };
        scan.kept_surface_sensitive |= !faithful;
        true
    }

    fn surface_plan_mix_is_allowed(plans: &SurgeryPlans, scan: &AssumeScan) -> bool {
        let will_purge = !plans.keeps_surface_overrides
            && plans.subst_eqs.is_empty()
            && (!plans.trichotomies.is_empty()
                || !plans.assume_plans.is_empty()
                || plans.has_quant_plans);
        if scan.kept_surface_sensitive && will_purge {
            return false;
        }
        if !surface_override_policy_allows(
            plans.keeps_surface_overrides,
            !plans.assume_plans.is_empty(),
        ) {
            return false;
        }
        let unaudited_deferred = !plans.deferred_leaves.is_empty() && scan.audit.is_none();
        if !retained_surface_plan_mix_is_safe(
            plans.keeps_surface_overrides,
            unaudited_deferred,
            plans.has_quant_plans,
        ) {
            return false;
        }
        if plans.has_quant_plans
            && (!plans.trichotomies.is_empty()
                || plans
                    .assume_plans
                    .values()
                    .any(|plan| !matches!(plan, AssumePlan::QuantExpansion { .. })))
        {
            return false;
        }
        if !plans.subst_eqs.is_empty() && (!plans.assume_plans.is_empty() || plans.has_quant_plans)
        {
            return false;
        }
        plans.trichotomies.is_empty() || !plans.keeps_surface_overrides
    }

    fn finalize_surface_plan(
        &mut self,
        input: &SurgeryInput<'_>,
        plans: &mut SurgeryPlans,
        audit: Option<ProvenanceSurfaceAudit>,
    ) -> bool {
        if !plans.keeps_surface_overrides {
            return plans.has_repairs();
        }
        let mut replaced = HashSet::default();
        for index in plans
            .ite_lifts
            .keys()
            .chain(plans.provenance_ite_lifts.keys())
            .chain(plans.normalized_authored_ors.keys())
            .chain(plans.authored_array_ites.keys())
            .chain(plans.exact_provenance_or_assumes.keys())
            .chain(plans.provenance_or_plans.keys())
            .chain(plans.or_units.keys())
            .chain(plans.taut_units.keys())
            .chain(plans.euf_lemmas.keys())
            .chain(plans.subst_eqs.keys())
        {
            replaced.insert(*index);
        }
        let Some(effective) = self.finalize_retained_surface_overrides(
            input.proof,
            input.live,
            &replaced,
            audit.unwrap_or_default(),
            &plans.taut_units,
            &plans.euf_lemmas,
        ) else {
            return false;
        };
        plans.prepared_surface_overrides = Some(effective);
        plans.has_repairs()
    }
}
