// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Planning and finalization of retained proof-surface requirements.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{FarkasAnnotation, Proof, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::{IteLiftPlan, OrTautologyPlan, OrUnitPlan, SubstEqPlan};
use crate::executor::proof_euf_lemma::EufLemmaPlan;
use crate::executor::proof_trust_surgery_ite::ProvenanceItePlan;
use crate::executor::proof_trust_surgery_provenance::{complement_of, ProvenanceSurfaceAudit};
use crate::executor::proof_trust_surgery_provenance_or::ProvenanceOrPlan;
use crate::executor::proof_trust_surgery_surface_audit::{
    copied_structural_roles_are_static, live_proof_rendering_is_static,
};
use crate::executor::Executor;

#[cfg(test)]
#[path = "proof_trust_surgery_surface_plans_tests.rs"]
mod tests;

impl Executor {
    /// Collect every authenticated source spelling and every rigid emitted
    /// operand known before Assume classification. No override is installed
    /// here; final validation happens only after late tautology/EUF plans are
    /// known.
    pub(super) fn plan_retained_surface_audit(
        &mut self,
        originals: &[(TermId, FrontendTerm)],
        ite_lifts: &HashMap<usize, IteLiftPlan>,
        provenance_ite_lifts: &HashMap<usize, ProvenanceItePlan>,
        exact_provenance_or_assumes: &HashMap<usize, TermId>,
        provenance_or_plans: &HashMap<usize, ProvenanceOrPlan>,
        or_units: &HashMap<usize, OrUnitPlan>,
        subst_eqs: &HashMap<usize, SubstEqPlan>,
    ) -> Option<ProvenanceSurfaceAudit> {
        let mut audit = ProvenanceSurfaceAudit::default();
        for plan in ite_lifts.values() {
            let source_ok = if let Some(source) = plan.defining_source {
                audit.require_original_arithmetic_alias_only(
                    &mut self.ctx,
                    originals,
                    source,
                    plan.orig,
                )
            } else {
                audit.require_original(&mut self.ctx, originals, plan.orig)
            };
            if !source_ok
                || plan
                    .bound
                    .is_some_and(|bound| !audit.require_original(&mut self.ctx, originals, bound))
            {
                return None;
            }
            audit.protect_operand(&mut self.ctx.terms, plan.cond);
            for operand in [
                plan.orig,
                plan.lifted_then,
                plan.lifted_else,
                plan.eq_then,
                plan.eq_else,
            ]
            .into_iter()
            .chain(plan.bound)
            {
                audit.protect_farkas_operand(&mut self.ctx.terms, operand);
            }
            for (branch_eq, lifted) in [
                (plan.eq_then, plan.lifted_then),
                (plan.eq_else, plan.lifted_else),
            ] {
                let not_eq = complement_of(&mut self.ctx.terms, branch_eq);
                let not_orig = complement_of(&mut self.ctx.terms, plan.orig);
                let mut clause = vec![not_eq, not_orig];
                if let Some(bound) = plan.bound {
                    clause.push(complement_of(&mut self.ctx.terms, bound));
                }
                clause.push(lifted);
                let farkas = FarkasAnnotation::from_ints(&vec![1; clause.len()]);
                audit.protect_farkas_lemma(&mut self.ctx.terms, &clause, &farkas);
            }
            for operand in [plan.goal, plan.ite_def, plan.and_term, plan.intro_eq] {
                audit.protect_rigid_root(&mut self.ctx.terms, operand);
            }
            audit.protect_ite_intro_role(
                &mut self.ctx.terms,
                plan.ite_term,
                plan.eq_then,
                plan.eq_else,
            );
        }
        for plan in provenance_ite_lifts.values() {
            let source_ok = if let Some(source) = plan.defining_source {
                audit.require_original_arithmetic_alias_only(
                    &mut self.ctx,
                    originals,
                    source,
                    plan.orig,
                )
            } else {
                audit.require_original(&mut self.ctx, originals, plan.orig)
            };
            if !source_ok
                || plan
                    .supports
                    .iter()
                    .any(|&support| !audit.require_original(&mut self.ctx, originals, support))
            {
                return None;
            }
            plan.protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }
        for &orig in exact_provenance_or_assumes.values() {
            if !audit.require_original(&mut self.ctx, originals, orig) {
                return None;
            }
            audit.protect_operand(&mut self.ctx.terms, orig);
        }
        for plan in provenance_or_plans.values() {
            if plan
                .authored_sources()
                .iter()
                .any(|&source| !audit.require_original(&mut self.ctx, originals, source))
            {
                return None;
            }
            plan.protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }
        for plan in or_units.values() {
            if !audit.require_original(&mut self.ctx, originals, plan.orig)
                || plan.eliminations.iter().any(|&(_, complement)| {
                    !audit.require_original(&mut self.ctx, originals, complement)
                })
            {
                return None;
            }
            audit.protect_operand(&mut self.ctx.terms, plan.orig);
            for &operand in &plan.disjuncts {
                audit.protect_operand(&mut self.ctx.terms, operand);
            }
            for &(pivot, complement) in &plan.eliminations {
                audit.protect_operand(&mut self.ctx.terms, pivot);
                audit.protect_operand(&mut self.ctx.terms, complement);
            }
        }
        for plan in subst_eqs.values() {
            if plan
                .hyps
                .iter()
                .any(|&source| !audit.require_original(&mut self.ctx, originals, source))
            {
                return None;
            }
            if let Some(&target) = plan.lemma.first() {
                audit.protect_rigid_operand(&mut self.ctx.terms, target);
            }
            for &hypothesis in &plan.hyps {
                audit.protect_operand(&mut self.ctx.terms, hypothesis);
            }
            plan.euf
                .protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }
        Some(audit)
    }

    /// Add plans discovered during Assume classification, then validate the
    /// final effective rendering and return the only map safe to commit.
    pub(super) fn finalize_retained_surface_overrides(
        &mut self,
        proof: &Proof,
        live: &[bool],
        replaced: &ay_core::kani_compat::DetHashSet<usize>,
        mut audit: ProvenanceSurfaceAudit,
        taut_units: &HashMap<usize, OrTautologyPlan>,
        euf_lemmas: &HashMap<usize, EufLemmaPlan>,
    ) -> Option<HashMap<TermId, String>> {
        for plan in taut_units.values() {
            plan.protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }
        for plan in euf_lemmas.values() {
            plan.protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }
        if !audit.protect_copied_resolution_and_farkas_roles(
            proof,
            live,
            replaced,
            &mut self.ctx.terms,
        ) {
            return None;
        }
        if !audit.aliases_are_fresh_in(proof, &self.ctx.terms) {
            return None;
        }
        let base = self.last_proof_term_overrides.as_ref();
        if base.is_some_and(|active| !audit.active_map_is_bounded(active)) {
            return None;
        }
        let mut effective = base.cloned().unwrap_or_default();
        if !audit.merge_into(&mut effective)
            || !live_proof_rendering_is_static(proof, live, &self.ctx.terms, &effective)
            || !copied_structural_roles_are_static(
                proof,
                live,
                replaced,
                &self.ctx.terms,
                &effective,
            )
            || !audit.validate_effective(&self.ctx.terms, &effective)
        {
            return None;
        }
        Some(effective)
    }
}
