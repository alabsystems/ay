// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transactional rendered-surface audit for standalone quantifier repair.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, Proof, Sort, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::{AssumePlan, QuantConsequencePlan, QuantInstanceChain, QuantNegationPlan};
use crate::executor::proof_trust_surgery_provenance::{
    complement_of, unique_atoms, ProvenanceSurfaceAudit, MAX_PROVENANCE_REPAIR_TERMS,
};
use crate::executor::proof_trust_surgery_surface_audit::{
    copied_structural_roles_are_static, live_proof_rendering_is_static,
};
use crate::executor::Executor;

#[path = "proof_trust_surgery_quant_surface_authority.rs"]
mod authority;
pub(super) use authority::QuantSurfaceAuthority;
#[path = "proof_trust_surgery_quant_surface_copied.rs"]
mod copied;
use copied::copied_quant_rendering_roles_are_static;
#[cfg(test)]
#[path = "proof_trust_surgery_quant_surface_tests.rs"]
mod tests;

pub(super) const MAX_QUANT_SURFACE_CHAINS: usize = 512;

pub(super) struct QuantSurfacePlans<'a> {
    pub(super) assumes: &'a HashMap<usize, AssumePlan>,
    pub(super) chains: &'a HashMap<(usize, usize), QuantInstanceChain>,
    pub(super) consequences: &'a HashMap<usize, QuantConsequencePlan>,
    pub(super) negations: &'a HashMap<usize, QuantNegationPlan>,
}

fn all_ones_farkas(width: usize) -> FarkasAnnotation {
    let coefficients = vec![1i64; width];
    FarkasAnnotation::from_ints(&coefficients)
}

impl Executor {
    fn register_quant_chain_surface(
        &mut self,
        authority: &mut QuantSurfaceAuthority<'_>,
        audit: &mut ProvenanceSurfaceAudit,
        source_forall: TermId,
        actual_forall: TermId,
        parsed: &FrontendTerm,
        chain: &QuantInstanceChain,
    ) -> bool {
        if !authority.spend_chain_source(source_forall, parsed)
            || chain.values.len() > MAX_PROVENANCE_REPAIR_TERMS
            || chain
                .guard
                .as_ref()
                .is_some_and(|(_, atoms)| atoms.len() > MAX_PROVENANCE_REPAIR_TERMS)
        {
            return false;
        }
        if !authority.spend_solver_attempt(&self.ctx.terms, &chain.values) {
            return false;
        }
        let Some(raw_forall) =
            self.build_raw_ematching_forall_source(source_forall, parsed, &chain.values, chain.phi)
        else {
            return false;
        };
        audit.protect_operand(&mut self.ctx.terms, actual_forall);
        if raw_forall != actual_forall {
            audit.protect_rigid_operand(&mut self.ctx.terms, raw_forall);
            audit.require_same_rendering(&mut self.ctx.terms, actual_forall, raw_forall);
        }
        for &value in &chain.values {
            audit.protect_rigid_operand(&mut self.ctx.terms, value);
        }
        audit.protect_rigid_operand(&mut self.ctx.terms, chain.phi);
        audit.protect_rigid_operand(&mut self.ctx.terms, chain.target);

        let not_forall = self.ctx.terms.mk_not_raw(actual_forall);
        let inst_or =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [not_forall, chain.phi], Sort::Bool);
        audit.protect_rigid_root(&mut self.ctx.terms, not_forall);
        audit.protect_rigid_root(&mut self.ctx.terms, inst_or);

        if let Some((guard, atoms)) = &chain.guard {
            let TermData::App(Symbol::Named(op), implication) = self.ctx.terms.get(chain.phi)
            else {
                return false;
            };
            if op != "=>" || implication.as_slice() != [*guard, chain.body_lit] {
                return false;
            }
            if atoms.len() == 1 {
                if atoms[0] != *guard {
                    return false;
                }
            } else if !matches!(
                self.ctx.terms.get(*guard),
                TermData::App(Symbol::Named(op), parts)
                    if op == "and" && parts.as_slice() == atoms.as_slice()
            ) {
                return false;
            }
            if !unique_atoms(&self.ctx.terms, atoms) {
                return false;
            }
            for &atom in atoms {
                audit.protect_farkas_lemma(
                    &mut self.ctx.terms,
                    &[atom],
                    &FarkasAnnotation::from_ints(&[1]),
                );
            }
        } else if chain.body_lit != chain.phi {
            return false;
        }

        if chain.target != chain.body_lit {
            let body_complement = complement_of(&mut self.ctx.terms, chain.body_lit);
            let clause = [chain.target, body_complement];
            if !unique_atoms(&self.ctx.terms, &clause) {
                return false;
            }
            audit.protect_farkas_lemma(
                &mut self.ctx.terms,
                &clause,
                &FarkasAnnotation::from_ints(&[1, 1]),
            );
        }
        true
    }

    fn register_quant_consequence_surface(
        &mut self,
        authority: &mut QuantSurfaceAuthority<'_>,
        audit: &mut ProvenanceSurfaceAudit,
        originals: &[(TermId, FrontendTerm)],
        plan: &QuantConsequencePlan,
    ) -> bool {
        let Some(parsed) = authority.original(originals, plan.forall_term) else {
            return false;
        };
        if !authority.authenticate(
            self,
            audit,
            originals,
            plan.forall_term,
            plan.forall_term,
            true,
        ) || !self.register_quant_chain_surface(
            authority,
            audit,
            plan.forall_term,
            plan.forall_term,
            parsed,
            &plan.chain,
        ) {
            return false;
        }
        for &support in &plan.supports {
            if !authority.authenticate(self, audit, originals, support, support, true) {
                return false;
            }
            audit.protect_operand(&mut self.ctx.terms, support);
        }
        if plan.lemma.len() != plan.supports.len().saturating_add(2) {
            return false;
        }
        let mut expected = vec![complement_of(&mut self.ctx.terms, plan.chain.target)];
        expected.extend(
            plan.supports
                .iter()
                .map(|&support| complement_of(&mut self.ctx.terms, support)),
        );
        expected.push(*plan.lemma.last().unwrap_or(&plan.chain.target));
        if plan.lemma != expected || !unique_atoms(&self.ctx.terms, &plan.lemma) {
            return false;
        }
        audit.protect_farkas_lemma(
            &mut self.ctx.terms,
            &plan.lemma,
            &all_ones_farkas(plan.lemma.len()),
        );
        true
    }

    fn register_quant_negation_surface(
        &mut self,
        authority: &mut QuantSurfaceAuthority<'_>,
        audit: &mut ProvenanceSurfaceAudit,
        originals: &[(TermId, FrontendTerm)],
        plan: &QuantNegationPlan,
    ) -> bool {
        let Some((source_forall, parsed)) = originals.get(plan.assertion_index) else {
            return false;
        };
        let source_forall = *source_forall;
        if authority.original(originals, source_forall).is_none()
            || !authority.authenticate(
                self,
                audit,
                originals,
                source_forall,
                plan.source_quantifier,
                true,
            )
        {
            return false;
        }
        if plan.forall_term != plan.source_quantifier
            && !authority.authenticate(
                self,
                audit,
                originals,
                source_forall,
                plan.forall_term,
                false,
            )
        {
            return false;
        }
        audit.protect_operand(&mut self.ctx.terms, plan.source_quantifier);
        audit.require_same_rendering(
            &mut self.ctx.terms,
            plan.source_quantifier,
            plan.forall_term,
        );
        if !self.register_quant_chain_surface(
            authority,
            audit,
            source_forall,
            plan.forall_term,
            parsed,
            &plan.chain,
        ) {
            return false;
        }
        for &support in &plan.supports {
            if !authority.authenticate(self, audit, originals, support, support, true) {
                return false;
            }
            audit.protect_operand(&mut self.ctx.terms, support);
        }
        let mut expected = vec![complement_of(&mut self.ctx.terms, plan.chain.phi)];
        expected.extend(
            plan.supports
                .iter()
                .map(|&support| complement_of(&mut self.ctx.terms, support)),
        );
        if plan.lemma != expected || !unique_atoms(&self.ctx.terms, &plan.lemma) {
            return false;
        }
        audit.protect_farkas_lemma(
            &mut self.ctx.terms,
            &plan.lemma,
            &all_ones_farkas(plan.lemma.len()),
        );
        true
    }

    /// Build and validate the exact map standalone quantifier surgery will
    /// commit. Every source and emitted surface-sensitive rule is registered
    /// before the proof is rebuilt; any collision or budget exhaustion keeps
    /// the original proof and map byte-identical.
    pub(super) fn prepare_quant_surface_overrides(
        &mut self,
        authority: &mut QuantSurfaceAuthority<'_>,
        proof: &Proof,
        live: &[bool],
        originals: &[(TermId, FrontendTerm)],
        plans: QuantSurfacePlans<'_>,
    ) -> Option<HashMap<TermId, String>> {
        let total_chains = plans
            .chains
            .len()
            .checked_add(plans.consequences.len())?
            .checked_add(plans.negations.len())?;
        if total_chains == 0 || total_chains > MAX_QUANT_SURFACE_CHAINS {
            return None;
        }
        let mut audit = ProvenanceSurfaceAudit::default();

        for (&(assume_index, _), chain) in plans.chains {
            let Some(AssumePlan::QuantExpansion {
                forall_term,
                assertion_index,
                ..
            }) = plans.assumes.get(&assume_index)
            else {
                return None;
            };
            let (source, parsed) = originals.get(*assertion_index)?;
            if source != forall_term {
                return None;
            }
            if !authority.authenticate(
                self,
                &mut audit,
                originals,
                *forall_term,
                *forall_term,
                true,
            ) || !self.register_quant_chain_surface(
                authority,
                &mut audit,
                *forall_term,
                *forall_term,
                parsed,
                chain,
            ) {
                return None;
            }
        }
        for plan in plans.consequences.values() {
            if !self.register_quant_consequence_surface(authority, &mut audit, originals, plan) {
                return None;
            }
        }
        for plan in plans.negations.values() {
            if !self.register_quant_negation_surface(authority, &mut audit, originals, plan) {
                return None;
            }
        }
        let replaced: HashSet<usize> = plans
            .assumes
            .keys()
            .chain(plans.consequences.keys())
            .chain(plans.negations.keys())
            .copied()
            .collect();
        if !audit.protect_copied_resolution_and_farkas_roles(
            proof,
            live,
            &replaced,
            &mut self.ctx.terms,
        ) {
            return None;
        }
        if !audit.aliases_are_fresh_in(proof, &self.ctx.terms) {
            return None;
        }
        let overrides = audit.materialize_protected_requirements()?;
        if !copied_quant_rendering_roles_are_static(
            proof,
            live,
            &plans,
            &self.ctx.terms,
            &overrides,
            authority.authenticated_assume_roots(),
        ) || !live_proof_rendering_is_static(proof, live, &self.ctx.terms, &overrides)
            || !copied_structural_roles_are_static(
                proof,
                live,
                &replaced,
                &self.ctx.terms,
                &overrides,
            )
            || !audit.validate_effective(&self.ctx.terms, &overrides)
        {
            return None;
        }
        Some(overrides)
    }
}
