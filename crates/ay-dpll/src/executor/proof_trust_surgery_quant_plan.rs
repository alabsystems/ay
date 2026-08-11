// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded classification of recorded finite-domain quantifier expansions.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::TermId;
use ay_frontend::command::Term as FrontendTerm;
use std::mem::size_of;

use super::{
    quant_canonical_term_work, quant_surface, AssumePlan, QuantConsequencePlan, QuantNegationPlan,
};
use crate::executor::proof_surface_syntax::strip_frontend_annotations;
use crate::executor::proof_trust_surgery_provenance::{complement_of, MAX_PROVENANCE_REPAIR_TERMS};
use crate::executor::Executor;

fn quant_plan_capacity_remaining(plan_count: usize, requested_chains: usize) -> bool {
    requested_chains > 0
        && plan_count
            .checked_add(requested_chains)
            .is_some_and(|total| total <= quant_surface::MAX_QUANT_SURFACE_CHAINS)
}

fn record_quant_plan(plan_count: &mut usize, requested_chains: usize) -> bool {
    if !quant_plan_capacity_remaining(*plan_count, requested_chains) {
        return false;
    }
    *plan_count += requested_chains;
    true
}

impl Executor {
    /// Charge one trust clause before classification. Generic canonical work
    /// deliberately rejects binders, but the direct E-matching lane starts
    /// from the exact singleton `(not forall)` clause and validates that
    /// quantifier through its bounded body downstream.
    pub(super) fn spend_trust_clause_terms(
        &self,
        clause: &[TermId],
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
    ) -> bool {
        if let [literal] = clause {
            if let TermData::Not(forall) = self.ctx.terms.get(*literal) {
                if matches!(self.ctx.terms.get(*forall), TermData::Forall(..)) {
                    return self.spend_quant_source_assume(*forall, authority);
                }
            }
        }
        authority
            .planning_budget()
            .spend_terms(&self.ctx.terms, clause)
    }

    /// Charge the canonical body of an exact quantifier-shaped source
    /// candidate. Generic term preflight intentionally rejects binders, so
    /// this lane enters through its bounded body; source authority is still
    /// authenticated by the downstream quantifier planner and surface audit.
    pub(super) fn spend_quant_source_assume(
        &self,
        term: TermId,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
    ) -> bool {
        let TermData::Forall(_, body, _) = self.ctx.terms.get(term) else {
            return false;
        };
        authority.spend_solver_attempt(&self.ctx.terms, &[*body])
    }

    /// Match a recorded expansion only to one exact bounded authored forall.
    pub(super) fn classify_quant_expansion(
        &self,
        term: TermId,
        originals: &[(TermId, FrontendTerm)],
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        plan_count: &mut usize,
    ) -> Option<AssumePlan> {
        if !authority.is_valid() {
            return None;
        }
        let TermData::App(sym, conjs) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "and"
            || conjs.is_empty()
            || conjs.len() > quant_surface::MAX_QUANT_SURFACE_CHAINS
            || !quant_plan_capacity_remaining(*plan_count, conjs.len())
        {
            return None;
        }
        if !authority.spend_classification_work(conjs.len().saturating_mul(size_of::<TermId>())) {
            return None;
        }
        let conjuncts: HashSet<TermId> = conjs.iter().copied().collect();
        if conjuncts.len() != conjs.len() {
            return None;
        }
        for record in self.quant_expansion_records.iter().take(4096) {
            if !authority.spend_classification_work(1) {
                return None;
            }
            if !matches!(self.ctx.terms.get(record.original), TermData::Forall(..)) {
                continue;
            }
            let Some((forall_canonical, parsed)) = originals.get(record.assertion_index) else {
                continue;
            };
            let forall_canonical = *forall_canonical;
            if !matches!(self.ctx.terms.get(forall_canonical), TermData::Forall(..))
                || authority.original(originals, forall_canonical).is_none()
                || record.instances.len() > quant_surface::MAX_QUANT_SURFACE_CHAINS
                || record
                    .instances
                    .iter()
                    .any(|(values, _)| values.len() > MAX_PROVENANCE_REPAIR_TERMS)
            {
                continue;
            }
            if !authority.spend_chain_source(forall_canonical, parsed) {
                return None;
            }
            if !matches!(strip_frontend_annotations(parsed), FrontendTerm::Forall(..)) {
                continue;
            }
            let mut selected: HashMap<TermId, usize> = HashMap::default();
            for (instance_index, (values, instance)) in record.instances.iter().enumerate() {
                let work = values
                    .len()
                    .checked_mul(size_of::<TermId>())
                    .and_then(|bytes| bytes.checked_add(1))?;
                if !authority.spend_classification_work(work) {
                    return None;
                }
                if conjuncts.contains(instance) {
                    selected.entry(*instance).or_insert(instance_index);
                }
            }
            if selected.len() == conjs.len() {
                let mut instances: HashMap<TermId, Vec<TermId>> = HashMap::default();
                for &conjunct in conjs {
                    let &instance_index = selected.get(&conjunct)?;
                    let values = &record.instances.get(instance_index)?.0;
                    if !authority.spend_solver_attempt(&self.ctx.terms, values) {
                        return None;
                    }
                    instances.insert(conjunct, values.clone());
                }
                if !record_quant_plan(plan_count, conjs.len()) {
                    return None;
                }
                return Some(AssumePlan::QuantExpansion {
                    forall_term: forall_canonical,
                    assertion_index: record.assertion_index,
                    conjs: conjs.clone(),
                    instances,
                });
            }
        }
        None
    }

    /// Recognize a refuted exact direct E-matching instance of one authored
    /// forall, with one independently checked arithmetic support.
    pub(super) fn plan_ematching_quant_negation(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        plan_count: &mut usize,
    ) -> Option<QuantNegationPlan> {
        if clause.len() != 1
            || self.ematching_proof_records.is_empty()
            || !authority.is_valid()
            || !quant_plan_capacity_remaining(*plan_count, 1)
        {
            return None;
        }
        let conclusion = clause[0];
        let supports = authority.nonquant_supports(&self.ctx.terms, originals)?;
        let record_count = self.ematching_proof_records.len().min(4096);
        for record_index in 0..record_count {
            let (quantifier, assertion_index, instance) = {
                let record = &self.ematching_proof_records[record_index];
                if record.binding.len() > MAX_PROVENANCE_REPAIR_TERMS {
                    continue;
                }
                (record.quantifier, record.assertion_index, record.instance)
            };
            if complement_of(&mut self.ctx.terms, quantifier) != conclusion {
                continue;
            }
            let binding = &self.ematching_proof_records[record_index].binding;
            if !authority.spend_solver_attempt(&self.ctx.terms, binding)
                || !authority.spend_solver_attempt(&self.ctx.terms, &[instance])
            {
                return None;
            }
            let binding = binding.clone();
            let Some((forall_term, parsed)) = originals.get(assertion_index) else {
                continue;
            };
            let forall_term = *forall_term;
            if !matches!(self.ctx.terms.get(forall_term), TermData::Forall(..))
                || authority.original(originals, forall_term).is_none()
            {
                continue;
            }
            if !authority.spend_chain_source(forall_term, parsed) {
                return None;
            }
            if matches!(
                strip_frontend_annotations(parsed),
                FrontendTerm::Symbol(name)
                    if name == crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER
            ) {
                let TermData::Forall(_, body, _) = self.ctx.terms.get(forall_term) else {
                    continue;
                };
                let Some(work) = quant_canonical_term_work(&self.ctx.terms, *body)
                    .and_then(|work| work.checked_mul(3))
                else {
                    continue;
                };
                if !authority.spend_canonical_work(work) {
                    return None;
                }
            }
            let Some(chain) =
                self.build_direct_ematching_instance_chain(forall_term, parsed, &binding, instance)
            else {
                continue;
            };
            let raw_instance = chain.phi;
            if !authority.spend_chain_source(forall_term, parsed) {
                return None;
            }
            if !authority.spend_solver_attempt(&self.ctx.terms, &binding) {
                return None;
            }
            let Some(raw_forall) =
                self.build_raw_ematching_forall_source(forall_term, parsed, &binding, raw_instance)
            else {
                continue;
            };
            let mut selected_support = None;
            for &support in &supports {
                if !authority.spend_solver_attempt(&self.ctx.terms, &[raw_instance, support]) {
                    return None;
                }
                if self.quant_conflict_valid(&[raw_instance, support]) {
                    selected_support = Some(support);
                    break;
                }
            }
            let Some(support) = selected_support else {
                continue;
            };
            let lemma = vec![
                complement_of(&mut self.ctx.terms, raw_instance),
                complement_of(&mut self.ctx.terms, support),
            ];
            if !record_quant_plan(plan_count, 1) {
                return None;
            }
            return Some(QuantNegationPlan {
                source_quantifier: quantifier,
                assertion_index,
                forall_term: raw_forall,
                chain,
                supports: vec![support],
                lemma,
            });
        }
        None
    }

    /// Recognize a folded consequence of one quantifier-expansion instance
    /// and at most one exact authored arithmetic support.
    pub(super) fn plan_quant_consequence(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        plan_count: &mut usize,
    ) -> Option<QuantConsequencePlan> {
        if clause.len() != 1
            || self.quant_expansion_records.is_empty()
            || !authority.is_valid()
            || !quant_plan_capacity_remaining(*plan_count, 1)
        {
            return None;
        }
        let conclusion = clause[0];
        let supports = authority.nonquant_supports(&self.ctx.terms, originals)?;
        let mut budget = 20_000usize;
        let record_count = self.quant_expansion_records.len().min(4096);
        for record_index in 0..record_count {
            let assertion_index = self.quant_expansion_records[record_index].assertion_index;
            let Some((forall_term, parsed)) = originals.get(assertion_index) else {
                continue;
            };
            let forall_term = *forall_term;
            if !matches!(self.ctx.terms.get(forall_term), TermData::Forall(..))
                || authority.original(originals, forall_term).is_none()
            {
                continue;
            }
            if !authority.spend_chain_source(forall_term, parsed) {
                return None;
            }
            if !matches!(strip_frontend_annotations(parsed), FrontendTerm::Forall(..)) {
                continue;
            }
            let instance_count = self.quant_expansion_records[record_index].instances.len();
            for instance_index in 0..instance_count {
                budget = budget.checked_sub(1)?;
                let (values, inst) = {
                    let (values, inst) =
                        &self.quant_expansion_records[record_index].instances[instance_index];
                    if values.len() > MAX_PROVENANCE_REPAIR_TERMS {
                        continue;
                    }
                    if !authority.spend_solver_attempt(&self.ctx.terms, values) {
                        return None;
                    }
                    (values.clone(), *inst)
                };
                if matches!(self.ctx.terms.get(inst), TermData::Const(_)) {
                    continue;
                }
                if !authority.spend_solver_attempt(&self.ctx.terms, &[inst, conclusion]) {
                    return None;
                }
                let used = if self.quant_lemma_valid(&[inst], conclusion) {
                    Vec::new()
                } else {
                    let mut found = None;
                    for &support in &supports {
                        budget = budget.checked_sub(1)?;
                        if !authority
                            .spend_solver_attempt(&self.ctx.terms, &[inst, support, conclusion])
                        {
                            return None;
                        }
                        if self.quant_lemma_valid(&[inst, support], conclusion) {
                            found = Some(support);
                            break;
                        }
                    }
                    let Some(support) = found else {
                        continue;
                    };
                    vec![support]
                };
                if !authority.spend_chain_source(forall_term, parsed) {
                    return None;
                }
                if !authority.spend_solver_attempt(&self.ctx.terms, &values) {
                    return None;
                }
                let Some(chain) = self.build_quant_instance_chain(parsed, &values, inst) else {
                    continue;
                };
                let mut lemma = Vec::with_capacity(2 + used.len());
                lemma.push(complement_of(&mut self.ctx.terms, inst));
                for &support in &used {
                    lemma.push(complement_of(&mut self.ctx.terms, support));
                }
                lemma.push(conclusion);
                if !record_quant_plan(plan_count, 1) {
                    return None;
                }
                return Some(QuantConsequencePlan {
                    forall_term,
                    chain,
                    supports: used,
                    lemma,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::{quant_surface, record_quant_plan};

    #[test]
    fn quant_plan_budget_rejects_the_513th_chain_before_classification() {
        let mut count = 0usize;
        for _ in 0..quant_surface::MAX_QUANT_SURFACE_CHAINS {
            assert!(record_quant_plan(&mut count, 1));
        }
        assert!(!record_quant_plan(&mut count, 1));
        let mut empty = 0;
        assert!(!record_quant_plan(
            &mut empty,
            quant_surface::MAX_QUANT_SURFACE_CHAINS + 1,
        ));
        assert_eq!(count, quant_surface::MAX_QUANT_SURFACE_CHAINS);
    }
}
