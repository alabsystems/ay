// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored-source, standalone-lemma, and quantifier leaf emission.

use super::super::*;
use super::model::{EmitDecision, RebuildWalk};

impl RebuildWalk<'_, '_> {
    pub(super) fn emit_simple_plan_family(&mut self, index: usize) -> EmitDecision {
        if let Some(result) = self.emit_authored_leaf(index).resolved() {
            return if result {
                EmitDecision::Emitted
            } else {
                EmitDecision::Reject
            };
        }
        if let Some(result) = self.emit_standalone_lemma(index).resolved() {
            return if result {
                EmitDecision::Emitted
            } else {
                EmitDecision::Reject
            };
        }
        self.emit_quantifier_leaf(index)
    }

    fn record(&mut self, index: usize, proof: ProofId) -> EmitDecision {
        self.state.map[index] = Some(proof);
        EmitDecision::Emitted
    }

    fn record_optional(&mut self, index: usize, proof: Option<ProofId>) -> EmitDecision {
        match proof {
            Some(proof) => self.record(index, proof),
            None => EmitDecision::Reject,
        }
    }

    fn emit_authored_leaf(&mut self, index: usize) -> EmitDecision {
        if let Some(plan) = self.plans.or_units.get(&index) {
            let Some(&assume) = self.state.lift_assume.get(&plan.orig) else {
                return EmitDecision::Reject;
            };
            let mut current = self.state.new_proof.add_rule_step(
                AletheRule::Or,
                plan.disjuncts.clone(),
                vec![assume],
                Vec::new(),
            );
            let mut remaining = plan.disjuncts.clone();
            for &(pivot, complement) in &plan.eliminations {
                let Some(&complement_assume) = self.state.lift_assume.get(&complement) else {
                    return EmitDecision::Reject;
                };
                remaining.retain(|&literal| atom_of(&self.executor.ctx.terms, literal) != pivot);
                current = self.state.new_proof.add_resolution(
                    remaining.clone(),
                    pivot,
                    current,
                    complement_assume,
                );
            }
            return self.record(index, current);
        }
        if let Some(plan) = self.plans.normalized_authored_ors.get(&index) {
            let Some(&assume) = self.state.lift_assume.get(&plan.source_or) else {
                return EmitDecision::Reject;
            };
            let unit =
                self.executor
                    .emit_normalized_authored_or(&mut self.state.new_proof, plan, assume);
            return self.record_optional(index, unit);
        }
        let Some(plan) = self.plans.authored_array_ites.get(&index) else {
            return EmitDecision::NotApplicable;
        };
        let (Some(&equality), Some(&guard)) = (
            self.state.lift_assume.get(&plan.array_equality),
            self.state.lift_assume.get(&plan.guard_source),
        ) else {
            return EmitDecision::Reject;
        };
        let unit =
            self.executor
                .emit_authored_array_ite(&mut self.state.new_proof, plan, equality, guard);
        self.record_optional(index, unit)
    }

    fn emit_standalone_lemma(&mut self, index: usize) -> EmitDecision {
        if let Some(plan) = self.plans.taut_units.get(&index) {
            let unit = if let Some(&unit) = self.state.taut_unit_of_term.get(&plan.term) {
                unit
            } else {
                let unit = self
                    .executor
                    .emit_or_tautology_derivation(&mut self.state.new_proof, plan);
                self.state.taut_unit_of_term.insert(plan.term, unit);
                unit
            };
            return self.record(index, unit);
        }
        if let Some(plan) = self.plans.euf_lemmas.get(&index).cloned() {
            let unit = if let Some(unit) = plan
                .or_term()
                .and_then(|term| self.state.euf_unit_of_term.get(&term).copied())
            {
                unit
            } else {
                let unit = self
                    .executor
                    .emit_euf_lemma(&mut self.state.new_proof, &plan);
                if let Some(term) = plan.or_term() {
                    self.state.euf_unit_of_term.insert(term, unit);
                }
                unit
            };
            return self.record(index, unit);
        }
        let Some(plan) = self.plans.subst_eqs.get(&index).cloned() else {
            return EmitDecision::NotApplicable;
        };
        let unit = self.executor.emit_substituted_equality(
            &mut self.state.new_proof,
            &plan,
            &self.state.lift_assume,
        );
        self.record_optional(index, unit)
    }

    fn emit_quantifier_leaf(&mut self, index: usize) -> EmitDecision {
        if let Some(plan) = self.plans.quant_negations.get(&index) {
            let unit = self.executor.emit_ematching_quant_negation(
                &mut self.state.new_proof,
                plan,
                &self.state.lift_assume,
            );
            return self.record_optional(index, unit);
        }
        let Some(plan) = self.plans.quant_consequences.get(&index) else {
            return EmitDecision::NotApplicable;
        };
        let Some(&assume) = self.state.lift_assume.get(&plan.forall_term) else {
            return EmitDecision::Reject;
        };
        let instance = self.executor.emit_quant_instance_chain(
            &mut self.state.new_proof,
            plan.forall_term,
            assume,
            &plan.chain,
        );
        let coefficients = vec![1i64; plan.lemma.len()];
        let lemma = self.state.new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: plan.lemma.clone(),
            farkas: Some(FarkasAnnotation::from_ints(&coefficients)),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let pivot = atom_of(&self.executor.ctx.terms, plan.chain.target);
        let mut current =
            self.state
                .new_proof
                .add_resolution(plan.lemma[1..].to_vec(), pivot, lemma, instance);
        for (offset, &support) in plan.supports.iter().enumerate() {
            let Some(&support_id) = self.state.lift_assume.get(&support) else {
                return EmitDecision::Reject;
            };
            current = self.state.new_proof.add_resolution(
                plan.lemma[offset + 2..].to_vec(),
                atom_of(&self.executor.ctx.terms, support),
                current,
                support_id,
            );
        }
        self.record(index, current)
    }
}
