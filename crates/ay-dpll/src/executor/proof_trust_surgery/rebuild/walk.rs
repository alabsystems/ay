// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Single forward step-remap walk and its fixed dispatch order.

use super::super::*;
use super::model::{EmitDecision, RebuildState, RebuildWalk, SurgeryInput, SurgeryPlans};

impl Executor {
    pub(super) fn emit_ordered_rebuild(
        &mut self,
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
        state: &mut RebuildState,
    ) -> bool {
        RebuildWalk {
            executor: self,
            input,
            plans,
            state,
        }
        .run()
    }
}

impl RebuildWalk<'_, '_> {
    fn run(&mut self) -> bool {
        for index in 0..self.input.step_count() {
            if !self.input.live[index] || self.plans.dropped_and_pos[index] {
                continue;
            }
            if !self.emit_step(index) {
                return false;
            }
        }
        true
    }

    fn emit_step(&mut self, index: usize) -> bool {
        if let Some(accepted) = self.emit_redirected_split(index).resolved() {
            return accepted;
        }
        if let Some(accepted) = self.emit_trichotomy(index).resolved() {
            return accepted;
        }
        if let Some(accepted) = self.emit_lift_family(index).resolved() {
            return accepted;
        }
        if let Some(accepted) = self.emit_simple_plan_family(index).resolved() {
            return accepted;
        }
        if let Some(accepted) = self.emit_unit_pattern(index).resolved() {
            return accepted;
        }
        self.emit_assume_or_copy(index)
    }

    fn emit_redirected_split(&mut self, index: usize) -> EmitDecision {
        let Some(&trust_index) = self.plans.or_split_of.get(&index) else {
            return EmitDecision::NotApplicable;
        };
        self.state.map[index] = self.state.trichotomy_clause.get(&trust_index).copied();
        if self.state.map[index].is_some() {
            EmitDecision::Emitted
        } else {
            EmitDecision::Reject
        }
    }

    fn emit_trichotomy(&mut self, index: usize) -> EmitDecision {
        let Some(plan) = self.plans.trichotomies.get(&index) else {
            return EmitDecision::NotApplicable;
        };
        let proof = &mut self.state.new_proof;
        let la = proof.add_rule_step(
            AletheRule::LaDisequality,
            vec![plan.or_term],
            Vec::new(),
            Vec::new(),
        );
        let split = proof.add_rule_step(
            AletheRule::Or,
            vec![plan.eq, plan.not_le_xy, plan.not_le_yx],
            vec![la],
            Vec::new(),
        );
        let from_yx = Executor::add_pair_lemma(proof, plan.strong_from_yx, plan.le_yx);
        let first = proof.add_resolution(
            vec![plan.eq, plan.not_le_xy, plan.strong_from_yx],
            plan.le_yx,
            split,
            from_yx,
        );
        let from_xy = Executor::add_pair_lemma(proof, plan.strong_from_xy, plan.le_xy);
        let strengthened = proof.add_resolution(
            vec![plan.eq, plan.strong_from_yx, plan.strong_from_xy],
            plan.le_xy,
            first,
            from_xy,
        );
        self.state.trichotomy_clause.insert(index, strengthened);
        EmitDecision::Emitted
    }
}
