// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Premise-remapped copying of untouched live proof steps.

use super::super::*;
use super::model::RebuildWalk;

impl RebuildWalk<'_, '_> {
    pub(super) fn copy_old_step(&mut self, index: usize) -> bool {
        match self.input.proof.steps[index].clone() {
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => self.copy_rule_step(index, &rule, &clause, &premises, &args),
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => self.copy_resolution(index, &clause, pivot, clause1, clause2),
            ProofStep::TheoryLemma { .. } => {
                let id = self
                    .state
                    .new_proof
                    .add_step(self.input.proof.steps[index].clone());
                self.state.map[index] = Some(id);
                true
            }
            _ => false,
        }
    }

    fn copy_rule_step(
        &mut self,
        index: usize,
        rule: &AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> bool {
        let mut remapped = Vec::with_capacity(premises.len());
        for premise in premises {
            let Some(mapped) = self.state.map[premise.0 as usize] else {
                return false;
            };
            remapped.push(mapped);
        }
        let Some(clause) = self.repair_or_decomposition_clause(rule, clause, premises) else {
            return false;
        };
        let id = self
            .state
            .new_proof
            .add_rule_step(rule.clone(), clause, remapped, args.to_vec());
        self.state.map[index] = Some(id);
        true
    }

    /// Solver-trail order is not proof authority. For a copied `or` consumer
    /// of a newly derived packed unit, require exact multiset equality and use
    /// the packed term's own operand order, which the Alethe rule checks.
    fn repair_or_decomposition_clause(
        &self,
        rule: &AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
    ) -> Option<Vec<TermId>> {
        if !matches!(rule, AletheRule::Or) || premises.len() != 1 {
            return Some(clause.to_vec());
        }
        let source = premises[0].0 as usize;
        let planned_term = self
            .plans
            .taut_units
            .get(&source)
            .map(|plan| plan.term)
            .or_else(|| {
                self.plans
                    .euf_lemmas
                    .get(&source)
                    .and_then(EufLemmaPlan::or_term)
            });
        let Some(term) = planned_term else {
            return Some(clause.to_vec());
        };
        let TermData::App(Symbol::Named(operator), disjuncts) = self.executor.ctx.terms.get(term)
        else {
            return None;
        };
        if operator != "or" {
            return None;
        }
        let disjuncts = disjuncts.clone();
        let mut expected = disjuncts.clone();
        let mut actual = clause.to_vec();
        expected.sort_unstable();
        actual.sort_unstable();
        (expected == actual).then_some(disjuncts)
    }

    fn copy_resolution(
        &mut self,
        index: usize,
        clause: &[TermId],
        pivot: TermId,
        first: ProofId,
        second: ProofId,
    ) -> bool {
        let (Some(first), Some(second)) = (
            self.state.map[first.0 as usize],
            self.state.map[second.0 as usize],
        ) else {
            return false;
        };
        let pivot = self
            .plans
            .quant_source_replacements
            .get(&pivot)
            .copied()
            .unwrap_or(pivot);
        let id = self
            .state
            .new_proof
            .add_resolution(clause.to_vec(), pivot, first, second);
        self.state.map[index] = Some(id);
        true
    }
}
