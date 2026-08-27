// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Classification of the BCP-time theory check result.

use ay_core::{TheoryResult, TheorySolver};
use ay_sat::Literal;

use super::*;

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn handle_bcp_check_result(
        &mut self,
        result: TheoryResult,
        round: &PropagationRound<'_>,
    ) -> PhaseOutcome<CheckPhase> {
        let mut phase = CheckPhase::new();
        match result {
            TheoryResult::Sat => self.handle_theory_sat(&mut phase),
            TheoryResult::Unknown => {
                self.pending_bound_refinements.clear();
                phase.label = CheckLabel::Unknown;
            }
            TheoryResult::NeedLemmas(lemmas) => self.handle_inline_lemmas(lemmas, &mut phase),
            TheoryResult::NeedExpressionSplit(split) => {
                self.handle_expression_split(split, &mut phase);
            }
            TheoryResult::NeedExpressionSplits(splits) => {
                self.handle_expression_splits(splits, &mut phase);
            }
            TheoryResult::NeedModelEquality(equality) => {
                self.handle_model_equality(equality, &mut phase);
            }
            TheoryResult::NeedModelEqualities(equalities) => {
                if let Some(result) = self.filter_stale_model_equalities(equalities) {
                    self.store_pending_split(result, &mut phase);
                } else {
                    phase.label = CheckLabel::StaleModelEqualities;
                }
            }
            result @ (TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedStringLemma(_)) => self.store_pending_split(result, &mut phase),
            TheoryResult::Unsat(conflict) => {
                return PhaseOutcome::Complete(self.handle_plain_conflict(conflict, round));
            }
            TheoryResult::UnsatWithFarkas(conflict) => {
                return PhaseOutcome::Complete(self.handle_farkas_conflict(conflict, round));
            }
            other => unreachable!("unhandled TheoryResult variant in propagate(): {other:?}"),
        }
        PhaseOutcome::Continue(phase)
    }

    fn handle_theory_sat(&mut self, phase: &mut CheckPhase) {
        let stale_expression_split = matches!(
            &self.pending_split,
            Some(TheoryResult::NeedExpressionSplit(split))
                if self.processed_expr_splits
                    .is_some_and(|set| set.contains(&split.disequality_term))
        );
        if stale_expression_split
            || !matches!(
                &self.pending_split,
                Some(TheoryResult::NeedExpressionSplit(_))
            )
        {
            self.pending_split = None;
        }
        let refinements = self.theory.take_bound_refinements();
        if self.should_stop_for_inline_bound_refinement_handoff(&refinements) {
            phase.refinement_handoff = RefinementHandoff::Stop;
        }
        self.record_pending_bound_refinements(refinements);
    }

    fn handle_inline_lemmas(&mut self, lemmas: Vec<ay_core::TheoryLemma>, phase: &mut CheckPhase) {
        let mut sat_clauses = Vec::with_capacity(lemmas.len());
        let mut all_mapped = true;
        for lemma in &lemmas {
            let literals: Vec<Literal> = lemma
                .clause
                .iter()
                .filter_map(|term| self.term_to_literal(term.term, term.value))
                .collect();
            if literals.len() != lemma.clause.len() {
                all_mapped = false;
                break;
            }
            sat_clauses.push(literals);
        }
        if !all_mapped || sat_clauses.is_empty() {
            self.store_pending_split(TheoryResult::NeedLemmas(lemmas), phase);
            return;
        }

        self.eager_stats.inline_lemma_clauses += sat_clauses.len() as u64;
        phase.label = CheckLabel::InlineLemmas;
        phase.inline_clauses.extend(sat_clauses);
        if let Some(proof) = self.proof.as_mut() {
            for lemma in &lemmas {
                let _ = crate::theory_inference::record_materialized_lemma_clause(
                    proof.tracker,
                    self.terms,
                    proof.negations,
                    &lemma.clause,
                );
            }
        }
    }

    fn handle_expression_split(
        &mut self,
        split: ay_core::ExpressionSplitRequest,
        phase: &mut CheckPhase,
    ) {
        if self
            .processed_expr_splits
            .is_some_and(|set| set.contains(&split.disequality_term))
        {
            phase.label = CheckLabel::StaleSplit;
            return;
        }
        self.expr_split_seen_count += 1;
        self.store_pending_split(TheoryResult::NeedExpressionSplit(split), phase);
    }

    fn handle_expression_splits(
        &mut self,
        splits: Vec<ay_core::ExpressionSplitRequest>,
        phase: &mut CheckPhase,
    ) {
        let mut fresh = splits;
        if let Some(processed) = self.processed_expr_splits {
            fresh.retain(|split| !processed.contains(&split.disequality_term));
        }
        if fresh.is_empty() {
            phase.label = CheckLabel::StaleSplit;
            return;
        }
        self.expr_split_seen_count += 1;
        let result = if fresh.len() == 1 {
            let Some(split) = fresh.pop() else {
                return;
            };
            TheoryResult::NeedExpressionSplit(split)
        } else {
            TheoryResult::NeedExpressionSplits(fresh)
        };
        self.store_pending_split(result, phase);
    }

    fn handle_model_equality(
        &mut self,
        equality: ay_core::ModelEqualityRequest,
        phase: &mut CheckPhase,
    ) {
        if self.model_equality_already_encoded(&equality) {
            phase.label = CheckLabel::StaleModelEquality;
        } else {
            self.store_pending_split(TheoryResult::NeedModelEquality(equality), phase);
        }
    }

    fn store_pending_split(&mut self, result: TheoryResult, phase: &mut CheckPhase) {
        self.pending_split = Some(result);
        self.pending_bound_refinements.clear();
        phase.label = CheckLabel::Split;
    }
}
