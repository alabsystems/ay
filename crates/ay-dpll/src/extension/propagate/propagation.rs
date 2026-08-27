// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main theory-propagation verification and SAT delivery lane.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{FarkasAnnotation, TheoryPropagation, TheoryResult, TheorySolver};
use ay_sat::{ExtPropagateResult, Literal};

use super::*;
use crate::extension::infer_bound_axiom_arith_kind;
use crate::extension::types::format_term_recursive;
use crate::verification::{log_propagation_debug, verify_theory_propagation};

enum PropagationDisposition {
    Skip,
    Lazy(Literal, u64),
    Lemma(Vec<Literal>),
    Eager(Vec<Literal>, Literal),
    Conflict(ExtPropagateResult),
}

enum ClauseDisposition {
    Skip,
    Lemma(Vec<Literal>),
    Propagation(Vec<Literal>),
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn deliver_theory_propagations(
        &mut self,
        round: &PropagationRound<'_>,
        mut check: CheckPhase,
    ) -> ExtPropagateResult {
        let propagations = self.theory.propagate();
        if propagations.is_empty() {
            return self.finish_empty_propagation_round(round, check);
        }
        self.zero_propagation_streak = 0;
        self.total_bcp_propagations += propagations.len() as u64;
        self.total_bcp_productive_prop_calls += 1;
        let mut batch = PropagationBatch::with_clauses(std::mem::take(&mut check.inline_clauses));
        for propagation in propagations {
            match self.process_propagation(propagation, round) {
                PropagationDisposition::Skip => {}
                PropagationDisposition::Lazy(literal, reason) => {
                    batch.lazy.push((literal, reason));
                }
                PropagationDisposition::Lemma(clause) => batch.clauses.push(clause),
                PropagationDisposition::Eager(clause, literal) => {
                    batch.eager.push((clause, literal));
                }
                PropagationDisposition::Conflict(result) => return result,
            }
        }
        self.finish_propagation_batch(round, check, batch)
    }

    fn process_propagation(
        &mut self,
        propagation: TheoryPropagation,
        round: &PropagationRound<'_>,
    ) -> PropagationDisposition {
        let propagation = match self.resolve_lazy_propagation(propagation, round.ctx) {
            LazyResolution::Skip => return PropagationDisposition::Skip,
            LazyResolution::Deliver {
                theory_literal,
                sat_literal,
                reason_data,
            } => {
                self.record_lazy_context_propagation(round.ctx, &theory_literal, reason_data);
                return PropagationDisposition::Lazy(sat_literal, reason_data);
            }
            LazyResolution::Materialized(propagation) => propagation,
        };
        self.process_materialized_propagation(propagation, round)
    }

    fn process_materialized_propagation(
        &mut self,
        propagation: TheoryPropagation,
        round: &PropagationRound<'_>,
    ) -> PropagationDisposition {
        if self.propagation_is_unmapped(&propagation) {
            return PropagationDisposition::Skip;
        }
        log_propagation_debug(&propagation, "eager");
        if let Err(e) = verify_theory_propagation(&propagation) {
            debug_assert!(
                false,
                "BUG(#4666): theory propagation verification failed: {e}"
            );
            tracing::warn!(
                error = %e,
                "BUG(#4666): theory propagation verification failed; skipping (#8595)"
            );
            return PropagationDisposition::Skip;
        }
        if !self.propagation_is_semantically_valid(&propagation) {
            return PropagationDisposition::Skip;
        }
        let Some(literal) =
            self.term_to_literal(propagation.literal.term, propagation.literal.value)
        else {
            return PropagationDisposition::Skip;
        };
        if let Some(value) = round.ctx.value(literal.variable()) {
            if value != propagation.literal.value {
                return self.propagation_conflict(&propagation, literal, round);
            }
            self.feedback_assigned_propagation(
                propagation.literal.term,
                propagation.literal.value,
                FeedbackLane::MainEager,
            );
            return PropagationDisposition::Skip;
        }
        match self.build_delivery_clause(&propagation, literal, round) {
            ClauseDisposition::Skip => PropagationDisposition::Skip,
            ClauseDisposition::Lemma(clause) => PropagationDisposition::Lemma(clause),
            ClauseDisposition::Propagation(clause) => {
                self.trace_and_record_propagation(&propagation, &clause, literal, round);
                PropagationDisposition::Eager(clause, literal)
            }
        }
    }

    fn propagation_is_unmapped(&mut self, propagation: &TheoryPropagation) -> bool {
        if self.term_to_var.contains_key(&propagation.literal.term) {
            return false;
        }
        self.eager_stats.props_unmapped += 1;
        if *PROP_DEBUG.get_or_init(|| ay_core::misc_cli_flags().prop_debug) {
            if let Some(terms) = self.terms {
                safe_eprintln!(
                    "PROPDBG UNMAPPED {} := {}",
                    propagation.literal.value,
                    format_term_recursive(terms, propagation.literal.term, 8)
                );
            }
        }
        true
    }

    fn propagation_conflict(
        &mut self,
        propagation: &TheoryPropagation,
        literal: Literal,
        round: &PropagationRound<'_>,
    ) -> PropagationDisposition {
        let mut conflict: Vec<Literal> = propagation
            .reason
            .iter()
            .filter_map(|reason| self.term_to_literal(reason.term, !reason.value))
            .collect();
        if conflict.len() < propagation.reason.len() {
            self.bump_partial_clause_count();
            self.emit_conflict_unknown(round);
            return PropagationDisposition::Skip;
        }
        if !reasons_are_falsified(&conflict, round) {
            tracing::warn!(
                propagated = ?literal,
                reason_count = conflict.len(),
                "BUG(#6262): theory propagation conflict has non-falsified reason literal; skipping"
            );
            return PropagationDisposition::Skip;
        }
        conflict.push(literal);
        if self.debug {
            safe_eprintln!(
                "[EAGER] Theory propagation conflict: {} literals",
                conflict.len()
            );
        }
        self.theory_conflict_count += 1;
        self.emit_eager_event(
            round.sat_level,
            round.asserted_atoms,
            "conflict",
            0,
            round.started_at,
        );
        let bump_vars = conflict.iter().map(|item| item.variable()).collect();
        PropagationDisposition::Conflict(
            ExtPropagateResult::conflict(conflict).with_bump_vars(bump_vars),
        )
    }

    fn build_delivery_clause(
        &mut self,
        propagation: &TheoryPropagation,
        literal: Literal,
        round: &PropagationRound<'_>,
    ) -> ClauseDisposition {
        let mut clause = Vec::with_capacity(propagation.reason.len() + 1);
        clause.push(literal);
        clause.extend(
            propagation
                .reason
                .iter()
                .filter_map(|reason| self.term_to_literal(reason.term, !reason.value)),
        );
        if clause.len() - 1 < propagation.reason.len() {
            self.bump_partial_clause_count();
            return ClauseDisposition::Skip;
        }
        if !reasons_are_falsified(&clause[1..], round) {
            tracing::warn!(
                propagated = ?literal,
                reason_count = clause.len() - 1,
                "BUG(#6262): theory propagation has non-falsified reason literal; demoting to lemma"
            );
            return ClauseDisposition::Lemma(clause);
        }
        ClauseDisposition::Propagation(clause)
    }

    fn trace_and_record_propagation(
        &mut self,
        propagation: &TheoryPropagation,
        clause: &[Literal],
        literal: Literal,
        round: &PropagationRound<'_>,
    ) {
        if self.debug {
            safe_eprintln!(
                "[EAGER] Adding propagation clause: {} literals (propagates {:?}={})",
                clause.len(),
                literal.variable(),
                propagation.literal.value
            );
        }
        if ay_core::misc_cli_flags().rup_fallback_trace {
            safe_eprintln!(
                "[level0-recorder] level={} lazy={} reason_len={}",
                round.ctx.decision_level(),
                propagation.reason_data.is_some(),
                propagation.reason.len()
            );
        }
        if round.ctx.decision_level() == 0 {
            self.record_level0_propagation(propagation, clause.len());
        }
        self.eager_stats.props_clause_added += 1;
        self.trace_mapped_propagation(propagation);
    }

    /// Record only level-0, single-reason, Farkas-classified implications.
    /// Widening either gate perturbs the proof firewall and has regressed the
    /// strict suites; uncertified `Generic` lemmas remain deliberately absent.
    fn record_level0_propagation(&mut self, propagation: &TheoryPropagation, clause_len: usize) {
        self.record_context_propagation(&propagation.literal, &propagation.reason);
        let terms = self.terms;
        let Some(proof) = self.proof.as_mut() else {
            return;
        };
        let mut clause = Vec::with_capacity(clause_len);
        if !push_term_at_polarity(
            &mut clause,
            propagation.literal.term,
            propagation.literal.value,
            proof.negations,
        ) {
            return;
        }
        for reason in &propagation.reason {
            if !push_term_at_polarity(&mut clause, reason.term, !reason.value, proof.negations) {
                return;
            }
        }
        let kind = match (terms, propagation.reason.as_slice()) {
            (Some(terms), [reason]) => infer_bound_axiom_arith_kind(
                terms,
                propagation.literal.term,
                reason.term,
                propagation.literal.value,
                reason.value,
            ),
            _ => None,
        };
        if let Some(kind) = kind {
            let _ = proof.tracker.add_theory_lemma_with_farkas_and_kind(
                clause,
                FarkasAnnotation::from_ints(&[1i64, 1]),
                kind,
            );
        }
    }

    fn trace_mapped_propagation(&self, propagation: &TheoryPropagation) {
        if !*PROP_DEBUG.get_or_init(|| ay_core::misc_cli_flags().prop_debug) {
            return;
        }
        if let Some(terms) = self.terms {
            let mut reason_key: Vec<_> = propagation
                .reason
                .iter()
                .map(|literal| (literal.term.0, literal.value))
                .collect();
            reason_key.sort_unstable();
            safe_eprintln!(
                "PROPDBG MAPPED {} rn={} rkey={:?} := {}",
                propagation.literal.value,
                propagation.reason.len(),
                reason_key,
                format_term_recursive(terms, propagation.literal.term, 8)
            );
        }
    }

    fn finish_empty_propagation_round(
        &mut self,
        round: &PropagationRound<'_>,
        check: CheckPhase,
    ) -> ExtPropagateResult {
        self.zero_propagation_streak += 1;
        self.emit_eager_event(
            round.sat_level,
            round.asserted_atoms,
            check.label.as_str(),
            check.inline_clauses.len(),
            round.started_at,
        );
        let split_stop = self.expression_split_stop();
        if split_stop {
            tracing::debug!(count = self.expr_split_seen_count, "expression split stop");
        }
        if check.refinement_handoff == RefinementHandoff::Stop {
            self.eager_stats.bound_refinement_handoffs += 1;
        }
        let stop = split_stop || check.refinement_handoff.requested();
        if check.inline_clauses.is_empty() && !stop {
            ExtPropagateResult::none()
        } else {
            ExtPropagateResult::clauses(check.inline_clauses).with_stop(stop)
        }
    }

    fn finish_propagation_batch(
        &mut self,
        round: &PropagationRound<'_>,
        check: CheckPhase,
        batch: PropagationBatch,
    ) -> ExtPropagateResult {
        let split_stop = self.expression_split_stop();
        if check.refinement_handoff == RefinementHandoff::Stop {
            self.eager_stats.bound_refinement_handoffs += 1;
        }
        let stop = split_stop || check.refinement_handoff.requested();
        let total = batch.len();
        if total == 0 {
            self.emit_eager_event(
                round.sat_level,
                round.asserted_atoms,
                check.label.as_str(),
                0,
                round.started_at,
            );
        } else {
            self.theory_propagation_count += total as u64;
            self.emit_eager_event(
                round.sat_level,
                round.asserted_atoms,
                "propagated",
                total,
                round.started_at,
            );
        }
        if total == 0 {
            return ExtPropagateResult::new(batch.clauses, batch.eager, None, stop);
        }
        let mut bump_vars = Vec::new();
        bump_vars.extend(
            batch
                .eager
                .iter()
                .flat_map(|(clause, _)| clause)
                .chain(batch.clauses.iter().flatten())
                .map(|literal| literal.variable()),
        );
        bump_vars.extend(batch.lazy.iter().map(|(literal, _)| literal.variable()));
        let mut result = ExtPropagateResult::new(batch.clauses, batch.eager, None, stop)
            .with_bump_vars(bump_vars);
        result.lazy_propagations = batch.lazy;
        result
    }

    fn expression_split_stop(&self) -> bool {
        self.expr_split_seen_count >= 50
            && matches!(
                &self.pending_split,
                Some(TheoryResult::NeedExpressionSplit(_))
            )
    }

    fn bump_partial_clause_count(&mut self) {
        self.partial_clause_count += 1;
        crate::combined_solvers::theory_stats::inc_partial_clauses();
        if self.partial_clause_count >= 100 {
            tracing::error!(
                count = self.partial_clause_count,
                "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
            );
        }
    }
}

pub(super) fn reasons_are_falsified(reasons: &[Literal], round: &PropagationRound<'_>) -> bool {
    reasons.iter().all(|literal| {
        round
            .ctx
            .value(literal.variable())
            .is_some_and(|value| value != literal.is_positive())
    })
}

fn push_term_at_polarity(
    clause: &mut Vec<ay_core::TermId>,
    term: ay_core::TermId,
    positive: bool,
    negations: &HashMap<ay_core::TermId, ay_core::TermId>,
) -> bool {
    if positive {
        clause.push(term);
        true
    } else if let Some(&negated) = negations.get(&term) {
        clause.push(negated);
        true
    } else {
        false
    }
}
