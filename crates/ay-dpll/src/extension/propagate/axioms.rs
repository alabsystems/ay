// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Callback liveness guards and pending theory-axiom delivery.

use ay_core::{FarkasAnnotation, TermId, TheoryLemmaKind, TheorySolver};
use ay_sat::ExtPropagateResult;

use super::*;
use crate::extension::infer_bound_axiom_arith_kind;

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Fail closed when propagation churn outlives its deadline or hard cap.
    pub(super) fn propagation_guard_result(&self) -> Option<ExtPropagateResult> {
        const DEADLINE_POLL_INTERVAL: u64 = 16;
        const DEFAULT_MAX_PROPAGATE_ROUNDS: u64 = 50_000_000;

        if self.solve_deadline.is_some_and(|deadline| {
            self.eager_stats
                .propagate_calls
                .is_multiple_of(DEADLINE_POLL_INTERVAL)
                && ay_core::time::Instant::now() >= deadline
        }) {
            return Some(ExtPropagateResult::none().with_stop(true));
        }

        let cap = ay_core::misc_cli_flags()
            .max_propagate_rounds
            .filter(|&cap| cap > 0)
            .unwrap_or(DEFAULT_MAX_PROPAGATE_ROUNDS);
        (self.eager_stats.propagate_calls > cap).then(|| ExtPropagateResult::none().with_stop(true))
    }

    /// Transfer pending axioms before observing any new SAT assignments.
    pub(super) fn take_pending_axiom_result(&mut self) -> Option<ExtPropagateResult> {
        if self.pending_axiom_clauses.is_empty() {
            return None;
        }
        let axioms = std::mem::take(&mut self.pending_axiom_clauses);
        let terms = std::mem::take(&mut self.pending_axiom_terms);
        let annotations = std::mem::take(&mut self.pending_axiom_farkas);
        self.record_pending_axioms(terms.into_iter().zip(annotations));
        Some(ExtPropagateResult::clauses(axioms))
    }

    /// Record each bound axiom with the strongest sound proof classification.
    fn record_pending_axioms(
        &mut self,
        axioms: impl Iterator<Item = ((TermId, bool, TermId, bool), Option<FarkasAnnotation>)>,
    ) {
        let Some(proof) = self.proof.as_mut() else {
            return;
        };
        for ((left, left_value, right, right_value), annotation) in axioms {
            let left_term = if left_value {
                left
            } else if let Some(&negated) = proof.negations.get(&left) {
                negated
            } else {
                continue;
            };
            let right_term = if right_value {
                right
            } else if let Some(&negated) = proof.negations.get(&right) {
                negated
            } else {
                continue;
            };
            let clause = vec![left_term, right_term];
            if let Some(kind) = self.terms.and_then(|terms| {
                infer_bound_axiom_arith_kind(terms, left, right, left_value, right_value)
            }) {
                let certificate =
                    annotation.unwrap_or_else(|| FarkasAnnotation::from_ints(&[1i64, 1]));
                proof
                    .tracker
                    .add_theory_lemma_with_farkas_and_kind(clause, certificate, kind);
                continue;
            }

            let (kind, clause) = match self.terms {
                None => (TheoryLemmaKind::Generic, clause),
                Some(terms) => {
                    let (kind, ordered) = crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                        terms,
                        &clause,
                        annotation.as_ref(),
                        None,
                    );
                    match ordered {
                        std::borrow::Cow::Borrowed(_) => (kind, clause),
                        std::borrow::Cow::Owned(ordered) if annotation.is_none() => (kind, ordered),
                        std::borrow::Cow::Owned(_) => (TheoryLemmaKind::Generic, clause),
                    }
                }
            };
            match kind {
                TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas => {
                    let certificate =
                        annotation.unwrap_or_else(|| FarkasAnnotation::from_ints(&[1i64, 1]));
                    proof
                        .tracker
                        .add_theory_lemma_with_farkas_and_kind(clause, certificate, kind);
                }
                TheoryLemmaKind::Generic => {
                    proof
                        .tracker
                        .add_theory_lemma_with_kind(clause, TheoryLemmaKind::Generic);
                }
                _ => {
                    proof.tracker.add_theory_lemma_with_kind(clause, kind);
                }
            }
        }
    }
}
