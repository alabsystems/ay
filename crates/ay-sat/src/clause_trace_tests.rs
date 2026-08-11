// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use super::{HintOmission, HintOmissionStats};
use crate::clause_trace_resolution::{
    validate_clause_trace_resolution, ClauseTraceResolutionError,
};
use crate::literal::Variable;
use crate::resolution_validate::ResolutionValidationLimits;

#[test]
fn test_clause_trace_basic() {
    let mut trace = ClauseTrace::new();
    assert!(trace.is_empty());
    assert!(!trace.has_empty_clause());

    // Add an original clause
    trace.add_clause(
        1,
        vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        true,
    );
    assert_eq!(trace.len(), 1);
    assert!(trace.entries()[0].is_original);
    assert!(trace.entries()[0].resolution_hints.is_empty());

    // Add a learned clause
    trace.add_clause(2, vec![Literal::positive(Variable(2))], false);
    assert_eq!(trace.len(), 2);
    assert!(!trace.entries()[1].is_original);
    assert!(trace.entries()[1].resolution_hints.is_empty());

    // Add empty clause
    trace.add_clause(3, vec![], false);
    assert!(trace.has_empty_clause());
}

#[test]
fn test_clause_trace_set_resolution_hints() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(10, vec![Literal::positive(Variable(0))], false);
    trace.add_clause(11, vec![Literal::negative(Variable(1))], false);

    assert!(trace.set_resolution_hints(11, vec![3, 4, 5]));
    assert_eq!(trace.entries()[1].resolution_hints, vec![3, 4, 5]);
    assert!(!trace.set_resolution_hints(99, vec![1]));
}

#[test]
fn test_clause_trace_iterators() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable(0))], true);
    trace.add_clause(2, vec![Literal::positive(Variable(1))], false);
    trace.add_clause(3, vec![Literal::positive(Variable(2))], true);
    trace.add_clause(4, vec![Literal::positive(Variable(3))], false);

    assert_eq!(trace.original_clauses().count(), 2);
    assert_eq!(trace.learned_clauses().count(), 2);
}

/// Regression test for #4435: add_clause_with_hints attaches hints atomically.
/// Before this fix, hints were added in a separate set_resolution_hints call
/// which could be lost if the caller was refactored or interrupted.
#[test]
fn test_clause_trace_atomic_hints_regression_4435() {
    let mut trace = ClauseTrace::new();

    // Atomic path: hints attached at insertion time
    trace.add_clause_with_hints(
        100,
        vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        false,
        vec![1, 2, 3],
    );
    let entry = &trace.entries()[0];
    assert_eq!(entry.id, 100);
    assert!(!entry.is_original);
    assert_eq!(entry.resolution_hints, vec![1, 2, 3]);

    // Empty clause with hints (level-0 conflict chain pattern)
    trace.add_clause_with_hints(101, vec![], false, vec![5, 6]);
    let empty_entry = &trace.entries()[1];
    assert_eq!(empty_entry.id, 101);
    assert!(empty_entry.clause.is_empty());
    assert_eq!(empty_entry.resolution_hints, vec![5, 6]);
    assert!(trace.has_empty_clause());
}

/// #6553: memory budget caps unbounded growth.
#[test]
fn test_clause_trace_memory_budget() {
    let mut trace = ClauseTrace::new();
    // Override budget to a small value for testing.
    trace.budget_bytes = 256;
    assert!(!trace.is_truncated());
    assert_eq!(trace.used_bytes(), 0);

    // Add entries until budget is exceeded.
    let mut added = 0;
    for i in 0..100u64 {
        let prev_len = trace.len();
        trace.add_clause(
            i,
            vec![
                Literal::positive(Variable(i as u32)),
                Literal::negative(Variable(0)),
            ],
            i < 5,
        );
        if trace.len() > prev_len {
            added += 1;
        }
    }

    // Some entries should have been recorded, but not all 100.
    assert!(added > 0, "at least one entry should fit in 256 bytes");
    assert!(added < 100, "budget should have capped entries");
    assert!(trace.is_truncated());
    assert!(trace.used_bytes() <= trace.budget_bytes + 128); // small overshoot from last accepted entry OK
}

/// #6553: empty clauses always recorded even when budget exceeded.
#[test]
fn test_clause_trace_budget_empty_clause_always_recorded() {
    let mut trace = ClauseTrace::new();
    // Set budget to 0 to force immediate truncation.
    trace.budget_bytes = 0;

    // Non-empty clause should be dropped.
    trace.add_clause(1, vec![Literal::positive(Variable(0))], false);
    assert_eq!(trace.len(), 0);
    assert!(trace.is_truncated());

    // Empty clause should always be recorded (UNSAT signal).
    trace.add_clause_with_hints(2, vec![], false, vec![1]);
    assert_eq!(trace.len(), 1);
    assert!(trace.has_empty_clause());
    assert_eq!(trace.entries()[0].id, 2);
}

#[test]
fn resolution_conversion_rejects_truncated_trace() {
    let mut trace = ClauseTrace::new();
    trace.budget_bytes = 0;
    trace.add_clause(1, vec![Literal::positive(Variable(0))], true);

    assert_eq!(
        validate_clause_trace_resolution(&trace, 1, &ResolutionValidationLimits::unbounded())
            .unwrap_err(),
        ClauseTraceResolutionError::Truncated
    );
}

#[test]
fn hint_omission_stats_count_each_cause_separately() {
    let trace = ClauseTrace::new();
    assert_eq!(trace.hint_omission_stats(), HintOmissionStats::default());

    trace.record_hint_lookup(None);
    trace.record_hint_lookup(None);
    trace.record_hint_lookup(Some(HintOmission::NotClauseReason));
    trace.record_hint_lookup(Some(HintOmission::LazyTheoryReason));
    trace.record_hint_lookup(Some(HintOmission::LazyTheoryReason));
    trace.record_hint_lookup(Some(HintOmission::ZeroClauseId));

    let stats = trace.hint_omission_stats();
    assert_eq!(stats.queries, 6, "every lookup is counted");
    assert_eq!(stats.resolved, 2);
    assert_eq!(stats.omitted_not_clause_reason, 1);
    assert_eq!(stats.omitted_lazy_theory_reason, 2);
    assert_eq!(stats.omitted_zero_clause_id, 1);
    assert_eq!(stats.omitted_total(), 4);
    assert_eq!(
        stats.resolved + stats.omitted_total(),
        stats.queries,
        "resolved + omitted must account for every query"
    );
}

#[test]
fn solver_namespace_stamp_is_opaque_clone_stable_and_mutation_sensitive() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable(0))], true);
    assert_eq!(trace.solver_num_vars(), None);

    trace.stamp_solver_num_vars(7);
    assert_eq!(trace.solver_num_vars(), Some(7));
    assert_eq!(trace.clone().solver_num_vars(), Some(7));

    // Diagnostic counters do not change certificate content.
    trace.record_hint_lookup(None);
    assert_eq!(trace.solver_num_vars(), Some(7));

    trace.set_resolution_hints(1, vec![2]);
    assert_eq!(trace.solver_num_vars(), None);

    trace.stamp_solver_num_vars(7);
    trace.mark_empty();
    assert_eq!(trace.solver_num_vars(), None);
}
