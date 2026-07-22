// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

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
