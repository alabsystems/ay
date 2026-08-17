// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::mem::size_of;

use crate::clause_trace_resolution::{
    validate_clause_trace_resolution, ClauseTraceResolutionError,
};
use crate::literal::Variable;
use crate::resolution_validate::ResolutionValidationLimits;

use super::*;
use super::{HintOmission, HintOmissionStats};

fn retained_arena_bytes(trace: &ClauseTrace) -> usize {
    trace.meta.capacity() * size_of::<EntryMeta>()
        + trace.lit_pool.capacity() * size_of::<Literal>()
        + trace.hint_pool.capacity() * size_of::<u64>()
}

fn minimum_add_peak_bytes(trace: &ClauseTrace, clause_len: usize, hints_len: usize) -> usize {
    let new_entries = trace.meta.len() + 1;
    let new_literals = trace.lit_pool.len() + clause_len;
    let new_hints = trace.hint_pool.len() + hints_len;
    trace.used_bytes()
        + (new_entries > trace.meta.capacity()) as usize * new_entries * size_of::<EntryMeta>()
        + (new_literals > trace.lit_pool.capacity()) as usize * new_literals * size_of::<Literal>()
        + (new_hints > trace.hint_pool.capacity()) as usize * new_hints * size_of::<u64>()
}

fn four_entry_trace() -> ClauseTrace {
    let mut trace = ClauseTrace::new();
    let lit = Literal::positive(Variable(0));
    for id in 1..=4 {
        trace.add_clause_with_hints(id, vec![lit], false, vec![id]);
    }
    assert_eq!(
        (
            trace.meta.capacity(),
            trace.lit_pool.capacity(),
            trace.hint_pool.capacity(),
        ),
        (4, 4, 4),
        "fixture must reach the geometric-growth boundary"
    );
    trace
}

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
    assert!(trace.entries().at(0).is_original);
    assert!(trace.entries().at(0).resolution_hints.is_empty());

    // Add a learned clause
    trace.add_clause(2, vec![Literal::positive(Variable(2))], false);
    assert_eq!(trace.len(), 2);
    assert!(!trace.entries().at(1).is_original);
    assert!(trace.entries().at(1).resolution_hints.is_empty());

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
    assert_eq!(trace.entries().at(1).resolution_hints, vec![3, 4, 5]);
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

    // Allocation-explicit compatibility for callers that need the pre-A3
    // owned-entry snapshot shape.
    let snapshot = trace.entries_snapshot();
    assert_eq!(snapshot.len(), 4);
    assert_eq!(snapshot[0].id, 1);
    assert_eq!(snapshot[0].clause, vec![Literal::positive(Variable(0))]);
    assert!(snapshot[0].is_original);
}

/// A3 hardening: replacing an interior hint span must compact/reindex the
/// arena instead of retaining unreachable payload. Repeating the operation
/// cannot grow the pool independently of the live hint census, and a growth
/// that exceeds the writer budget fails closed without mutating the entry.
#[test]
fn test_clause_trace_repeated_interior_hint_replacement_stays_compact_and_bounded() {
    let mut trace = ClauseTrace::new();
    let lit = Literal::positive(Variable(0));
    trace.add_clause_with_hints(1, vec![lit], false, vec![10, 11]);
    trace.add_clause_with_hints(2, vec![lit], false, vec![20]);
    trace.add_clause_with_hints(3, vec![lit], false, vec![30, 31]);

    for round in 0..64u64 {
        let replacement = match round % 3 {
            0 => vec![],
            1 => vec![100 + round],
            _ => vec![100 + round, 200 + round, 300 + round, 400 + round],
        };
        assert!(trace.set_resolution_hints(1, replacement.clone()));
        assert_eq!(trace.entries().at(0).resolution_hints, replacement);
        assert_eq!(trace.entries().at(1).resolution_hints, [20]);
        assert_eq!(trace.entries().at(2).resolution_hints, [30, 31]);

        let live_hint_count: usize = trace
            .entries()
            .iter()
            .map(|entry| entry.resolution_hints.len())
            .sum();
        assert_eq!(
            trace.hint_pool.len(),
            live_hint_count,
            "interior replacement retained unreachable hint payload at round {round}"
        );
    }

    let before = trace.entries().at(0).resolution_hints.to_vec();
    let pool_len_before = trace.hint_pool.len();
    trace.budget_bytes = trace.used_bytes();
    let mut over_budget = before.clone();
    over_budget.push(999);
    assert!(!trace.set_resolution_hints(1, over_budget));
    assert!(trace.is_truncated());
    assert_eq!(trace.entries().at(0).resolution_hints, before);
    assert_eq!(trace.hint_pool.len(), pool_len_before);
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
    let entry = trace.entries().at(0);
    assert_eq!(entry.id, 100);
    assert!(!entry.is_original);
    assert_eq!(entry.resolution_hints, vec![1, 2, 3]);

    // Empty clause with hints (level-0 conflict chain pattern)
    trace.add_clause_with_hints(101, vec![], false, vec![5, 6]);
    let empty_entry = trace.entries().at(1);
    assert_eq!(empty_entry.id, 101);
    assert!(empty_entry.clause.is_empty());
    assert_eq!(empty_entry.resolution_hints, vec![5, 6]);
    assert!(trace.has_empty_clause());
}

#[test]
fn clause_trace_used_bytes_is_exact_retained_capacity() {
    let mut trace = ClauseTrace::with_capacity(8);
    assert_eq!(trace.used_bytes(), retained_arena_bytes(&trace));
    assert!(trace.used_bytes() <= trace.budget_bytes);

    trace.add_clause_with_hints(
        1,
        vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        false,
        vec![7, 8, 9],
    );
    assert_eq!(trace.used_bytes(), retained_arena_bytes(&trace));

    let cloned = trace.clone();
    assert_eq!(cloned.used_bytes(), retained_arena_bytes(&cloned));
    assert!(cloned.used_bytes() <= cloned.budget_bytes);
}

/// The fifth payload needs three new five-slot vectors while all old four-slot
/// vectors remain live. One byte below that peak must reject without mutation;
/// the exact peak must admit without geometric over-allocation.
#[test]
fn clause_trace_add_respects_exact_capacity_boundary() {
    let lit = Literal::positive(Variable(0));
    let mut below = four_entry_trace();
    let peak = minimum_add_peak_bytes(&below, 1, 1);
    let before = below.entries_snapshot();
    let capacities = (
        below.meta.capacity(),
        below.lit_pool.capacity(),
        below.hint_pool.capacity(),
    );
    below.budget_bytes = peak - 1;
    below.add_clause_with_hints(5, vec![lit], false, vec![5]);
    assert_eq!(below.len(), before.len());
    for (actual, expected) in below.entries().iter().zip(&before) {
        assert_eq!(actual.id, expected.id);
        assert_eq!(actual.clause, expected.clause.as_slice());
        assert_eq!(
            actual.resolution_hints,
            expected.resolution_hints.as_slice()
        );
    }
    assert_eq!(
        capacities,
        (
            below.meta.capacity(),
            below.lit_pool.capacity(),
            below.hint_pool.capacity(),
        ),
        "failed admission must not retain a partial reservation"
    );
    assert!(below.is_truncated());

    let mut exact = four_entry_trace();
    let old_bytes = exact.used_bytes();
    exact.budget_bytes = peak;
    exact.add_clause_with_hints(5, vec![lit], false, vec![5]);
    assert_eq!(exact.len(), 5);
    assert!(!exact.is_truncated());
    assert_eq!(exact.used_bytes(), retained_arena_bytes(&exact));
    assert_eq!(old_bytes + exact.used_bytes(), peak);

    let capacities = (
        exact.meta.capacity(),
        exact.lit_pool.capacity(),
        exact.hint_pool.capacity(),
    );
    exact.add_clause_with_hints(6, vec![lit], false, vec![6]);
    assert_eq!(exact.len(), 5, "over-budget entry must not be visible");
    assert_eq!(
        capacities,
        (
            exact.meta.capacity(),
            exact.lit_pool.capacity(),
            exact.hint_pool.capacity(),
        )
    );
    assert!(exact.is_truncated());
    assert!(exact.used_bytes() <= exact.budget_bytes);
}

#[test]
fn clause_trace_hint_replacement_respects_exact_capacity_boundary() {
    let mut below = four_entry_trace();
    let peak = below.used_bytes() + 5 * size_of::<u64>();
    let before = below.entries_snapshot();
    let hint_capacity = below.hint_pool.capacity();
    below.budget_bytes = peak - 1;
    assert!(!below.set_resolution_hints(1, vec![10, 11]));
    for (actual, expected) in below.entries().iter().zip(&before) {
        assert_eq!(actual.id, expected.id);
        assert_eq!(
            actual.resolution_hints,
            expected.resolution_hints.as_slice()
        );
    }
    assert_eq!(below.hint_pool.capacity(), hint_capacity);
    assert!(below.is_truncated());

    let mut exact = four_entry_trace();
    let old_bytes = exact.used_bytes();
    exact.budget_bytes = peak;
    assert!(exact.set_resolution_hints(1, vec![10, 11]));
    assert_eq!(exact.entries().at(0).resolution_hints, [10, 11]);
    assert_eq!(
        old_bytes + exact.hint_pool.capacity() * size_of::<u64>(),
        peak
    );
    let before = exact.entries_snapshot();
    let hint_capacity = exact.hint_pool.capacity();

    assert!(!exact.set_resolution_hints(1, vec![10, 11, 12]));
    for (actual, expected) in exact.entries().iter().zip(&before) {
        assert_eq!(actual.id, expected.id);
        assert_eq!(
            actual.resolution_hints,
            expected.resolution_hints.as_slice()
        );
    }
    assert_eq!(exact.hint_pool.capacity(), hint_capacity);
    assert!(exact.is_truncated());
    assert!(exact.used_bytes() <= exact.budget_bytes);
}

#[test]
fn clause_trace_impossible_preallocation_fails_closed() {
    let trace = ClauseTrace::with_capacity(usize::MAX);
    assert!(trace.is_truncated());
    assert!(trace.is_empty());
    assert_eq!(trace.used_bytes(), 0);
    assert_eq!(trace.meta.capacity(), 0);
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
    assert!(trace.used_bytes() <= trace.budget_bytes);
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

    // The allocation-free UNSAT marker is preserved, but repeated over-budget
    // proof entries/payloads cannot grow any arena allocation.
    for id in 2..66 {
        trace.add_clause_with_hints(id, vec![], false, vec![id; 1024]);
    }
    assert_eq!(trace.len(), 0);
    assert_eq!(trace.used_bytes(), 0);
    assert_eq!(trace.meta.len(), 0);
    assert_eq!(trace.hint_pool.len(), 0);
    assert_eq!(trace.lit_pool.len(), 0);
    assert!(trace.has_empty_clause());
    assert!(trace.is_truncated());
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
    assert_eq!(trace.scope_assumptions(), Some([].as_slice()));
    assert_eq!(trace.clone().solver_num_vars(), Some(7));

    // Diagnostic counters do not change certificate content.
    trace.record_hint_lookup(None);
    assert_eq!(trace.solver_num_vars(), Some(7));

    trace.set_resolution_hints(1, vec![2]);
    assert_eq!(trace.solver_num_vars(), None);
    assert_eq!(trace.scope_assumptions(), None);

    trace.stamp_solver_num_vars(7);
    trace.mark_empty();
    assert_eq!(trace.solver_num_vars(), None);
}
