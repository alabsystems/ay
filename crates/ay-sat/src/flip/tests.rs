// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for flip-based local search.

use super::*;
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::walk::WalkFilter;

/// Helper: create a positive or negative literal from 1-indexed DIMACS variable.
fn lit(v: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable(v))
    } else {
        Literal::negative(Variable(v))
    }
}

/// Helper: build a clause arena from raw DIMACS-style clause data.
/// Variables are 1-indexed in DIMACS but 0-indexed internally, so we use
/// 0-indexed variables directly.
fn build_arena(clauses: &[&[Literal]]) -> ClauseArena {
    let mut arena = ClauseArena::new();
    for &clause in clauses {
        arena.add(clause, false);
    }
    arena
}

#[test]
fn test_flip_already_satisfying() {
    // Clauses: (x0) AND (x1) -- satisfied by phases [1, 1]
    let arena = build_arena(&[&[lit(0, true)], &[lit(1, true)]]);
    let mut phases = vec![1i8, 1];
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    let result = flip_search(&arena, 2, &mut phases, &mut stats, 1_000_000, filter);
    assert!(result, "should find satisfying assignment");
    assert_eq!(stats.best_unsat, 0);
}

#[test]
fn test_flip_improves_assignment() {
    // Clauses: (x0) AND (x1) AND (x2)
    // Initial phases: [-1, -1, -1] -- all unsatisfied.
    // Flip should improve by flipping all to positive.
    let arena = build_arena(&[&[lit(0, true)], &[lit(1, true)], &[lit(2, true)]]);
    let mut phases = vec![-1i8, -1, -1];
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    let result = flip_search(&arena, 3, &mut phases, &mut stats, 10_000_000, filter);
    assert!(result, "should find satisfying assignment for unit clauses");
    assert_eq!(stats.best_unsat, 0);
    // All phases should be positive.
    assert!(phases[0] > 0);
    assert!(phases[1] > 0);
    assert!(phases[2] > 0);
}

#[test]
fn test_flip_conflicting_clauses() {
    // Clauses: (x0) AND (-x0) -- unsatisfiable.
    // Flip should reduce unsat from 1 to 1 (can't do better).
    let arena = build_arena(&[&[lit(0, true)], &[lit(0, false)]]);
    let mut phases = vec![1i8];
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    let result = flip_search(&arena, 1, &mut phases, &mut stats, 1_000_000, filter);
    assert!(!result, "unsatisfiable formula should not be solved");
    assert_eq!(stats.best_unsat, 1);
}

#[test]
fn test_flip_empty_formula() {
    let arena = ClauseArena::new();
    let mut phases = vec![1i8; 3];
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    let result = flip_search(&arena, 3, &mut phases, &mut stats, 1_000_000, filter);
    assert!(result, "empty formula is trivially satisfiable");
}

#[test]
fn test_flip_stats_tracking() {
    let arena = build_arena(&[&[lit(0, true)], &[lit(1, false)]]);
    let mut phases = vec![-1i8, 1]; // x0 unsat, -x1 unsat
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    flip_search(&arena, 2, &mut phases, &mut stats, 10_000_000, filter);
    assert_eq!(stats.rounds, 1);
    assert!(stats.flips > 0, "should have performed some flips");
}

#[test]
fn test_flip_effort_computation() {
    // Zero delta: should return minimum.
    assert_eq!(compute_flip_effort(0), FLIP_MIN_EFFORT);

    // Small delta: should be at least minimum.
    assert!(compute_flip_effort(100) >= FLIP_MIN_EFFORT);

    // Large delta: should be capped at maximum.
    let huge = compute_flip_effort(u64::MAX / 2);
    assert!(huge <= FLIP_MAX_EFFORT * 1000);
}

#[test]
fn test_flip_three_sat_instance() {
    // A satisfiable 3-SAT instance with 4 variables.
    // (x0 OR x1 OR x2) AND (-x0 OR x2 OR x3) AND (x1 OR -x2 OR x3)
    let arena = build_arena(&[
        &[lit(0, true), lit(1, true), lit(2, true)],
        &[lit(0, false), lit(2, true), lit(3, true)],
        &[lit(1, true), lit(2, false), lit(3, true)],
    ]);
    let mut phases = vec![1i8, 1, 1, 1];
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    let result = flip_search(&arena, 4, &mut phases, &mut stats, 10_000_000, filter);
    // With initial phases [1,1,1,1]: clause 1 sat (x0), clause 2 sat (x2,x3),
    // clause 3 sat (x1,x3). So initial is already satisfying.
    assert!(result || stats.best_unsat == 0);
}

#[test]
fn test_flip_respects_tick_limit() {
    // Large formula with very small tick limit should return early.
    let mut clauses_storage: Vec<Vec<Literal>> = Vec::new();
    for i in 0..100u32 {
        clauses_storage.push(vec![lit(i, true), lit(i + 100, true), lit(i + 200, false)]);
    }
    let clause_refs: Vec<&[Literal]> = clauses_storage.iter().map(Vec::as_slice).collect();
    let arena = build_arena(&clause_refs);
    let mut phases = vec![-1i8; 300];
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    // Very small tick limit: should not crash, may not find optimal.
    let _result = flip_search(&arena, 300, &mut phases, &mut stats, 10, filter);
    // Just verify it doesn't panic and returns.
    assert_eq!(stats.rounds, 1);
}

#[test]
fn test_flip_multiple_rounds() {
    let arena = build_arena(&[
        &[lit(0, true), lit(1, true)],
        &[lit(0, false), lit(1, false)],
    ]);
    let mut phases = vec![1i8, 1]; // clause 2 is unsat
    let mut stats = FlipStats::default();
    let filter = WalkFilter::irredundant_only();

    // Run twice to verify stats accumulate.
    flip_search(&arena, 2, &mut phases, &mut stats, 10_000_000, filter);
    assert_eq!(stats.rounds, 1);

    flip_search(&arena, 2, &mut phases, &mut stats, 10_000_000, filter);
    assert_eq!(stats.rounds, 2);
}
