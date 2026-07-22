// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::expr::ChcVar;
use crate::ChcSort;

fn x_var() -> ChcExpr {
    ChcExpr::var(ChcVar::new("x".to_string(), ChcSort::Int))
}

fn y_var() -> ChcExpr {
    ChcExpr::var(ChcVar::new("y".to_string(), ChcSort::Int))
}

fn int(n: i128) -> ChcExpr {
    ChcExpr::Int(n)
}

#[test]
fn test_reach_solver_empty() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Empty solver returns false for any state
    assert!(!solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(0))));
}

#[test]
fn test_reach_solver_exact_match() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add x = 0
    solver.add(ChcExpr::eq(x_var(), int(0)));

    // x = 0 should be reachable
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(0))));

    // x = 5 should NOT be reachable
    assert!(!solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(5))));
}

#[test]
fn test_reach_solver_intersection() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add x >= 0 ∧ x < 10
    solver.add(ChcExpr::and(
        ChcExpr::ge(x_var(), int(0)),
        ChcExpr::lt(x_var(), int(10)),
    ));

    // x = 5 intersects [0, 10)
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(5))));

    // x = 15 does NOT intersect [0, 10)
    assert!(!solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(15))));

    // x >= 8 intersects [0, 10)
    assert!(solver.is_reachable(&mut smt, &ChcExpr::ge(x_var(), int(8))));

    // x >= 10 does NOT intersect [0, 10)
    assert!(!solver.is_reachable(&mut smt, &ChcExpr::ge(x_var(), int(10))));
}

#[test]
fn test_reach_solver_multiple_facts() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add x = 0
    solver.add(ChcExpr::eq(x_var(), int(0)));
    // Add x = 10
    solver.add(ChcExpr::eq(x_var(), int(10)));
    // Add x = 20
    solver.add(ChcExpr::eq(x_var(), int(20)));

    // All three values should be reachable
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(0))));
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(10))));
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(20))));

    // Other values should not be reachable
    assert!(!solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(5))));
    assert!(!solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(15))));
}

#[test]
fn test_reach_solver_store() {
    let mut store = ReachSolverStore::new();
    let mut smt = SmtContext::new();

    let pred1 = PredicateId(0);
    let pred2 = PredicateId(1);

    // Add facts for different predicates
    store.add(pred1, ChcExpr::eq(x_var(), int(0)));
    store.add(pred2, ChcExpr::eq(x_var(), int(100)));

    // pred1 has x=0 but not x=100
    assert!(store.is_reachable(&mut smt, pred1, &ChcExpr::eq(x_var(), int(0))));
    assert!(!store.is_reachable(&mut smt, pred1, &ChcExpr::eq(x_var(), int(100))));

    // pred2 has x=100 but not x=0
    assert!(!store.is_reachable(&mut smt, pred2, &ChcExpr::eq(x_var(), int(0))));
    assert!(store.is_reachable(&mut smt, pred2, &ChcExpr::eq(x_var(), int(100))));

    // Unknown predicate returns false
    let pred3 = PredicateId(2);
    assert!(!store.is_reachable(&mut smt, pred3, &ChcExpr::eq(x_var(), int(0))));
}

#[test]
fn test_reach_solver_store_caps_predicate_slots() {
    let mut store = ReachSolverStore::new();

    for i in 0..MAX_REACH_SOLVER_PREDICATES {
        store.add(
            PredicateId(u32::try_from(i).expect("predicate index should fit in u32")),
            ChcExpr::eq(x_var(), int(i as i128)),
        );
    }
    assert_eq!(
        store.solvers.len(),
        MAX_REACH_SOLVER_PREDICATES,
        "store should hold up to the predicate cap"
    );

    let overflow = PredicateId(
        u32::try_from(MAX_REACH_SOLVER_PREDICATES).expect("predicate cap should fit in u32"),
    );
    store.add(overflow, ChcExpr::eq(x_var(), int(999)));

    assert_eq!(
        store.solvers.len(),
        1,
        "adding a new predicate past cap should clear old slots first"
    );
    assert!(
        store.solvers.contains_key(&overflow),
        "store should retain the newest predicate after overflow clear"
    );
    assert!(
        !store.solvers.contains_key(&PredicateId(0)),
        "old predicate slots should be evicted on overflow"
    );
}

#[test]
fn test_reach_solver_two_variables() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add x = 0 ∧ y = 0
    solver.add(ChcExpr::and(
        ChcExpr::eq(x_var(), int(0)),
        ChcExpr::eq(y_var(), int(0)),
    ));

    // x = 0 ∧ y = 0 should be reachable
    assert!(solver.is_reachable(
        &mut smt,
        &ChcExpr::and(ChcExpr::eq(x_var(), int(0)), ChcExpr::eq(y_var(), int(0)),)
    ));

    // x = 0 (no constraint on y) should intersect
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(0))));

    // x = 0 ∧ y = 1 should NOT be reachable
    assert!(!solver.is_reachable(
        &mut smt,
        &ChcExpr::and(ChcExpr::eq(x_var(), int(0)), ChcExpr::eq(y_var(), int(1)),)
    ));
}

#[test]
fn test_find_match_returns_correct_reach_fact_id() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add two backed entries with distinct facts
    let rf_id_0 = ReachFactId(100);
    let rf_id_1 = ReachFactId(200);

    // Entry 0: x = 0
    solver.add_backed(rf_id_0, ChcExpr::eq(x_var(), int(0)));
    // Entry 1: x = 10
    solver.add_backed(rf_id_1, ChcExpr::eq(x_var(), int(10)));

    // Query state x = 0 should match rf_id_0
    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(0)));
    assert!(result.is_some());
    let (matched_id, _model) = result.unwrap();
    assert_eq!(matched_id, rf_id_0);

    // Query state x = 10 should match rf_id_1
    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(10)));
    assert!(result.is_some());
    let (matched_id, _model) = result.unwrap();
    assert_eq!(matched_id, rf_id_1);

    // Query state x = 5 should match nothing
    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(5)));
    assert!(result.is_none());
}

#[test]
fn test_find_match_model_marks_matching_tag_true() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    let rf_id_0 = ReachFactId(100);
    let rf_id_1 = ReachFactId(200);

    solver.add_backed(rf_id_0, ChcExpr::eq(x_var(), int(0)));
    solver.add_backed(rf_id_1, ChcExpr::eq(x_var(), int(10)));

    let (matched_id, model) = solver
        .find_match(&mut smt, &ChcExpr::eq(x_var(), int(10)))
        .expect("expected match");
    assert_eq!(matched_id, rf_id_1);

    // With tagged disjunction encoding, the matching tag must be true.
    // Non-matching tags may or may not be in the model (solver-dependent).
    let tag1 = solver.entries[1].tag.name.clone();
    assert_eq!(model.get(&tag1), Some(&SmtValue::Bool(true)));
}

#[test]
fn test_find_match_filter_only_entry_not_returned() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add a filter-only entry (no backing ID)
    solver.add(ChcExpr::eq(x_var(), int(0)));

    // is_reachable should return true
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(0))));

    // But find_match should return None (no backed entry)
    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(0)));
    assert!(result.is_none());
}

#[test]
fn test_find_match_mixed_backed_and_filter_only() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add filter-only entry for x = 0
    solver.add(ChcExpr::eq(x_var(), int(0)));

    // Add backed entry for x = 10
    let rf_id = ReachFactId(42);
    solver.add_backed(rf_id, ChcExpr::eq(x_var(), int(10)));

    // Query x = 0: reachable via filter-only, but `find_match` ignores filter-only entries.
    assert!(solver.is_reachable(&mut smt, &ChcExpr::eq(x_var(), int(0))));
    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(0)));
    assert!(result.is_none());

    // Query x = 10: backed entry, should return rf_id
    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(10)));
    assert!(result.is_some());
    let (matched_id, _model) = result.unwrap();
    assert_eq!(matched_id, rf_id);
}

#[test]
fn test_find_match_backed_over_filter_only_duplicate_fact() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    let fact = ChcExpr::eq(x_var(), int(0));
    solver.add(fact.clone());

    let rf_id = ReachFactId(42);
    solver.add_backed(rf_id, fact.clone());

    let result = solver.find_match(&mut smt, &fact);
    assert!(result.is_some());
    let (matched_id, _model) = result.unwrap();
    assert_eq!(matched_id, rf_id);
}

#[test]
fn test_reach_solver_store_find_match() {
    let mut store = ReachSolverStore::new();
    let mut smt = SmtContext::new();

    let pred = PredicateId(0);
    let rf_id = ReachFactId(999);

    // Add a backed entry
    store.add_backed(pred, rf_id, ChcExpr::eq(x_var(), int(42)));

    // find_match should return the ID
    let result = store.find_match(&mut smt, pred, &ChcExpr::eq(x_var(), int(42)));
    assert!(result.is_some());
    let (matched_id, _model) = result.unwrap();
    assert_eq!(matched_id, rf_id);

    // Unknown predicate returns None
    let pred2 = PredicateId(1);
    let result = store.find_match(&mut smt, pred2, &ChcExpr::eq(x_var(), int(42)));
    assert!(result.is_none());
}

#[test]
fn test_reach_solver_cap_evicts_filter_only_before_backed() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    solver.add_internal_with_cap(None, ChcExpr::eq(x_var(), int(0)), 2);
    solver.add_internal_with_cap(Some(ReachFactId(7)), ChcExpr::eq(x_var(), int(7)), 2);
    solver.add_internal_with_cap(None, ChcExpr::eq(x_var(), int(9)), 2);

    assert_eq!(solver.entries.len(), 2);
    assert_eq!(solver.entries.iter().filter(|e| e.id.is_some()).count(), 1);

    let result = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(7)));
    assert_eq!(result.map(|(id, _)| id), Some(ReachFactId(7)));
}

#[test]
fn test_reach_solver_cap_evicts_oldest_when_all_backed() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    solver.add_internal_with_cap(Some(ReachFactId(1)), ChcExpr::eq(x_var(), int(1)), 2);
    solver.add_internal_with_cap(Some(ReachFactId(2)), ChcExpr::eq(x_var(), int(2)), 2);
    solver.add_internal_with_cap(Some(ReachFactId(3)), ChcExpr::eq(x_var(), int(3)), 2);

    assert_eq!(solver.entries.len(), 2);

    let evicted = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(1)));
    assert!(
        evicted.is_none(),
        "oldest backed entry should be evicted once cap is exceeded"
    );

    let newest = solver.find_match(&mut smt, &ChcExpr::eq(x_var(), int(3)));
    assert_eq!(newest.map(|(id, _)| id), Some(ReachFactId(3)));
}

/// Regression test: find_match must NOT return a match when the POB state
/// uses an inequality (x < 0) against reach facts that are all non-negative.
/// This is the exact pattern that caused 7 PDR integration test failures:
/// PDR reported x < 0 as intersecting x = 5, which is impossible.
#[test]
fn test_find_match_inequality_does_not_match_disjoint_points() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Add backed entries for x = 5, 4, 3, 2, 1, 0 (all non-negative)
    for i in (0..=5).rev() {
        solver.add_backed(ReachFactId(i as usize), ChcExpr::eq(x_var(), int(i)));
    }

    // x < 0 should NOT intersect any of {0, 1, 2, 3, 4, 5}
    let result = solver.find_match(&mut smt, &ChcExpr::lt(x_var(), int(0)));
    assert!(
        result.is_none(),
        "x < 0 should not intersect reach facts x ∈ {{0,1,2,3,4,5}}, got {:?}",
        result.map(|(id, _)| id)
    );

    // x >= 0 should intersect (it matches all of them)
    let result = solver.find_match(&mut smt, &ChcExpr::ge(x_var(), int(0)));
    assert!(
        result.is_some(),
        "x >= 0 should intersect non-negative reach facts"
    );
}

/// Test that find_match with canonical variable names (__p0_a0) works correctly.
#[test]
fn test_find_match_canonical_var_inequality() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    let canon_var = || ChcExpr::var(ChcVar::new("__p0_a0".to_string(), ChcSort::Int));

    // Initial reach fact: __p0_a0 = 5
    solver.add_backed(ReachFactId(0), ChcExpr::eq(canon_var(), int(5)));

    // __p0_a0 < 0 should NOT intersect __p0_a0 = 5
    let result = solver.find_match(&mut smt, &ChcExpr::lt(canon_var(), int(0)));
    assert!(
        result.is_none(),
        "__p0_a0 < 0 should not intersect __p0_a0 = 5, got {:?}",
        result.map(|(id, _)| id)
    );
}

/// Regression test for the exact counter_unsafe false-positive bug:
/// When reach facts contain both non-matching (x=5) and matching (x=-1) entries,
/// find_match must return the CORRECT matching entry, not the first entry whose
/// don't-care tag happens to be true.
#[test]
fn test_find_match_returns_correct_entry_not_dont_care_tag() {
    let mut solver = ReachSolver::new();
    let mut smt = SmtContext::new();

    // Simulate counter_unsafe forward propagation: x=5, x=4, ..., x=0, x=-1
    for i in (0..=5).rev() {
        solver.add_backed(ReachFactId(100 + i as usize), ChcExpr::eq(x_var(), int(i)));
    }
    // x = -1 is the actually matching reach fact
    solver.add_backed(ReachFactId(200), ChcExpr::eq(x_var(), int(-1)));

    // x < 0 should match ReachFactId(200) (x=-1), NOT ReachFactId(105) (x=5)
    let result = solver.find_match(&mut smt, &ChcExpr::lt(x_var(), int(0)));
    assert!(result.is_some(), "x < 0 should intersect x = -1");
    let (rf_id, model) = result.unwrap();
    assert_eq!(
        rf_id,
        ReachFactId(200),
        "Expected ReachFactId(200) for x=-1, got {rf_id:?} with model {model:?}",
    );
}
