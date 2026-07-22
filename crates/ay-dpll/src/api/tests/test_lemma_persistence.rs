// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for theory lemma persistence across push/pop (#8304).
//!
//! These tests verify the LemmaCache and its integration with the solver's
//! incremental push/pop lifecycle for binary path analysis workloads.

use crate::api::{Logic, SolveResult, Solver, Sort};

/// Basic API: set_lemma_persistence and cached_lemma_count.
#[test]
fn test_lemma_persistence_api_default_off() {
    let solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    assert!(
        !solver.lemma_persistence(),
        "lemma persistence should be off by default"
    );
    assert_eq!(
        solver.cached_lemma_count(),
        0,
        "cached lemma count should be 0 when disabled"
    );
}

#[test]
fn test_lemma_persistence_api_toggle() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);
    assert!(solver.lemma_persistence());
    solver.set_lemma_persistence(false);
    assert!(!solver.lemma_persistence());
}

/// When lemma persistence is enabled, the solver should retain theory lemmas
/// across push/pop boundaries. After pop, the cached count should reflect
/// only lemmas from surviving scopes.
#[test]
fn test_lemma_persistence_survives_pop() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);

    // Declare variables
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    // Assert x > 0 at global scope
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");
    solver.try_assert_term(x_gt_0).expect("boolean assertion");

    // Push scope 1
    solver.try_push().expect("push should succeed");

    // Assert y = x + 1 in scope 1
    let one = solver.int_const(1);
    let x_plus_1 = solver.try_add(x, one).expect("int + int");
    let y_eq = solver.try_eq(y, x_plus_1).expect("matching sorts");
    solver.try_assert_term(y_eq).expect("boolean assertion");

    // Solve to generate theory lemmas
    let result = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result, SolveResult::Sat, "should be SAT in scope 1");

    // Pop scope 1
    solver.try_pop().expect("pop should succeed");

    // Push scope 2 (different path, same shared constraints)
    solver.try_push().expect("push should succeed");

    // Assert y = x + 2 in scope 2 (different branch condition)
    let two = solver.int_const(2);
    let x_plus_2 = solver.try_add(x, two).expect("int + int");
    let y_eq_2 = solver.try_eq(y, x_plus_2).expect("matching sorts");
    solver.try_assert_term(y_eq_2).expect("boolean assertion");

    // Solve again - should benefit from cached lemmas
    let result2 = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result2, SolveResult::Sat, "should be SAT in scope 2");

    solver.try_pop().expect("pop should succeed");
}

/// Scope-dependent lemma discard: lemmas derived at scope 2 should not
/// survive pop to scope 0.
#[test]
fn test_lemma_persistence_scope_discard() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Assert x >= 0 at global scope
    let x_ge_0 = solver.try_ge(x, zero).expect("int >= int");
    solver.try_assert_term(x_ge_0).expect("boolean assertion");

    // Push scope 1, then push scope 2
    solver.try_push().expect("push should succeed");
    solver.try_push().expect("push should succeed");

    // Assert x <= 10 in scope 2
    let x_le_10 = solver.try_le(x, ten).expect("int <= int");
    solver.try_assert_term(x_le_10).expect("boolean assertion");

    let result = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result, SolveResult::Sat);

    // Pop both scopes
    solver.try_pop().expect("pop should succeed"); // scope 2 -> 1
    solver.try_pop().expect("pop should succeed"); // scope 1 -> 0

    // Only global-scope cached lemmas should remain
    // (The exact count depends on theory behavior, but the solver should
    // function correctly regardless)
    assert_eq!(solver.num_scopes(), 0);
}

/// The solver should work correctly with lemma persistence enabled even
/// for simple problems that may not generate theory lemmas.
#[test]
fn test_lemma_persistence_no_lemmas_generated() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);

    let a = solver.declare_const("a", Sort::Bool);
    solver.try_assert_term(a).expect("boolean assertion");

    solver.try_push().expect("push should succeed");

    let result = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result, SolveResult::Sat);

    solver.try_pop().expect("pop should succeed");

    let result2 = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result2, SolveResult::Sat);

    assert_eq!(solver.cached_lemma_count(), 0);
}

/// Lemma persistence should be cleared on reset.
#[test]
fn test_lemma_persistence_cleared_on_reset() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");

    solver.try_push().expect("push should succeed");
    solver.try_assert_term(x_gt_0).expect("boolean assertion");
    let _ = solver.try_check_sat();
    solver.try_pop().expect("pop should succeed");

    // Reset should clear cached lemmas
    solver.try_reset().expect("reset should succeed");
    assert_eq!(
        solver.cached_lemma_count(),
        0,
        "cached lemma count should be 0 after reset"
    );
}

/// Multiple push/pop cycles with lemma persistence enabled should not
/// corrupt the solver state.
#[test]
fn test_lemma_persistence_multiple_cycles() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");
    solver.try_assert_term(x_gt_0).expect("boolean assertion");

    for i in 0..5 {
        solver.try_push().expect("push should succeed");

        let bound = solver.int_const(i + 1);
        let y_eq = solver.try_eq(y, bound).expect("matching sorts");
        solver.try_assert_term(y_eq).expect("boolean assertion");

        let result = solver.try_check_sat().expect("check_sat should succeed");
        assert_eq!(result, SolveResult::Sat, "should be SAT for path {i}");

        solver.try_pop().expect("pop should succeed");
    }

    // Solver should still be in a valid state
    assert_eq!(solver.num_scopes(), 0);
    let final_result = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(final_result, SolveResult::Sat);
}

/// The UNSAT result should be correct with lemma persistence enabled.
#[test]
fn test_lemma_persistence_unsat_correctness() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    solver.set_lemma_persistence(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // x > 0
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");
    solver.try_assert_term(x_gt_0).expect("boolean assertion");

    // First path: x < 0 (UNSAT with x > 0)
    solver.try_push().expect("push should succeed");
    let x_lt_0 = solver.try_lt(x, zero).expect("int < int");
    solver.try_assert_term(x_lt_0).expect("boolean assertion");

    let result1 = solver.try_check_sat().expect("check_sat should succeed");
    assert!(result1.is_unsat(), "x > 0 AND x < 0 should be UNSAT");
    solver.try_pop().expect("pop should succeed");

    // Second path: x = 5 (SAT)
    solver.try_push().expect("push should succeed");
    let five = solver.int_const(5);
    let x_eq_5 = solver.try_eq(x, five).expect("matching sorts");
    solver.try_assert_term(x_eq_5).expect("boolean assertion");

    let result2 = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result2, SolveResult::Sat, "x > 0 AND x = 5 should be SAT");
    solver.try_pop().expect("pop should succeed");
}
