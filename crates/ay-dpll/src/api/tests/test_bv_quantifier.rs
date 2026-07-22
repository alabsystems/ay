// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for BV-specific quantifier instantiation (BV-MBQI, #8299).
//!
//! Validates that AY can solve quantified BV formulas using model-based
//! instantiation with boundary value heuristics. These formulas arise from
//! binary analysis memory safety properties.

use crate::api::*;

// =========================================================================
// Simple BV forall with model-based instantiation
// =========================================================================

/// forall x:BV8. x == x should be SAT (tautology).
#[test]
fn test_bv_forall_trivial_tautology() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let eq = solver.eq(x, x);
    let forall = solver.forall(&[x], eq);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(result.is_sat(), "forall x:BV8. x == x should be SAT");
}

/// forall x:BV8. x != x should be UNSAT (contradiction).
#[test]
fn test_bv_forall_trivial_contradiction() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let eq = solver.eq(x, x);
    let neq = solver.not(eq);
    let forall = solver.forall(&[x], neq);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(result.is_unsat(), "forall x:BV8. x != x should be UNSAT");
}

// =========================================================================
// Boundary value coverage (0, MAX)
// =========================================================================

/// forall x:BV8. bvule(0, x) should be SAT (always true: 0 <= x for all unsigned x).
#[test]
fn test_bv_forall_zero_le_x() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);
    let le = solver.bvule(zero, x);
    let forall = solver.forall(&[x], le);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(result.is_sat(), "forall x:BV8. 0 <= x should be SAT");
}

/// forall x:BV8. bvult(x, 255) should be UNSAT because x=255 falsifies it.
/// The BV-MBQI boundary heuristic should generate MAX (255) as a candidate.
#[test]
fn test_bv_forall_x_lt_max_is_unsat() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let max_val = solver.bv_const(0xFF, 8);
    let lt = solver.bvult(x, max_val);
    let forall = solver.forall(&[x], lt);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "forall x:BV8. bvult(x, 255) should be UNSAT (x=255 is counterexample)"
    );
}

/// forall x:BV8. bvule(x, 255) should be SAT (always true: x <= MAX).
#[test]
fn test_bv_forall_x_le_max_is_sat() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let max_val = solver.bv_const(0xFF, 8);
    let le = solver.bvule(x, max_val);
    let forall = solver.forall(&[x], le);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(result.is_sat(), "forall x:BV8. bvule(x, 255) should be SAT");
}

// =========================================================================
// Guard-filtered instantiation (using 8-bit BV to stay within solver limits)
// =========================================================================

/// forall ptr:BV8. (ptr == 10 => ptr == 10) should be SAT (trivially true).
/// Tests that guard pattern detection works with BV MBQI.
#[test]
fn test_bv_forall_guarded_trivial_implication() {
    let mut solver = Solver::new(Logic::All);

    let ptr = solver.fresh_var("ptr", Sort::bitvec(8));
    let ten = solver.bv_const(10, 8);

    let guard = solver.eq(ptr, ten);
    let body = solver.eq(ptr, ten);
    let implication = solver.implies(guard, body);
    let forall = solver.forall(&[ptr], implication);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "forall ptr:BV8. (ptr == 10 => ptr == 10) should be SAT"
    );
}

/// forall x:BV8. (bvult(x, 100) => bvult(x, 100)).
/// Trivially SAT — the guard implies itself.
#[test]
fn test_bv_forall_guard_self_implication() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let hundred = solver.bv_const(100, 8);

    let guard = solver.bvult(x, hundred);
    let body = solver.bvult(x, hundred);
    let implication = solver.implies(guard, body);
    let forall = solver.forall(&[x], implication);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "forall x:BV8. (x < 100 => x < 100) should be SAT"
    );
}

// =========================================================================
// Multi-variable quantifiers
// =========================================================================

/// forall x:BV8. forall y:BV8. bvsub(x, y) == bvsub(y, x) should be UNSAT
/// (subtraction is not commutative for most values).
/// The BV-MBQI boundary heuristic should find a counterexample (e.g., x=0, y=1).
#[test]
fn test_bv_forall_bvsub_not_commutative() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let y = solver.fresh_var("y", Sort::bitvec(8));

    let xy = solver.bvsub(x, y);
    let yx = solver.bvsub(y, x);
    let eq = solver.eq(xy, yx);

    // forall x, y. x - y == y - x (false in general)
    let forall = solver.forall(&[x, y], eq);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "forall x y:BV8. bvsub(x,y) == bvsub(y,x) should be UNSAT"
    );
}

/// forall x:BV8. bvadd(x, 0) == x should be SAT (identity element).
/// Tests that body constants (0) are extracted for instantiation.
#[test]
fn test_bv_forall_add_identity() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);

    let sum = solver.bvadd(x, zero);
    let eq = solver.eq(sum, x);
    let forall = solver.forall(&[x], eq);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "forall x:BV8. bvadd(x, 0) == x should be SAT (additive identity)"
    );
}

/// forall x:BV8. (x == 0 OR bvult(0, x)) should be SAT.
/// Every 8-bit value is either 0 or greater than 0.
#[test]
fn test_bv_forall_zero_or_positive() {
    let mut solver = Solver::new(Logic::All);

    let x = solver.fresh_var("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);

    let is_zero = solver.eq(x, zero);
    let is_positive = solver.bvult(zero, x);
    let disj = solver.or(is_zero, is_positive);
    let forall = solver.forall(&[x], disj);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "forall x:BV8. (x == 0 || 0 < x) should be SAT"
    );
}
