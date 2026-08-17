// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-logic, stress, mixed-scope, and lemma-persistence CEGIS tests.

use super::*;

// =========================================================================
// Cross-logic validation: push/pop works with multiple logics
// =========================================================================

/// Confirms push/pop works with QF_BV (the primary EXTERNAL_CODEGEN logic).
#[test]
fn test_incremental_qf_bv() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    let x = solver.declare_const("x", Sort::bitvec(32));
    let zero = solver.bv_const(0, 32);

    solver.try_push().expect("push");
    let eq = solver.eq(x, zero);
    solver.try_assert_term(eq).expect("assert");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");

    // After pop, x == 0 is no longer asserted
    let one = solver.bv_const(1, 32);
    solver.try_push().expect("push 2");
    let eq2 = solver.eq(x, one);
    solver.try_assert_term(eq2).expect("assert x = 1");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop 2");
}

/// Confirms push/pop works with QF_ABV (arrays of bitvectors).
#[test]
fn test_incremental_qf_abv() {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("QF_ABV solver");
    let mem = solver.declare_const("mem", Sort::array(Sort::bitvec(32), Sort::bitvec(8)));
    let addr = solver.declare_const("addr", Sort::bitvec(32));

    solver.try_push().expect("push");
    let zero_addr = solver.bv_const(0, 32);
    let addr_eq = solver.eq(addr, zero_addr);
    solver.try_assert_term(addr_eq).expect("assert addr = 0");

    let val = solver.select(mem, addr);
    let forty_two = solver.bv_const(42, 8);
    let val_eq = solver.eq(val, forty_two);
    solver
        .try_assert_term(val_eq)
        .expect("assert mem[addr] = 42");

    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");

    // After pop, we can use a different address
    solver.try_push().expect("push 2");
    let one_addr = solver.bv_const(1, 32);
    let addr_eq2 = solver.eq(addr, one_addr);
    solver.try_assert_term(addr_eq2).expect("assert addr = 1");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop 2");
}

/// Confirms push/pop works with QF_LIA (integer arithmetic).
#[test]
fn test_incremental_qf_lia() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    let x = solver.declare_const("x", Sort::Int);

    solver.try_push().expect("push");
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("gt");
    solver.try_assert_term(x_gt_0).expect("assert x > 0");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");

    solver.try_push().expect("push 2");
    let neg = solver.int_const(-5);
    let x_eq_neg = solver.eq(x, neg);
    solver.try_assert_term(x_eq_neg).expect("assert x = -5");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop 2");
}

/// Confirms push/pop works with QF_LRA (real arithmetic).
#[test]
fn test_incremental_qf_lra() {
    let mut solver = Solver::try_new(Logic::QfLra).expect("QF_LRA solver");
    let x = solver.declare_const("x", Sort::Real);

    solver.try_push().expect("push");
    let half = solver.real_const(0.5);
    let x_eq = solver.eq(x, half);
    solver.try_assert_term(x_eq).expect("assert x = 0.5");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");
}

// =========================================================================
// Stress: many iterations without leaking state
// =========================================================================

/// Verifies that 100 push/pop cycles do not accumulate state.
///
/// This mirrors the EXTERNAL_CODEGEN use case of iterating over many candidates
/// in a synthesis loop.
#[test]
fn test_incremental_many_iterations_no_leak() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    let x = solver.declare_const("x", Sort::bitvec(8));

    for i in 0..100u8 {
        solver.try_push().expect("push");

        let val = solver.bv_const(i64::from(i), 8);
        let eq = solver.eq(x, val);
        solver.try_assert_term(eq).expect("assert x == i");

        let result = solver.try_check_sat().expect("check_sat");
        assert!(result.is_sat(), "x = {i} should always be SAT");

        if let Some(ModelValue::BitVec { value, .. }) = solver.value(x) {
            assert_eq!(value, BigInt::from(i), "model should match asserted value");
        }

        solver.try_pop().expect("pop");
    }

    assert_eq!(solver.num_scopes(), 0, "all 100 scopes cleaned up");
}

/// Verifies that 100 assumption-based iterations do not accumulate state.
#[test]
fn test_incremental_many_assumption_iterations() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    let x = solver.declare_const("x", Sort::bitvec(8));

    for i in 0..100u8 {
        let val = solver.bv_const(i64::from(i), 8);
        let eq = solver.eq(x, val);

        let result = solver.check_sat_assuming(&[eq]);
        assert!(result.is_sat(), "x = {i} should always be SAT");
    }

    assert_eq!(
        solver.num_scopes(),
        0,
        "assumptions should not alter scopes"
    );
}

// =========================================================================
// Combined: assumption within a pushed scope
// =========================================================================

/// Demonstrates mixing push/pop and assumptions in the same CEGIS loop.
///
/// Pattern: push a scope for the candidate's structural constraints,
/// then use assumptions for quick variant checks within that scope.
#[test]
fn test_cegis_push_pop_plus_assumptions() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));

    // Candidate: y = x + 1
    solver.try_push().expect("push for candidate");
    let one = solver.bv_const(1, 8);
    let x_plus_1 = solver.bvadd(x, one);
    let y_eq = solver.eq(y, x_plus_1);
    solver.try_assert_term(y_eq).expect("assert y = x + 1");

    // Quick assumption checks for specific inputs within this candidate
    let zero = solver.bv_const(0, 8);
    let x_eq_0 = solver.eq(x, zero);
    let result = solver.check_sat_assuming(&[x_eq_0]);
    assert!(result.is_sat(), "x=0 => y=1 should be SAT");
    if let Some(ModelValue::BitVec { value, .. }) = solver.value(y) {
        assert_eq!(value, BigInt::from(1), "y should be 1 when x is 0");
    }

    let max_val = solver.bv_const(0xFF, 8);
    let x_eq_max = solver.eq(x, max_val);
    let result2 = solver.check_sat_assuming(&[x_eq_max]);
    assert!(
        result2.is_sat(),
        "x=0xFF => y=0x00 should be SAT (wrapping)"
    );
    if let Some(ModelValue::BitVec { value, .. }) = solver.value(y) {
        assert_eq!(value, BigInt::from(0), "y should wrap to 0 when x is 0xFF");
    }

    solver.try_pop().expect("pop candidate");
    assert_eq!(solver.num_scopes(), 0);
}

// =========================================================================
// Lemma persistence across push/pop (advanced incremental feature)
// =========================================================================

/// Demonstrates enabling lemma persistence for incremental solving.
///
/// When the same theory lemmas apply across multiple candidates (common in
/// binary analysis where path constraints share most structure), enabling
/// lemma persistence avoids re-deriving them after each pop.
#[test]
fn test_cegis_lemma_persistence() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    solver.set_lemma_persistence(true);
    assert!(solver.lemma_persistence());

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    // Shared constraint: x + y > 10
    let ten = solver.int_const(10);
    let sum = solver.try_add(x, y).expect("add");
    let sum_gt_10 = solver.try_gt(sum, ten).expect("gt");
    solver
        .try_assert_term(sum_gt_10)
        .expect("assert x + y > 10");

    // First candidate: x = 5
    solver.try_push().expect("push");
    let five = solver.int_const(5);
    let x_eq_5 = solver.eq(x, five);
    solver.try_assert_term(x_eq_5).expect("assert x = 5");
    let result1 = solver.try_check_sat().expect("check");
    assert!(result1.is_sat(), "x=5, x+y>10 should be SAT (y > 5)");
    solver.try_pop().expect("pop");

    // Second candidate: x = 20
    solver.try_push().expect("push");
    let twenty = solver.int_const(20);
    let x_eq_20 = solver.eq(x, twenty);
    solver.try_assert_term(x_eq_20).expect("assert x = 20");
    let result2 = solver.try_check_sat().expect("check");
    assert!(result2.is_sat(), "x=20, x+y>10 should be SAT (y > -10)");
    solver.try_pop().expect("pop");

    // Lemmas from first solve may speed up subsequent solves
    // (no correctness assertion here -- it is a performance optimization)
    assert_eq!(solver.num_scopes(), 0);
}
