// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core tests for AY Solver API: types, terms, solving, arrays, datatypes, quantifiers.

use std::time::Duration;

use num_bigint::BigInt;

use crate::api::*;
use ay_core::{Symbol, TermData};

#[test]
fn test_basic_lia() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // x > 0 and x < 10
    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);
    let c2 = solver.lt(x, ten);
    solver.assert_term(c2);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_int_const_bigint_outside_i64_range() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let max = solver.int_const(i64::MAX);
    let big = BigInt::from(i64::MAX) + 1;
    let big_term = solver.int_const_bigint(&big);

    let eq1 = solver.eq(x, max);
    solver.assert_term(eq1);
    let eq2 = solver.eq(x, big_term);
    solver.assert_term(eq2);

    assert!(solver.check_sat().is_unsat());
}

#[test]
#[should_panic(expected = "sort mismatch in assert_term: expected Bool, got Int")]
fn test_assert_term_panics_on_non_bool() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    solver.assert_term(x);
}

#[test]
fn test_try_assert_term_rejects_non_bool() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let err = solver.try_assert_term(x).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "assert_term",
            expected: "Bool",
            got
        } if got == vec![Sort::Int]
    ));
}

#[test]
fn test_unsat() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // x > 0 and x < 0 is unsat
    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);
    let c2 = solver.lt(x, zero);
    solver.assert_term(c2);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_incremental() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);

    solver.push();
    let c2 = solver.lt(x, zero);
    solver.assert_term(c2);
    assert!(solver.check_sat().is_unsat());
    solver.pop();

    // After pop, should be sat again
    let c3 = solver.lt(x, ten);
    solver.assert_term(c3);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_implication() {
    // Simplified test: just a single implication
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let five = solver.int_const(5);

    // x = 5
    let x_eq_5 = solver.eq(x, five);
    solver.assert_term(x_eq_5);

    // x = 5 implies y = 5
    let y_eq_5 = solver.eq(y, five);
    let impl_term = solver.implies(x_eq_5, y_eq_5);
    solver.assert_term(impl_term);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_equality_constraints() {
    // Test equality constraints (simpler than full ReLU which needs disequality splits)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let z = solver.declare_const("z", Sort::Int);

    let five = solver.int_const(5);
    let ten = solver.int_const(10);

    // x = 5
    let x_eq_5 = solver.eq(x, five);
    solver.assert_term(x_eq_5);

    // y = x + 5 (i.e., y = 10)
    let x_plus_5 = solver.add(x, five);
    let y_eq = solver.eq(y, x_plus_5);
    solver.assert_term(y_eq);

    // z = y (i.e., z = 10)
    let z_eq_y = solver.eq(z, y);
    solver.assert_term(z_eq_y);

    // z = 10 (should be consistent)
    let z_eq_10 = solver.eq(z, ten);
    solver.assert_term(z_eq_10);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    assert_eq!(model.int_val_i64("x"), Some(5));
    assert_eq!(model.int_val_i64("y"), Some(10));
    assert_eq!(model.int_val_i64("z"), Some(10));
}

#[test]
fn test_lra_simple() {
    let mut solver = Solver::new(Logic::QfLra);

    let x = solver.declare_const("x", Sort::Real);
    let half = solver.rational_const(1, 2);
    let one = solver.real_const(1.0);

    // x > 0.5 and x < 1
    let c1 = solver.gt(x, half);
    solver.assert_term(c1);
    let c2 = solver.lt(x, one);
    solver.assert_term(c2);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_boolean_logic() {
    let mut solver = Solver::new(Logic::QfUf);

    let a = solver.declare_const("a", Sort::Bool);

    // a and (not a) is unsat
    solver.assert_term(a);
    let not_a = solver.not(a);
    solver.assert_term(not_a);

    assert!(solver.check_sat().is_unsat());

    solver.reset();

    // a or b, not a, not b is unsat
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let a_or_b = solver.or(a, b);
    solver.assert_term(a_or_b);
    let not_a = solver.not(a);
    solver.assert_term(not_a);
    let not_b = solver.not(b);
    solver.assert_term(not_b);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_distinct_simplify_duplicates() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);

    assert_eq!(solver.distinct(&[]), solver.bool_const(true));
    assert_eq!(solver.distinct(&[x]), solver.bool_const(true));
    assert_eq!(solver.distinct(&[x, x]), solver.bool_const(false));
}

#[test]
fn test_distinct_sat_unsat() {
    // UNSAT: x = 0, y = 0, distinct(x, y)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    let x_eq_0 = solver.eq(x, zero);
    solver.assert_term(x_eq_0);
    let y_eq_0 = solver.eq(y, zero);
    solver.assert_term(y_eq_0);
    let x_y_distinct = solver.distinct(&[x, y]);
    solver.assert_term(x_y_distinct);

    assert!(solver.check_sat().is_unsat());

    // SAT: x = 0, y = 1, z = 2, distinct(x, y, z)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let z = solver.declare_const("z", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    let x_eq_0 = solver.eq(x, zero);
    solver.assert_term(x_eq_0);
    let y_eq_1 = solver.eq(y, one);
    solver.assert_term(y_eq_1);
    let z_eq_2 = solver.eq(z, two);
    solver.assert_term(z_eq_2);
    let xyz_distinct = solver.distinct(&[x, y, z]);
    solver.assert_term(xyz_distinct);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_relu_encoding_qf_auflira() {
    // Test the ReLU encoding pattern from neural-verification-consumer's neural network verification
    // This uses QF_AUFLIRA (mixed Int+Real), which may return Unknown until
    // full Nelson-Oppen theory combination is implemented.
    //
    // ReLU encoding: y = max(0, x)
    // Uses binary phase variable p (0 or 1):
    //   - y >= 0
    //   - If p = 1: y = x (active phase)
    //   - If p = 0: y = 0 (inactive phase)

    let mut solver = Solver::new(Logic::QfAuflira);

    // Declare variables
    let x = solver.declare_const("x", Sort::Real);
    let y = solver.declare_const("y", Sort::Real);
    let p = solver.declare_const("p", Sort::Int);

    // p is binary: 0 <= p <= 1
    let zero_int = solver.int_const(0);
    let one_int = solver.int_const(1);
    let p_ge_0 = solver.ge(p, zero_int);
    let p_le_1 = solver.le(p, one_int);
    solver.assert_term(p_ge_0);
    solver.assert_term(p_le_1);

    // y >= 0 (ReLU output is non-negative)
    let zero_real = solver.real_const(0.0);
    let y_ge_0 = solver.ge(y, zero_real);
    solver.assert_term(y_ge_0);

    // When p = 1: y = x
    let p_eq_1 = solver.eq(p, one_int);
    let y_eq_x = solver.eq(y, x);
    let active_impl = solver.implies(p_eq_1, y_eq_x);
    solver.assert_term(active_impl);

    // When p = 0: y = 0
    let p_eq_0 = solver.eq(p, zero_int);
    let y_eq_0 = solver.eq(y, zero_real);
    let inactive_impl = solver.implies(p_eq_0, y_eq_0);
    solver.assert_term(inactive_impl);

    // Set x = 5.0 (positive input)
    let five = solver.real_const(5.0);
    let x_eq_5 = solver.eq(x, five);
    solver.assert_term(x_eq_5);

    // Check: This should be satisfiable with p=1, y=5
    let result = solver.check_sat();

    // Note: QF_AUFLIRA may return Unknown until full implementation
    // For now, we just verify no crash and document the behavior
    match result.result() {
        SolveResult::Sat => {
            // If we get SAT, verify the model makes sense
            if let Some(verified_model) = solver.model() {
                let model = verified_model.into_inner();
                // p should be 1 (active phase for positive x)
                if let Some(p_val) = model.int_val_i64("p") {
                    assert!(p_val == 0 || p_val == 1, "p should be binary");
                }
                // y should equal x when p=1, or 0 when p=0
                if let Some(y_val) = model.real_val_f64("y") {
                    assert!(y_val >= 0.0, "ReLU output should be non-negative");
                }
            }
        }
        SolveResult::Unknown => {
            // Expected until full QF_AUFLIRA is implemented
            // The solver correctly recognizes it cannot handle mixed Int+Real
        }
        SolveResult::Unsat(_) => {
            panic!("ReLU encoding should be satisfiable with x=5");
        }
    }
}

#[test]
fn test_pure_real_relu_qf_lra() {
    // Pure Real version of ReLU (no binary Int phase)
    // This uses QF_LRA which is fully supported
    //
    // Big-M encoding: y = max(0, x) with bounds
    // Assumptions: -M <= x <= M for some large M

    let mut solver = Solver::new(Logic::QfLra);

    let x = solver.declare_const("x", Sort::Real);
    let y = solver.declare_const("y", Sort::Real);

    let zero = solver.real_const(0.0);

    // y >= 0
    let y_ge_0 = solver.ge(y, zero);
    solver.assert_term(y_ge_0);

    // y >= x
    let y_ge_x = solver.ge(y, x);
    solver.assert_term(y_ge_x);

    // Set x = 5.0
    let five = solver.real_const(5.0);
    let x_eq_5 = solver.eq(x, five);
    solver.assert_term(x_eq_5);

    // Set y = x (for positive x, ReLU(x) = x)
    let y_eq_5 = solver.eq(y, five);
    solver.assert_term(y_eq_5);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    assert_eq!(model.real_val_f64("x"), Some(5.0));
    assert_eq!(model.real_val_f64("y"), Some(5.0));
}

#[test]
fn test_disequality_split_binary_int() {
    // Test P2.1: NeedDisequalitySplit handling for binary Int variables
    // When p ∈ {0, 1} and p != 0, should infer p = 1
    let mut solver = Solver::new(Logic::QfLia);

    let p = solver.declare_const("p", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // 0 <= p <= 1
    let p_ge_0 = solver.ge(p, zero);
    let p_le_1 = solver.le(p, one);
    solver.assert_term(p_ge_0);
    solver.assert_term(p_le_1);

    // p != 0 (should trigger disequality split)
    let p_neq_0 = solver.neq(p, zero);
    solver.assert_term(p_neq_0);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    assert_eq!(
        model.int_val_i64("p"),
        Some(1),
        "p should be 1 when p != 0 and p in [0, 1]"
    );
}

#[test]
// Fixed in c95763c4: Multi-reason bounds and n-ary distinct expansion
fn test_blocking_clauses_qf_lia_issue_294() {
    // Discriminating test for Issue #294: QF_LIA blocking clause soundness bug
    // This test MUST pass before #294 can be closed.
    //
    // The bug: Disequality splits accumulate globally, over-constraining the formula.
    // With blocking clauses (disjunctions of disequalities), satisfying ONE disjunct
    // should suffice, but the solver creates splits for ALL disequalities.
    //
    // Grid: x in [1,2], y in [1,2] = 4 points
    // Block: (1,1) and (2,2)
    // Valid: (1,2), (2,1) - MUST be SAT
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    // x in [1, 2]
    let x_ge_1 = solver.ge(x, one);
    let x_le_2 = solver.le(x, two);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_2);

    // y in [1, 2]
    let y_ge_1 = solver.ge(y, one);
    let y_le_2 = solver.le(y, two);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_2);

    // Block (1,1): at least one of x != 1 or y != 1
    let x_neq_1 = solver.neq(x, one);
    let y_neq_1 = solver.neq(y, one);
    let block_1_1 = solver.or(x_neq_1, y_neq_1);
    solver.assert_term(block_1_1);

    // Block (2,2): at least one of x != 2 or y != 2
    let x_neq_2 = solver.neq(x, two);
    let y_neq_2 = solver.neq(y, two);
    let block_2_2 = solver.or(x_neq_2, y_neq_2);
    solver.assert_term(block_2_2);

    // MUST be SAT: (1,2) and (2,1) are valid
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "BUG #294: Formula is SAT but solver returned UNSAT. Valid models: x=1,y=2 or x=2,y=1"
    );

    // Verify model is valid
    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    let x_val = model.int_val_i64("x").expect("x should be in model");
    let y_val = model.int_val_i64("y").expect("y should be in model");

    // Model must satisfy bounds
    assert!((1..=2).contains(&x_val), "x={x_val} out of bounds [1,2]");
    assert!((1..=2).contains(&y_val), "y={y_val} out of bounds [1,2]");

    // Model must not be (1,1) or (2,2)
    assert!(
        !(x_val == 1 && y_val == 1),
        "Model (1,1) violates first blocking clause"
    );
    assert!(
        !(x_val == 2 && y_val == 2),
        "Model (2,2) violates second blocking clause"
    );
}

#[test]
// Fixed in c95763c4: Multi-reason bounds and n-ary distinct expansion
fn test_diophantine_conflict_clause_issue_187() {
    // Discriminating test for Issue #187: Incomplete conflict clause from Diophantine solver
    // This test MUST pass before #187 can be closed.
    //
    // The bug: When the Diophantine solver determines variable values from multiple
    // equalities, it uses only the first equality as the reason for bounds.
    // This causes incomplete conflict clauses when those bounds conflict with
    // other constraints.
    //
    // Formula: (= D 1) AND ((= y 2) OR (= y 1)) AND (> y 1)
    // Expected: SAT with y=2 (satisfies (= y 2) and (> y 1))
    // Bug: The Diophantine solver solves (= D 1) and (= y 1) together,
    //      setting y=1 with reason=(= D 1) instead of (= y 1).
    //      When y=1 conflicts with (> y 1), the conflict clause is incomplete.
    let mut solver = Solver::new(Logic::QfLia);

    let d = solver.declare_const("D", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    // (= D 1)
    let d_eq_1 = solver.eq(d, one);
    solver.assert_term(d_eq_1);

    // (or (= y 2) (= y 1))
    let y_eq_2 = solver.eq(y, two);
    let y_eq_1 = solver.eq(y, one);
    let y_choice = solver.or(y_eq_2, y_eq_1);
    solver.assert_term(y_choice);

    // (> y 1)
    let y_gt_1 = solver.gt(y, one);
    solver.assert_term(y_gt_1);

    // MUST be SAT: y=2 satisfies all constraints
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "BUG #187: Formula is SAT but solver returned UNSAT. Valid model: D=1, y=2"
    );

    // Verify model is valid
    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    let d_val = model.int_val_i64("D").expect("D should be in model");
    let y_val = model.int_val_i64("y").expect("y should be in model");

    // D must be 1
    assert_eq!(d_val, 1, "D must equal 1");

    // y must be 2 (only valid value: satisfies (= y 2) and (> y 1))
    assert_eq!(
        y_val, 2,
        "y must equal 2 (only value satisfying (> y 1) from choice)"
    );
}

#[test]
fn test_relu_encoding_with_neq() {
    // Full ReLU encoding with explicit neq constraint
    // This tests the complete NeedDisequalitySplit flow in QF_AUFLIRA
    let mut solver = Solver::new(Logic::QfAuflira);

    let x = solver.declare_const("x", Sort::Real);
    let y = solver.declare_const("y", Sort::Real);
    let p = solver.declare_const("p", Sort::Int);

    let zero_int = solver.int_const(0);
    let one_int = solver.int_const(1);
    let zero_real = solver.real_const(0.0);
    let five = solver.real_const(5.0);

    // p is binary: 0 <= p <= 1
    let p_ge_0 = solver.ge(p, zero_int);
    solver.assert_term(p_ge_0);
    let p_le_1 = solver.le(p, one_int);
    solver.assert_term(p_le_1);

    // y >= 0 (ReLU output non-negative)
    let y_ge_0 = solver.ge(y, zero_real);
    solver.assert_term(y_ge_0);

    // When p = 1: y = x (active phase)
    let p_eq_1 = solver.eq(p, one_int);
    let y_eq_x = solver.eq(y, x);
    let active_impl = solver.implies(p_eq_1, y_eq_x);
    solver.assert_term(active_impl);

    // When p = 0: y = 0 (inactive phase)
    let p_eq_0 = solver.eq(p, zero_int);
    let y_eq_0 = solver.eq(y, zero_real);
    let inactive_impl = solver.implies(p_eq_0, y_eq_0);
    solver.assert_term(inactive_impl);

    // x = 5.0 (positive input)
    let x_eq_5 = solver.eq(x, five);
    solver.assert_term(x_eq_5);

    // Force p != 0 (should trigger disequality split and give p = 1)
    let p_neq_0 = solver.neq(p, zero_int);
    solver.assert_term(p_neq_0);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    assert_eq!(model.int_val_i64("p"), Some(1), "p should be 1 when p != 0");
    assert_eq!(
        model.real_val_f64("y"),
        Some(5.0),
        "y should equal x when p = 1"
    );
    assert_eq!(model.real_val_f64("x"), Some(5.0), "x should be 5.0");
}

#[test]
// Discriminating test for Issue #309: Multi-variable ALL-SAT enumeration
// model-checker consumer needs to enumerate all solutions in a 2x2 grid, finding 4 solutions.
//
// Note: Issue #309 is closed; this test keeps the simple "accumulating" style.
// See `test_allsat_with_pushpop_issue_1579` for a variant that uses push/pop
// between models.
fn test_allsat_enumeration_qf_lia_issue_309() {
    // Enumerate all (x,y) pairs where x in [1,2], y in [1,2]
    // Expected: 4 solutions - (1,1), (1,2), (2,1), (2,2)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    // x in [1, 2]
    let x_ge_1 = solver.ge(x, one);
    let x_le_2 = solver.le(x, two);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_2);

    // y in [1, 2]
    let y_ge_1 = solver.ge(y, one);
    let y_le_2 = solver.le(y, two);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_2);

    // Enumerate all solutions using incremental blocking clauses
    // (no push/pop - accumulate blocking clauses)
    let mut solutions: Vec<(i64, i64)> = Vec::new();

    loop {
        match solver.check_sat().result() {
            SolveResult::Sat => {}
            SolveResult::Unsat(_) => break,
            SolveResult::Unknown => {
                panic!("Unexpected Unknown while enumerating ALL-SAT models (Issue #309)")
            }
        }

        let model = solver.model().expect("Expected model").into_inner();
        let x_val = model.int_val_i64("x").expect("x should be in model");
        let y_val = model.int_val_i64("y").expect("y should be in model");

        // Verify model is valid
        assert!((1..=2).contains(&x_val), "x={x_val} out of bounds");
        assert!((1..=2).contains(&y_val), "y={y_val} out of bounds");

        // Verify not a duplicate
        assert!(
            !solutions.contains(&(x_val, y_val)),
            "Duplicate solution ({x_val}, {y_val})"
        );

        solutions.push((x_val, y_val));

        // Add blocking clause for this solution: x != x_val OR y != y_val
        let px = solver.int_const(x_val);
        let py = solver.int_const(y_val);
        let x_neq = solver.neq(x, px);
        let y_neq = solver.neq(y, py);
        let block = solver.or(x_neq, y_neq);
        solver.assert_term(block);

        // Safety limit
        assert!(
            solutions.len() <= 10,
            "Too many solutions found, likely infinite loop"
        );
    }

    // Sort for deterministic comparison
    solutions.sort_unstable();

    assert_eq!(
        solutions.len(),
        4,
        "Expected 4 solutions (2x2 grid), found {}: {:?}",
        solutions.len(),
        solutions
    );

    let expected = vec![(1, 1), (1, 2), (2, 1), (2, 2)];
    assert_eq!(
        solutions, expected,
        "Solutions don't match expected 2x2 grid"
    );
}

#[test]
// Discriminating test for Issue #938: ALL-SAT with arithmetic constraints
// This test reproduces the bug where adding blocking clauses to a formula
// with arithmetic constraints (like x + y = 5) incorrectly returns UNSAT.
fn test_allsat_enumeration_with_arithmetic_issue_938() {
    // Enumerate all (x,y) pairs where x in [1,4], y in [1,4], x + y = 5
    // Expected: 4 solutions - (1,4), (2,3), (3,2), (4,1)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let four = solver.int_const(4);
    let five = solver.int_const(5);

    // x in [1, 4]
    let x_ge_1 = solver.ge(x, one);
    let x_le_4 = solver.le(x, four);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_4);

    // y in [1, 4]
    let y_ge_1 = solver.ge(y, one);
    let y_le_4 = solver.le(y, four);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_4);

    // x + y = 5 (arithmetic constraint)
    let sum = solver.add(x, y);
    let sum_eq_5 = solver.eq(sum, five);
    solver.assert_term(sum_eq_5);

    // Enumerate all solutions using incremental blocking clauses
    let mut solutions: Vec<(i64, i64)> = Vec::new();

    loop {
        match solver.check_sat().result() {
            SolveResult::Sat => {}
            SolveResult::Unsat(_) => break,
            SolveResult::Unknown => {
                panic!("Unexpected Unknown while enumerating ALL-SAT models (Issue #938)")
            }
        }

        let model = solver.model().expect("Expected model").into_inner();
        let x_val = model.int_val_i64("x").expect("x should be in model");
        let y_val = model.int_val_i64("y").expect("y should be in model");

        // Verify model is valid
        assert!((1..=4).contains(&x_val), "x={x_val} out of bounds");
        assert!((1..=4).contains(&y_val), "y={y_val} out of bounds");
        assert_eq!(x_val + y_val, 5, "x + y must equal 5");

        // Verify not a duplicate
        assert!(
            !solutions.contains(&(x_val, y_val)),
            "Duplicate solution ({x_val}, {y_val})"
        );

        solutions.push((x_val, y_val));

        // Add blocking clause for this solution: x != x_val OR y != y_val
        let px = solver.int_const(x_val);
        let py = solver.int_const(y_val);
        let x_eq_px = solver.eq(x, px);
        let y_eq_py = solver.eq(y, py);
        let x_neq = solver.not(x_eq_px);
        let y_neq = solver.not(y_eq_py);
        let block = solver.or(x_neq, y_neq);
        solver.assert_term(block);

        // Safety limit
        assert!(
            solutions.len() <= 10,
            "Too many solutions found, likely infinite loop"
        );
    }

    // Sort for deterministic comparison
    solutions.sort_unstable();

    assert_eq!(
        solutions.len(),
        4,
        "Expected 4 solutions for x + y = 5 with x,y in [1,4], found {}: {:?}",
        solutions.len(),
        solutions
    );

    let expected = vec![(1, 4), (2, 3), (3, 2), (4, 1)];
    assert_eq!(
        solutions, expected,
        "Solutions don't match expected for x + y = 5"
    );
}

#[test]
// Discriminating test for Issue #309: push/pop after check-sat fails
// This is the root cause of the ALL-SAT enumeration bug.
fn test_pushpop_after_checksat_issue_309() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    // x in [1, 2]
    let x_ge_1 = solver.ge(x, one);
    let x_le_2 = solver.le(x, two);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_2);

    // y in [1, 2]
    let y_ge_1 = solver.ge(y, one);
    let y_le_2 = solver.le(y, two);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_2);

    // First check - should be SAT
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    let model1 = solver.model().expect("Expected model").into_inner();
    let x1 = model1.int_val_i64("x").expect("x");
    let y1 = model1.int_val_i64("y").expect("y");

    // Push, add blocking clause, check again
    solver.push();
    let px = solver.int_const(x1);
    let py = solver.int_const(y1);
    let x_neq = solver.neq(x, px);
    let y_neq = solver.neq(y, py);
    let block = solver.or(x_neq, y_neq);
    solver.assert_term(block);

    // Fixed: This previously returned Unknown instead of Sat (issue #309)
    let result2 = solver.check_sat();
    assert_eq!(
        result2,
        SolveResult::Sat,
        "push/pop after check-sat should still find solutions. \
         First solution was ({x1}, {y1}), blocking it should find another."
    );
}

#[test]
// Issue #1579: Verify ALL-SAT enumeration works with incremental push/pop.
//
// Each iteration: check-sat → push → assert blocking clause → check-sat → pop
// → assert blocking clause (permanently).
fn test_allsat_with_pushpop_issue_1579() {
    // Enumerate all (x,y) pairs where x in [1,2], y in [1,2]
    // Expected: 4 solutions - (1,1), (1,2), (2,1), (2,2)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    // x in [1, 2]
    let x_ge_1 = solver.ge(x, one);
    let x_le_2 = solver.le(x, two);
    solver.assert_term(x_ge_1);
    solver.assert_term(x_le_2);

    // y in [1, 2]
    let y_ge_1 = solver.ge(y, one);
    let y_le_2 = solver.le(y, two);
    solver.assert_term(y_ge_1);
    solver.assert_term(y_le_2);

    let expected = vec![(1, 1), (1, 2), (2, 1), (2, 2)];
    let expected_count = expected.len();

    // Enumerate all solutions by permanently accumulating blocking clauses at
    // the base level, but exercising push/pop around each blocking clause.
    let mut solutions: Vec<(i64, i64)> = Vec::new();

    loop {
        match solver.check_sat().result() {
            SolveResult::Sat => {}
            SolveResult::Unsat(_) => break,
            SolveResult::Unknown => panic!(
                "Unexpected Unknown while enumerating ALL-SAT models (solutions so far: {solutions:?})"
            ),
        }

        let model = solver.model().expect("Expected model").into_inner();
        let x_val = model.int_val_i64("x").expect("x should be in model");
        let y_val = model.int_val_i64("y").expect("y should be in model");

        // Verify model is valid
        assert!((1..=2).contains(&x_val), "x={x_val} out of bounds");
        assert!((1..=2).contains(&y_val), "y={y_val} out of bounds");

        // Verify not a duplicate
        assert!(
            !solutions.contains(&(x_val, y_val)),
            "Duplicate solution ({x_val}, {y_val})"
        );

        solutions.push((x_val, y_val));

        // Add blocking clause (x != x_val OR y != y_val) via push/pop, then
        // assert it permanently at the base level.
        solver.push();
        let px = solver.int_const(x_val);
        let py = solver.int_const(y_val);
        let x_neq = solver.neq(x, px);
        let y_neq = solver.neq(y, py);
        let block = solver.or(x_neq, y_neq);
        solver.assert_term(block);

        let pushed_result = solver.check_sat();
        let expected_pushed_result = if solutions.len() < expected_count {
            SolveResult::Sat
        } else {
            SolveResult::unsat()
        };
        if pushed_result != expected_pushed_result {
            solver.pop();
            panic!(
                "Unexpected result after push+block: expected {expected_pushed_result:?} but got {pushed_result:?} (blocked model: ({x_val}, {y_val}), solutions so far: {solutions:?})"
            );
        }
        solver.pop();
        solver.assert_term(block);

        // Safety limit
        assert!(
            solutions.len() <= expected_count,
            "Too many solutions found, expected {expected_count} but found {solutions:?}"
        );
    }

    // Sort for deterministic comparison
    solutions.sort_unstable();

    assert_eq!(
        solutions.len(),
        4,
        "Expected 4 solutions (2x2 grid), found {}: {:?}",
        solutions.len(),
        solutions
    );

    assert_eq!(
        solutions, expected,
        "Solutions don't match expected 2x2 grid"
    );
}

// =========================================================================
// FuncDecl and apply tests (#589)
// =========================================================================

#[test]
fn test_euf_uninterpreted_function() {
    // Declare f: Int → Int, assert f(x) = f(y) and x != y
    // EUF allows non-injective functions, so this should be SAT
    let mut solver = Solver::new(Logic::QfUf);

    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let fx = solver.apply(&f, &[x]);
    let fy = solver.apply(&f, &[y]);
    let eq = solver.eq(fx, fy);
    solver.assert_term(eq);

    let neq = solver.neq(x, y);
    solver.assert_term(neq);

    // Should be SAT: f can map both x and y to the same value
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_euf_binary_function() {
    // Declare f: Int × Int → Bool, test basic usage
    let mut solver = Solver::new(Logic::QfUf);

    let f = solver.declare_fun("f", &[Sort::Int, Sort::Int], Sort::Bool);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let fxy = solver.apply(&f, &[x, y]);
    solver.assert_term(fxy);

    let fyx = solver.apply(&f, &[y, x]);
    let not_fyx = solver.not(fyx);
    solver.assert_term(not_fyx);

    // Should be SAT: uninterpreted function can have arbitrary behavior
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn native_ufs_named_like_builtins_keep_private_core_identity() {
    let mut solver = Solver::new(Logic::All);
    let seven = solver.int_const(7);
    let minus_two = solver.int_const(-2);

    let user_rem = solver.declare_fun("rem", &[Sort::Int, Sort::Int], Sort::Int);
    let user_rem_again = solver.declare_fun("rem", &[Sort::Int, Sort::Int], Sort::Int);
    assert_eq!(
        user_rem, user_rem_again,
        "idempotent declaration lost identity"
    );
    assert_eq!(user_rem.name(), "rem");
    assert_ne!(user_rem.core_name(), "rem");
    let rem_application = solver.apply(&user_rem, &[seven, minus_two]);
    let TermData::App(Symbol::Named(rem_identity), _) = solver.terms().get(rem_application.id())
    else {
        panic!("native UF application must be a named application");
    };
    assert_eq!(rem_identity, user_rem.core_name());

    // If the proof evaluator confused this UF with integer `rem`, it would
    // accept the non-theorem below as a closed arithmetic truth.
    let minus_one = solver.int_const(-1);
    let forged_rem_value = solver.eq(rem_application, minus_one);
    assert!(!ay_proof::recognize_ground_evaluate(
        solver.terms(),
        forged_rem_value.id()
    ));

    let user_equality = solver.declare_fun("=", &[Sort::Int, Sort::Int], Sort::Bool);
    assert_eq!(user_equality.name(), "=");
    assert_ne!(user_equality.core_name(), "=");
    let equality_application = solver.apply(&user_equality, &[seven, minus_two]);
    let TermData::App(Symbol::Named(equality_identity), _) =
        solver.terms().get(equality_application.id())
    else {
        panic!("native UF application must be a named application");
    };
    assert_eq!(equality_identity, user_equality.core_name());
    assert!(!ay_proof::recognize_ground_evaluate(
        solver.terms(),
        equality_application.id()
    ));

    // Both assertions are satisfiable for free functions. Reusing either
    // surface spelling as builtin core identity would instead force
    // `rem(7, -2) = -1` and builtin equality on unequal arguments, making
    // this query spuriously UNSAT.
    let zero = solver.int_const(0);
    let rem_is_zero = solver.eq(rem_application, zero);
    solver.assert_term(rem_is_zero);
    solver.assert_term(equality_application);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

/// Regression test for verification-consumer issue #6498: nullary UF functions declared via
/// `declare_fun` with empty domain should return SAT when unconstrained,
/// not Unknown. The bug was that nullary UF applications were not detected
/// as UF by StaticFeatures, causing incorrect logic narrowing (AUFLIA → LIA)
/// which stripped UF support and broke model validation for UF terms.
#[test]
fn test_nullary_uf_function_sat_6498() {
    // Reproduces verification-consumer's `register_opaque_logic_fn_skips_defining_axiom` test:
    // declare an unconstrained nullary function, assert it != 42, expect SAT.
    let mut solver = Solver::new(Logic::Auflia);
    let f = solver.declare_fun("logic_secret", &[], Sort::Int);
    let call = solver.apply(&f, &[]);
    let forty_two = solver.int_const(42);
    let eq = solver.eq(call, forty_two);
    let neq = solver.not(eq);
    solver.assert_term(neq);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "Unconstrained nullary UF should be SAT, not Unknown"
    );
}

/// Regression test for verification-consumer issue #6498: nullary UF with extra assertions
/// (reproduces `default_mode_verification_fails` pattern).
#[test]
fn test_nullary_uf_with_extra_assertion_sat_6498() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let f = solver.declare_fun("logic_answer", &[], Sort::Int);
    let call = solver.apply(&f, &[]);
    let result = solver.declare_const("result", Sort::Int);
    let zero = solver.int_const(0);
    let result_eq_body = solver.eq(result, zero);
    solver.assert_term(result_eq_body);
    let forty_two = solver.int_const(42);
    let postcond = solver.eq(call, forty_two);
    let neg_postcond = solver.not(postcond);
    solver.assert_term(neg_postcond);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "Nullary UF + extra constraint should be SAT, not Unknown"
    );
}

/// Regression test for verification-consumer issue #6498 test 1: Seq(Int) equality under
/// QF_AUFLIA should redirect to the Seq solver instead of returning Unknown.
#[test]
fn test_seq_equality_under_auflia_sat_6498() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let s = solver.declare_const("s", Sort::Seq(Box::new(Sort::Int)));
    let coerced = solver.declare_const("coerced", Sort::Seq(Box::new(Sort::Int)));
    let eq = solver.eq(coerced, s);
    solver.assert_term(eq);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "Seq equality under QF_AUFLIA should be SAT, not Unknown"
    );
}

#[test]
fn test_funcdecl_accessors() {
    let mut solver = Solver::new(Logic::QfUf);
    let f = solver.declare_fun("my_func", &[Sort::Int, Sort::Bool], Sort::Real);

    assert_eq!(f.name(), "my_func");
    assert_eq!(f.arity(), 2);
    assert_eq!(f.domain(), &[Sort::Int, Sort::Bool]);
    assert_eq!(f.range(), &Sort::Real);
}

#[test]
#[should_panic(expected = "invalid argument to apply: function f expects 1 args, got 0")]
fn test_apply_wrong_arity_panics_at_runtime() {
    let mut solver = Solver::new(Logic::QfUf);
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);

    let _ = solver.apply(&f, &[]);
}

// =========================================================================
// Array operation tests (#588)
// =========================================================================

#[test]
fn test_array_select_store() {
    // Basic array select/store: select(store(a, i, v), i) = v
    let mut solver = Solver::new(Logic::QfAuflia);

    let arr = solver.declare_const("a", Sort::array(Sort::Int, Sort::Int));
    let i = solver.declare_const("i", Sort::Int);
    let one = solver.int_const(1);

    let stored = solver.store(arr, i, one);
    let selected = solver.select(stored, i);
    let eq = solver.eq(selected, one);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_const_array() {
    // const_array creates an array where all elements equal the default
    let mut solver = Solver::new(Logic::QfAuflia);

    let zero = solver.int_const(0);
    let arr = solver.const_array(Sort::Int, zero);

    let i = solver.declare_const("i", Sort::Int);
    let selected = solver.select(arr, i);
    let eq = solver.eq(selected, zero);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_sort_array_nested() {
    // Test nested array sorts: Array(Int, Array(Int, Bool))
    let mut solver = Solver::new(Logic::QfAuflia);

    let inner_sort = Sort::array(Sort::Int, Sort::Bool);
    let outer_sort = Sort::array(Sort::Int, inner_sort);

    let arr = solver.declare_const("nested_arr", outer_sort);
    let idx1 = solver.int_const(0);

    let inner = solver.select(arr, idx1);
    let val = solver.select(inner, idx1);

    solver.assert_term(val);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_sort_uninterpreted() {
    // Test uninterpreted sorts
    let mut solver = Solver::new(Logic::QfUf);

    let u = solver.declare_const("u", Sort::Uninterpreted("MySort".to_string()));
    let v = solver.declare_const("v", Sort::Uninterpreted("MySort".to_string()));

    let eq = solver.eq(u, v);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

// =========================================================================
// Quantified logic tests (#582)
// =========================================================================

#[test]
fn test_quantified_logic_uf() {
    // UF logic should accept the logic setting without error
    // (Quantifier construction requires forall/exists methods)
    let mut solver = Solver::new(Logic::Uf);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let eq = solver.eq(x, y);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_quantified_logic_lia() {
    // LIA logic for quantified linear integer arithmetic
    let mut solver = Solver::new(Logic::Lia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // x >= 0 and x <= 1
    let c1 = solver.ge(x, zero);
    let c2 = solver.le(x, one);
    solver.assert_term(c1);
    solver.assert_term(c2);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_quantified_logic_uflia() {
    // UFLIA: Quantified UF + LIA
    let mut solver = Solver::new(Logic::Uflia);

    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let fx = solver.apply(&f, &[x]);
    let fy = solver.apply(&f, &[y]);
    let eq = solver.eq(fx, fy);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

/// Quantified LIRA logic: mixed integer and real arithmetic with quantifiers (#5888).
/// Previously returned Unknown because LIRA was not in from_logic mapping.
#[test]
fn test_quantified_logic_lira() {
    let mut solver = Solver::new(Logic::Lira);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Real);
    let zero_int = solver.int_const(0);
    let zero_real = solver.real_const(0.0);

    // x >= 0 and y >= 0.0
    let c1 = solver.ge(x, zero_int);
    let c2 = solver.ge(y, zero_real);
    solver.assert_term(c1);
    solver.assert_term(c2);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
}

#[test]
fn test_uflia_ground_unsat_with_unrelated_forall_axiom_2829() {
    let mut solver = Solver::new(Logic::Uflia);

    let i = solver.declare_const("i", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let ten = solver.int_const(10);

    // Ground constraints:
    // i >= 0 /\ i < 10 /\ i' = i + 1 /\ not(i' >= 0)
    let i_ge_zero = solver.ge(i, zero);
    solver.assert_term(i_ge_zero);
    let i_lt_ten = solver.lt(i, ten);
    solver.assert_term(i_lt_ten);
    let i_plus_one = solver.add(i, one);
    let ip_eq_i_plus_one = solver.eq(i_prime, i_plus_one);
    solver.assert_term(ip_eq_i_plus_one);
    let ip_ge_zero = solver.ge(i_prime, zero);
    let not_ip_ge_zero = solver.not(ip_ge_zero);
    solver.assert_term(not_ip_ge_zero);

    // Unrelated quantified axiom: forall x. dummy(x) = x
    let dummy = solver.declare_fun("logic_dummy", &[Sort::Int], Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let dummy_x = solver.apply(&dummy, &[x]);
    let axiom_body = solver.eq(dummy_x, x);
    let axiom = solver.forall_with_triggers(&[x], axiom_body, &[&[dummy_x]]);
    solver.assert_term(axiom);

    // Ground arithmetic contradiction must remain UNSAT.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_uflia_ground_unsat_with_referenced_forall_axiom_2829() {
    let mut solver = Solver::new(Logic::Uflia);

    let i = solver.declare_const("i", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Ground constraints:
    // i >= 0 /\ i < 10 /\ i' = double(i) /\ not(i' >= 0)
    let i_ge_zero = solver.ge(i, zero);
    solver.assert_term(i_ge_zero);
    let i_lt_ten = solver.lt(i, ten);
    solver.assert_term(i_lt_ten);

    let double = solver.declare_fun("double", &[Sort::Int], Sort::Int);
    let double_i = solver.apply(&double, &[i]);
    let ip_eq_double_i = solver.eq(i_prime, double_i);
    solver.assert_term(ip_eq_double_i);

    let ip_ge_zero = solver.ge(i_prime, zero);
    let not_ip_ge_zero = solver.not(ip_ge_zero);
    solver.assert_term(not_ip_ge_zero);

    // Referenced quantified axiom: forall x. double(x) = x + x
    // Trigger ensures E-matching can instantiate on ground term double(i).
    let x = solver.fresh_var("x", Sort::Int);
    let double_x = solver.apply(&double, &[x]);
    let x_plus_x = solver.add(x, x);
    let axiom_body = solver.eq(double_x, x_plus_x);
    let axiom = solver.forall_with_triggers(&[x], axiom_body, &[&[double_x]]);
    solver.assert_term(axiom);

    // With i >= 0 and double(i) = i + i, i' cannot be negative.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_uflia_logic_double_loop_preservation_unsat_7884() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let i = solver.declare_const("i", Sort::Int);
    let acc = solver.declare_const("acc", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let acc_prime = solver.declare_const("acc_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    let double = solver.declare_fun("logic_double", &[Sort::Int], Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let double_x = solver.apply(&double, &[x]);
    let x_plus_x = solver.add(x, x);
    let axiom_body = solver.eq(double_x, x_plus_x);
    let axiom = solver.forall_with_triggers(&[x], axiom_body, &[&[double_x]]);
    solver.assert_term(axiom);

    let double_i = solver.apply(&double, &[i]);
    let acc_eq_double_i = solver.eq(acc, double_i);
    solver.assert_term(acc_eq_double_i);
    let i_lt_n = solver.lt(i, n);
    solver.assert_term(i_lt_n);
    let i_ge_zero = solver.ge(i, zero);
    solver.assert_term(i_ge_zero);

    let i_plus_one = solver.add(i, one);
    let ip_eq_i_plus_one = solver.eq(i_prime, i_plus_one);
    solver.assert_term(ip_eq_i_plus_one);

    let acc_plus_two = solver.add(acc, two);
    let accp_eq_acc_plus_two = solver.eq(acc_prime, acc_plus_two);
    solver.assert_term(accp_eq_acc_plus_two);

    let double_i_prime = solver.apply(&double, &[i_prime]);
    let preserved = solver.eq(acc_prime, double_i_prime);
    let not_preserved = solver.not(preserved);
    solver.assert_term(not_preserved);

    // verification-consumer v0.2.0 loop-preservation repro from #7884.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_uflia_logic_double_minimal_preservation_unsat_7884() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let i = solver.declare_const("i", Sort::Int);
    let acc = solver.declare_const("acc", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let acc_prime = solver.declare_const("acc_prime", Sort::Int);
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    let double = solver.declare_fun("logic_double", &[Sort::Int], Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let double_x = solver.apply(&double, &[x]);
    let x_plus_x = solver.add(x, x);
    let axiom_body = solver.eq(double_x, x_plus_x);
    let axiom = solver.forall_with_triggers(&[x], axiom_body, &[&[double_x]]);
    solver.assert_term(axiom);

    let double_i = solver.apply(&double, &[i]);
    let acc_eq_double_i = solver.eq(acc, double_i);
    solver.assert_term(acc_eq_double_i);

    let i_plus_one = solver.add(i, one);
    let ip_eq_i_plus_one = solver.eq(i_prime, i_plus_one);
    solver.assert_term(ip_eq_i_plus_one);

    let acc_plus_two = solver.add(acc, two);
    let accp_eq_acc_plus_two = solver.eq(acc_prime, acc_plus_two);
    solver.assert_term(accp_eq_acc_plus_two);

    let double_i_prime = solver.apply(&double, &[i_prime]);
    let preserved = solver.eq(acc_prime, double_i_prime);
    let not_preserved = solver.not(preserved);
    solver.assert_term(not_preserved);

    // Minimal UFLIA preservation boundary from #7884.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_uflia_ground_unsat_with_arith_forall_is_not_sat_2829() {
    let mut solver = Solver::new(Logic::Uflia);

    let i = solver.declare_const("i", Sort::Int);
    let i_prime = solver.declare_const("i_prime", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let ten = solver.int_const(10);

    // Ground contradiction.
    let i_ge_zero = solver.ge(i, zero);
    solver.assert_term(i_ge_zero);
    let i_lt_ten = solver.lt(i, ten);
    solver.assert_term(i_lt_ten);
    let i_plus_one = solver.add(i, one);
    let ip_eq_i_plus_one = solver.eq(i_prime, i_plus_one);
    solver.assert_term(ip_eq_i_plus_one);
    let ip_ge_zero = solver.ge(i_prime, zero);
    let not_ip_ge_zero = solver.not(ip_ge_zero);
    solver.assert_term(not_ip_ge_zero);

    // Arithmetic forall that CEGQI handles: forall x. x >= x
    let x = solver.fresh_var("x", Sort::Int);
    let x_ge_x = solver.ge(x, x);
    let axiom = solver.forall(&[x], x_ge_x);
    solver.assert_term(axiom);

    // Ground contradiction must not be flipped to SAT by CEGQI result mapping.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_uflia_cegqi_forall_counterexample_not_sat_with_other_ematch_2829() {
    let mut solver = Solver::new(Logic::Uflia);

    // Ground UF term to trigger E-matching on the UF axiom below.
    let c = solver.declare_const("c", Sort::Int);
    let id = solver.declare_fun("id", &[Sort::Int], Sort::Int);
    let id_c = solver.apply(&id, &[c]);
    let id_c_eq_c = solver.eq(id_c, c);
    solver.assert_term(id_c_eq_c);

    // UF quantifier with trigger: E-matching should instantiate this on id(c).
    let x = solver.fresh_var("x", Sort::Int);
    let id_x = solver.apply(&id, &[x]);
    let id_x_eq_x = solver.eq(id_x, x);
    let uf_axiom = solver.forall_with_triggers(&[x], id_x_eq_x, &[&[id_x]]);
    solver.assert_term(uf_axiom);

    // Arithmetic forall with an obvious counterexample (y = 0): forall y. y > 0
    // This must never be reported as SAT.
    let y = solver.fresh_var("y", Sort::Int);
    let zero = solver.int_const(0);
    let y_gt_zero = solver.gt(y, zero);
    let bad_forall = solver.forall(&[y], y_gt_zero);
    solver.assert_term(bad_forall);

    // Precision gap: should return Unsat (forall y. y > 0 is false),
    // but currently returns Unknown due to CEGQI+E-matching interaction.
    assert_ne!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_uflia_valid_cegqi_forall_not_unsat_with_other_ematch_2829() {
    let mut solver = Solver::new(Logic::Uflia);

    // Ground UF term to trigger E-matching on the UF axiom below.
    let c = solver.declare_const("c", Sort::Int);
    let id = solver.declare_fun("id", &[Sort::Int], Sort::Int);
    let id_c = solver.apply(&id, &[c]);
    let id_c_eq_c = solver.eq(id_c, c);
    solver.assert_term(id_c_eq_c);

    // UF quantifier with trigger: E-matching should instantiate this on id(c).
    let x = solver.fresh_var("x", Sort::Int);
    let id_x = solver.apply(&id, &[x]);
    let id_x_eq_x = solver.eq(id_x, x);
    let uf_axiom = solver.forall_with_triggers(&[x], id_x_eq_x, &[&[id_x]]);
    solver.assert_term(uf_axiom);

    // Arithmetic tautology: forall y. y >= y
    // This satisfiable formula must never be reported as UNSAT.
    let y = solver.fresh_var("y", Sort::Int);
    let y_ge_y = solver.ge(y, y);
    let valid_forall = solver.forall(&[y], y_ge_y);
    solver.assert_term(valid_forall);

    // Precision gap: should return Sat (forall y. y >= y is valid + consistent UF),
    // but currently returns Unknown due to CEGQI+E-matching interaction.
    assert!(!solver.check_sat().is_unsat());
}

#[test]
fn test_forall_construction() {
    use ay_core::term::TermData;

    let mut solver = Solver::new(Logic::Uf);
    let x = solver.fresh_var("x", Sort::Int);
    let zero = solver.int_const(0);

    let body = solver.gt(x, zero);
    let q = solver.forall(&[x], body);

    assert!(solver.terms().is_quantifier(q.id()));
    assert_eq!(solver.terms().sort(q.id()), &Sort::Bool);

    let x_name = match solver.terms().get(x.id()) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("expected Var, got {other:?}"),
    };

    match solver.terms().get(q.id()) {
        TermData::Forall(vars, q_body, triggers) => {
            assert_eq!(vars, &vec![(x_name, Sort::Int)]);
            assert_eq!(*q_body, body.id());
            assert!(triggers.is_empty());
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn test_exists_construction() {
    use ay_core::term::TermData;

    let mut solver = Solver::new(Logic::Lia);
    let x = solver.fresh_var("x", Sort::Int);
    let one = solver.int_const(1);

    let body = solver.eq(x, one);
    let q = solver.exists(&[x], body);

    assert!(solver.terms().is_quantifier(q.id()));
    assert_eq!(solver.terms().sort(q.id()), &Sort::Bool);

    let x_name = match solver.terms().get(x.id()) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("expected Var, got {other:?}"),
    };

    match solver.terms().get(q.id()) {
        TermData::Exists(vars, q_body, triggers) => {
            assert_eq!(vars, &vec![(x_name, Sort::Int)]);
            assert_eq!(*q_body, body.id());
            assert!(triggers.is_empty());
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn test_forall_with_triggers_stores_triggers() {
    use ay_core::term::TermData;

    let mut solver = Solver::new(Logic::Uf);
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.gt(x, zero);

    let f_x = solver.apply(&f, &[x]);
    let q = solver.forall_with_triggers(&[x], body, &[&[f_x]]);

    match solver.terms().get(q.id()) {
        TermData::Forall(_, _, triggers) => {
            assert_eq!(triggers, &vec![vec![f_x.id()]]);
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn test_try_forall_with_triggers_rejects_triggers_without_bound_vars() {
    let mut solver = Solver::new(Logic::Uf);
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let zero = solver.int_const(0);
    let body = solver.gt(x, zero);

    let f_y = solver.apply(&f, &[y]);
    let err = solver
        .try_forall_with_triggers(&[x], body, &[&[f_y]])
        .unwrap_err();

    assert!(matches!(err, SolverError::InvalidTrigger { .. }));
}

#[test]
fn test_try_forall_with_triggers_skips_non_function_triggers() {
    use ay_core::term::TermData;

    let mut solver = Solver::new(Logic::Uf);
    let x = solver.fresh_var("x", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.gt(x, zero);

    // Var triggers are skipped; this should behave like empty triggers.
    let q = solver
        .try_forall_with_triggers(&[x], body, &[&[x]])
        .unwrap();

    match solver.terms().get(q.id()) {
        TermData::Forall(_, _, triggers) => {
            assert!(triggers.is_empty());
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn test_try_forall_rejects_non_var_term() {
    let mut solver = Solver::new(Logic::Uf);

    let not_a_var = solver.int_const(0);
    let body = solver.bool_const(true);
    let err = solver.try_forall(&[not_a_var], body).unwrap_err();

    assert!(matches!(err, SolverError::InvalidArgument { .. }));
}

#[test]
fn test_try_forall_rejects_non_bool_body() {
    let mut solver = Solver::new(Logic::Uf);

    let x = solver.fresh_var("x", Sort::Int);
    let not_bool = solver.int_const(0);
    let err = solver.try_forall(&[x], not_bool).unwrap_err();

    assert!(matches!(err, SolverError::SortMismatch { .. }));
}

#[test]
fn test_try_forall_rejects_duplicate_vars() {
    let mut solver = Solver::new(Logic::Uf);

    let x = solver.fresh_var("x", Sort::Int);
    let body = solver.bool_const(true);
    let err = solver.try_forall(&[x, x], body).unwrap_err();

    assert!(matches!(err, SolverError::InvalidArgument { .. }));
}

#[test]
fn test_try_exists_rejects_duplicate_vars() {
    let mut solver = Solver::new(Logic::Uf);

    let x = solver.fresh_var("x", Sort::Int);
    let body = solver.bool_const(true);
    let err = solver.try_exists(&[x, x], body).unwrap_err();

    assert!(matches!(err, SolverError::InvalidArgument { .. }));
}

#[test]
fn test_try_exists_rejects_non_bool_body() {
    let mut solver = Solver::new(Logic::Uf);

    let x = solver.fresh_var("x", Sort::Int);
    let not_bool = solver.int_const(0);
    let err = solver.try_exists(&[x], not_bool).unwrap_err();

    assert!(matches!(err, SolverError::SortMismatch { .. }));
}

#[test]
fn test_declare_fun_zero_arity() {
    // 0-arity functions act as uninterpreted constants
    let mut solver = Solver::new(Logic::QfUf);
    let c = solver.declare_fun("c", &[], Sort::Int);
    assert_eq!(c.arity(), 0);
    let c_val = solver.apply(&c, &[]);
    let five = solver.int_const(5);
    let eq = solver.eq(c_val, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_array_read_unwritten_index() {
    // const_array + store: verify unwritten indices return default
    let mut solver = Solver::new(Logic::QfAuflia);
    let zero = solver.int_const(0);
    let arr = solver.const_array(Sort::Int, zero);
    let idx5 = solver.int_const(5);
    let val42 = solver.int_const(42);
    let arr2 = solver.store(arr, idx5, val42);
    // Read at written index
    let read5 = solver.select(arr2, idx5);
    let eq5 = solver.eq(read5, val42);
    solver.assert_term(eq5);
    // Read at unwritten index should give default
    let idx10 = solver.int_const(10);
    let read10 = solver.select(arr2, idx10);
    let eq10 = solver.eq(read10, zero);
    solver.assert_term(eq10);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_array_store_different_indices() {
    // Storing at different indices doesn't interfere
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("a", Sort::array(Sort::Int, Sort::Int));
    let idx0 = solver.int_const(0);
    let idx1 = solver.int_const(1);
    let val10 = solver.int_const(10);
    let val20 = solver.int_const(20);
    let arr1 = solver.store(arr, idx0, val10);
    let arr2 = solver.store(arr1, idx1, val20);
    let read0 = solver.select(arr2, idx0);
    let eq0 = solver.eq(read0, val10);
    solver.assert_term(eq0);
    let read1 = solver.select(arr2, idx1);
    let eq1 = solver.eq(read1, val20);
    solver.assert_term(eq1);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

// =========================================================================
// =========================================================================
// try_new and SolverError tests (#602)
// =========================================================================

#[test]
fn test_try_new_success() {
    // try_new succeeds for supported logics
    let result = Solver::try_new(Logic::QfLia);
    assert!(result.is_ok());

    let result = Solver::try_new(Logic::QfLra);
    assert!(result.is_ok());

    let result = Solver::try_new(Logic::QfUf);
    assert!(result.is_ok());

    let result = Solver::try_new(Logic::QfBv);
    assert!(result.is_ok());
}

#[test]
fn test_try_new_returns_functional_solver() {
    // try_new returns a solver that works correctly
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA should be supported");

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_solver_error_display() {
    // SolverError has a reasonable Display implementation
    let err = SolverError::UnsupportedLogic("INVALID_LOGIC".to_string());
    let msg = format!("{err}");
    assert!(msg.contains("unsupported logic"));
    assert!(msg.contains("INVALID_LOGIC"));
}

// BV API fallible constructors (#1439)

#[test]
fn test_try_bvzeroext_returns_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfBv);
    let p = solver.declare_const("p", Sort::Bool);

    let err = solver.try_bvzeroext(p, 1).unwrap_err();
    match err {
        SolverError::SortMismatch {
            operation,
            expected,
            got,
        } => {
            assert_eq!(operation, "bvzeroext");
            assert_eq!(expected, "BitVec");
            assert!(matches!(got.as_slice(), [Sort::Bool]));
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_try_bvconcat_returns_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let p = solver.declare_const("p", Sort::Bool);

    let err = solver.try_bvconcat(x, p).unwrap_err();
    match err {
        SolverError::SortMismatch {
            operation,
            expected,
            got,
        } => {
            assert_eq!(operation, "bvconcat");
            assert_eq!(expected, "BitVec, BitVec");
            assert_eq!(got.len(), 2);
            assert!(matches!(&got[0], Sort::BitVec(bv) if bv.width == 8));
            assert!(matches!(&got[1], Sort::Bool));
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_try_bvadd_no_overflow_rejects_width_mismatch() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(8));
    let b = solver.declare_const("b", Sort::bitvec(16));

    let err = solver.try_bvadd_no_overflow(a, b, true).unwrap_err();
    match err {
        SolverError::SortMismatch {
            operation,
            expected,
            got,
        } => {
            assert_eq!(operation, "bvadd_no_overflow");
            assert_eq!(expected, "BitVec(w), BitVec(w)");
            assert_eq!(got.len(), 2);
            assert!(matches!(&got[0], Sort::BitVec(bv) if bv.width == 8));
            assert!(matches!(&got[1], Sort::BitVec(bv) if bv.width == 16));
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_try_bvextract_rejects_out_of_bounds() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));

    let err = solver.try_bvextract(x, 10, 0).unwrap_err();
    match err {
        SolverError::InvalidArgument { operation, message } => {
            assert_eq!(operation, "bvextract");
            assert!(message.contains("high (10)"));
            assert!(message.contains("width (8)"));
        }
        other => panic!("expected InvalidArgument, got {other:?}"),
    }
}

#[test]
fn test_try_bvrepeat_returns_sort_mismatch() {
    let mut solver = Solver::new(Logic::QfBv);
    let p = solver.declare_const("p", Sort::Bool);

    let err = solver.try_bvrepeat(p, 2).unwrap_err();
    match err {
        SolverError::SortMismatch {
            operation,
            expected,
            got,
        } => {
            assert_eq!(operation, "bvrepeat");
            assert_eq!(expected, "BitVec");
            assert!(matches!(got.as_slice(), [Sort::Bool]));
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_try_bvrepeat_rejects_zero_repetitions() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));

    let err = solver.try_bvrepeat(x, 0).unwrap_err();
    match err {
        SolverError::InvalidArgument { operation, message } => {
            assert_eq!(operation, "bvrepeat");
            assert!(message.contains("repeat count (0)"));
        }
        other => panic!("expected InvalidArgument, got {other:?}"),
    }
}

#[test]
fn test_try_bvrepeat_returns_repeated_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));

    let y = solver.try_bvrepeat(x, 3).unwrap();
    assert!(matches!(solver.terms().sort(y.id()), Sort::BitVec(bv) if bv.width == 24));
}

// Arithmetic API sort validation regressions (#2708)

#[test]
fn test_try_add_many_rejects_single_non_arithmetic_term() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);

    let err = solver.try_add_many(&[p]).unwrap_err();
    match err {
        SolverError::SortMismatch {
            operation,
            expected,
            got,
        } => {
            assert_eq!(operation, "add_many");
            assert_eq!(expected, "Int or Real");
            assert_eq!(got, vec![Sort::Bool]);
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_try_mul_many_rejects_single_non_arithmetic_term() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);

    let err = solver.try_mul_many(&[p]).unwrap_err();
    match err {
        SolverError::SortMismatch {
            operation,
            expected,
            got,
        } => {
            assert_eq!(operation, "mul_many");
            assert_eq!(expected, "Int or Real");
            assert_eq!(got, vec![Sort::Bool]);
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
#[should_panic(expected = "sort mismatch in lt")]
fn test_lt_panics_on_non_arithmetic_sort() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);
    let _ = solver.lt(p, q);
}

#[test]
#[should_panic(expected = "sort mismatch in ge")]
fn test_ge_panics_on_mixed_int_real() {
    let mut solver = Solver::new(Logic::QfLira);
    let i = solver.declare_const("i", Sort::Int);
    let r = solver.declare_const("r", Sort::Real);
    let _ = solver.ge(i, r);
}

/// Test for #1159: Datatype API support for model-checker-consumer integration
#[test]
fn test_datatype_api_1159() {
    let mut solver = Solver::new(Logic::Uf);

    let option_dt = DatatypeSort {
        name: "Option".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };

    solver.declare_datatype(&option_dt);
    let x = solver.declare_const("x", Sort::Datatype(option_dt.clone()));
    let is_some_x = solver.datatype_tester("Some", x);
    solver.assert_term(is_some_x);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_datatype_constructor_selector() {
    let mut solver = Solver::new(Logic::Uf);

    let point_dt = DatatypeSort {
        name: "Point".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-point".to_string(),
            fields: vec![
                DatatypeField {
                    name: "point-x".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "point-y".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };

    solver.declare_datatype(&point_dt);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let p = solver.datatype_constructor(&point_dt, "mk-point", &[one, two]);
    let q = solver.declare_const("q", Sort::Datatype(point_dt.clone()));
    let eq = solver.eq(q, p);
    solver.assert_term(eq);

    let qx = solver.datatype_selector("point-x", q, Sort::Int);
    let qx_eq_1 = solver.eq(qx, one);
    solver.assert_term(qx_eq_1);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_all_logic_unused_seq_decl_does_not_override_dt_auflia_routing() {
    let mut solver = Solver::new(Logic::All);
    let _unused_seq = solver.declare_const("unused_seq", Sort::Seq(Box::new(Sort::Int)));

    let point_dt = DatatypeSort {
        name: "PointWithUnusedSeq".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-point-unused-seq".to_string(),
            fields: vec![
                DatatypeField {
                    name: "point-unused-seq-x".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "point-unused-seq-y".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };

    solver.declare_datatype(&point_dt);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let p = solver.datatype_constructor(&point_dt, "mk-point-unused-seq", &[one, two]);
    let q = solver.declare_const("q_unused_seq_dt", Sort::Datatype(point_dt));
    let eq = solver.eq(q, p);
    solver.assert_term(eq);

    let qx = solver.datatype_selector("point-unused-seq-x", q, Sort::Int);
    let qx_eq_1 = solver.eq(qx, one);
    solver.assert_term(qx_eq_1);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_datatype_nullary_constructor() {
    let mut solver = Solver::new(Logic::Uf);

    let color_dt = DatatypeSort {
        name: "Color".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Red".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Green".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Blue".to_string(),
                fields: vec![],
            },
        ],
    };

    solver.declare_datatype(&color_dt);
    let c = solver.declare_const("c", Sort::Datatype(color_dt.clone()));
    let red = solver.datatype_constructor(&color_dt, "Red", &[]);
    let c_eq_red = solver.eq(c, red);
    solver.assert_term(c_eq_red);

    let is_red_c = solver.datatype_tester("Red", c);
    solver.assert_term(is_red_c);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

/// Regression test for #2832: 4-variable doubling equality chain via Solver API.
/// Root cause: VariableSubstitution TermId-ordering rejected `acc -> (+ i i)`.
/// Fixed by #2830 (graph-based cycle detection).
#[test]
fn test_doubling_equality_chain_unsat_2832() {
    let mut s = Solver::new(Logic::QfLia);
    s.set_timeout(Some(Duration::from_secs(5)));
    let i = s.declare_const("i", Sort::Int);
    let acc = s.declare_const("acc", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let acc_prime = s.declare_const("acc_prime", Sort::Int);
    let one = s.int_const(1);
    let two = s.int_const(2);

    // acc = i + i
    let i_plus_i = s.add(i, i);
    let eq1 = s.eq(acc, i_plus_i);
    s.assert_term(eq1);
    // i_prime = i + 1
    let i_plus_one = s.add(i, one);
    let eq2 = s.eq(i_prime, i_plus_one);
    s.assert_term(eq2);
    // acc_prime = acc + 2
    let acc_plus_two = s.add(acc, two);
    let eq3 = s.eq(acc_prime, acc_plus_two);
    s.assert_term(eq3);
    // NOT(acc_prime = i_prime + i_prime)
    let ip_plus_ip = s.add(i_prime, i_prime);
    let eq4 = s.eq(acc_prime, ip_plus_ip);
    let neg = s.not(eq4);
    s.assert_term(neg);

    assert!(s.check_sat().is_unsat());
}

// P0 #5041: QF_AUFLIA Solver API hangs on ge/le with array select
#[test]
fn test_auflia_ge_le_select_unsat() {
    // Contradictory constraints on array element — must return UNSAT quickly
    let mut solver = Solver::new(Logic::QfAuflia);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let perms = solver.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let loc = solver.declare_const("loc", Sort::Int);
    let selected = solver.select(perms, loc);

    let c1260 = solver.int_const(1260);
    let c1259 = solver.int_const(1259);

    let ge1 = solver.ge(selected, c1260);
    let eq1 = solver.eq(selected, c1259);

    solver.assert_term(ge1);
    solver.assert_term(eq1);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_auflia_ge_le_select_sat() {
    // Satisfiable range constraint on array element — should not hang
    let mut solver = Solver::new(Logic::QfAuflia);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let perms = solver.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let loc = solver.declare_const("loc", Sort::Int);
    let selected = solver.select(perms, loc);

    let c1260 = solver.int_const(1260);
    let c2520 = solver.int_const(2520);
    let c0 = solver.int_const(0);

    let ge1 = solver.ge(selected, c1260);
    let le1 = solver.le(selected, c2520);
    let ge2 = solver.ge(selected, c0);

    solver.assert_term(ge1);
    solver.assert_term(le1);
    solver.assert_term(ge2);

    let result = solver.check_sat();
    // Should ideally be Sat, but even Unknown is acceptable as long as it doesn't hang
    assert_ne!(
        result,
        SolveResult::unsat(),
        "range 1260..2520 is satisfiable"
    );
}

#[test]
fn test_auflia_verification_consumer_points_to_half_perm() {
    // Exact reproduction of verification-consumer's PointsTo encoding for half permission.
    // This is the formula that P0 #5041 reports as hanging.
    // Formula: domain[loc] == 1 AND heap[loc] == 42 AND perms[loc] >= 1260
    //          AND perms[loc] <= 2520 AND perms[loc] > -1
    let mut solver = Solver::new(Logic::QfAuflia);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let heap = solver.declare_const("heap", Sort::array(Sort::Int, Sort::Int));
    let domain = solver.declare_const("domain", Sort::array(Sort::Int, Sort::Int));
    let perms = solver.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let loc = solver.declare_const("loc", Sort::Int);

    // domain[loc] == 1
    let dom_val = solver.select(domain, loc);
    let one = solver.int_const(1);
    let in_dom = solver.eq(dom_val, one);

    // heap[loc] == 42
    let heap_val = solver.select(heap, loc);
    let val42 = solver.int_const(42);
    let val_eq = solver.eq(heap_val, val42);

    // perms[loc] >= 1260 (half permission threshold)
    let current_perm = solver.select(perms, loc);
    let half = solver.int_const(1260);
    let perm_ge = solver.ge(current_perm, half);

    // perms[loc] <= 2520 (PERM_SCALE)
    let perm_scale = solver.int_const(2520);
    let perm_bounded = solver.le(current_perm, perm_scale);

    // perms[loc] > -1 (non-negative)
    let neg_one = solver.int_const(-1);
    let perm_non_neg = solver.gt(current_perm, neg_one);

    // Conjunction: in_dom AND val_eq AND perm_ge AND perm_bounded AND perm_non_neg
    let and1 = solver.and(in_dom, val_eq);
    let and2 = solver.and(and1, perm_ge);
    let and3 = solver.and(and2, perm_bounded);
    let formula = solver.and(and3, perm_non_neg);

    solver.assert_term(formula);

    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "PointsTo half permission should be SAT"
    );
}

#[test]
fn test_auflia_verification_consumer_points_to_half_then_pin_unsat() {
    // Second phase: after asserting points-to with half permission,
    // pin perms[loc] to threshold-1 (1259) which should be UNSAT.
    let mut solver = Solver::new(Logic::QfAuflia);
    solver.set_timeout(Some(Duration::from_secs(5)));

    let heap = solver.declare_const("heap", Sort::array(Sort::Int, Sort::Int));
    let domain = solver.declare_const("domain", Sort::array(Sort::Int, Sort::Int));
    let perms = solver.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let loc = solver.declare_const("loc", Sort::Int);

    // Encode PointsTo with half permission
    let dom_val = solver.select(domain, loc);
    let one = solver.int_const(1);
    let in_dom = solver.eq(dom_val, one);

    let heap_val = solver.select(heap, loc);
    let val42 = solver.int_const(42);
    let val_eq = solver.eq(heap_val, val42);

    let current_perm = solver.select(perms, loc);
    let half = solver.int_const(1260);
    let perm_ge = solver.ge(current_perm, half);

    let perm_scale = solver.int_const(2520);
    let perm_bounded = solver.le(current_perm, perm_scale);

    let neg_one = solver.int_const(-1);
    let perm_non_neg = solver.gt(current_perm, neg_one);

    let and1 = solver.and(in_dom, val_eq);
    let and2 = solver.and(and1, perm_ge);
    let and3 = solver.and(and2, perm_bounded);
    let formula = solver.and(and3, perm_non_neg);

    solver.assert_term(formula);

    // Pin perms[loc] = 1259 (below threshold)
    let below = solver.int_const(1259);
    let pinned = solver.eq(current_perm, below);
    solver.assert_term(pinned);

    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "pinned below half threshold should be UNSAT"
    );
}

/// Regression test for #5405: LRA solver must return UNSAT (not SAT with invalid model)
/// when strict inequalities make a formula unsatisfiable.
///
/// Formula: x in [-10, 10] and (x < -10 or x > 10) is UNSAT.
/// The LRA solver was returning SAT with an invalid model, which model validation
/// caught and converted to Unknown("internal-error").
#[test]
fn test_lra_strict_inequality_disjunction_unsat_5405() {
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.declare_const("x", Sort::Real);

    // x >= -10
    let neg10 = solver.real_const(-10.0);
    let c1 = solver.ge(x, neg10);
    solver.assert_term(c1);

    // x <= 10
    let pos10 = solver.real_const(10.0);
    let c2 = solver.le(x, pos10);
    solver.assert_term(c2);

    // x < -10 or x > 10 (contradicts bounds)
    let neg10b = solver.real_const(-10.0);
    let pos10b = solver.real_const(10.0);
    let lt_neg10 = solver.lt(x, neg10b);
    let gt_pos10 = solver.gt(x, pos10b);
    let disj = solver.or(lt_neg10, gt_pos10);
    solver.assert_term(disj);

    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "#5405: x in [-10,10] and (x < -10 or x > 10) should be UNSAT"
    );
}

/// Regression test for #5405 variant: trivially SAT QF_LRA through API should
/// produce a valid model (not internal-error).
#[test]
fn test_lra_api_sat_model_valid_5405() {
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.declare_const("x", Sort::Real);

    // x >= 1 and x <= 5
    let one = solver.real_const(1.0);
    let five = solver.real_const(5.0);
    let c1 = solver.ge(x, one);
    let c2 = solver.le(x, five);
    solver.assert_term(c1);
    solver.assert_term(c2);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat, "x in [1,5] should be SAT");

    let model = solver
        .model()
        .expect("SAT result should have model")
        .into_inner();
    let x_val = model
        .real_val_f64("x")
        .expect("model should have Real value for x");
    assert!(
        (1.0..=5.0).contains(&x_val),
        "model x={x_val} should be in [1,5]"
    );
}

/// Regression test for #5405 variant: strict bounds only, API path.
#[test]
fn test_lra_api_strict_bounds_sat_5405() {
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.declare_const("x", Sort::Real);

    // x > 0 and x < 1
    let zero = solver.real_const(0.0);
    let one = solver.real_const(1.0);
    let c1 = solver.gt(x, zero);
    let c2 = solver.lt(x, one);
    solver.assert_term(c1);
    solver.assert_term(c2);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat, "x in (0,1) should be SAT");

    let model = solver
        .model()
        .expect("SAT result should have model")
        .into_inner();
    let x_val = model
        .real_val_f64("x")
        .expect("model should have Real value for x");
    assert!(
        x_val > 0.0 && x_val < 1.0,
        "model x={x_val} should be in (0,1)"
    );
}

#[test]
fn test_iff_both_true() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);

    // p <=> q, p = true => q must be true
    let biconditional = solver.iff(p, q);
    solver.assert_term(biconditional);
    solver.assert_term(p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_iff_both_false() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);

    // p <=> q, p = false => q must be false
    let biconditional = solver.iff(p, q);
    solver.assert_term(biconditional);
    let not_p = solver.not(p);
    solver.assert_term(not_p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_iff_contradiction() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);

    // p <=> q, p = true, q = false => unsat
    let biconditional = solver.iff(p, q);
    solver.assert_term(biconditional);
    solver.assert_term(p);
    let not_q = solver.not(q);
    solver.assert_term(not_q);

    assert!(solver.check_sat().is_unsat());
}

#[test]
fn test_try_iff_sort_error() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let x = solver.declare_const("x", Sort::Int);

    let err = solver.try_iff(p, x).unwrap_err();
    if let SolverError::SortMismatch { operation, .. } = err {
        assert_eq!(operation, "iff");
    } else {
        panic!("expected SortMismatch, got {err:?}");
    }
}

/// Regression test for #2910: API-level sequential push/pop cycles must not
/// leak state between scopes.
///
/// Reproduces the deductive-checks verification pattern: for each assertion condition,
/// push, assert(not(condition)), check-sat, pop. All conditions are trivially
/// true (constants), so each check-sat must return UNSAT.
#[test]
fn test_deductive_checks_push_pop_api_sequential_constant_checks() {
    let mut solver = Solver::new(Logic::QfLia);

    let five = solver.int_const(5);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // VC1: 5 > 0 is true → assert(not(5 > 0)) = assert(5 <= 0) → UNSAT
    solver.push();
    let not_vc1 = solver.le(five, zero);
    solver.assert_term(not_vc1);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Bug #2910: VC1 (5 <= 0) should be UNSAT"
    );
    solver.pop();

    // VC2: 5 < 10 is true → assert(not(5 < 10)) = assert(5 >= 10) → UNSAT
    solver.push();
    let not_vc2 = solver.ge(five, ten);
    solver.assert_term(not_vc2);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Bug #2910: VC2 (5 >= 10) should be UNSAT"
    );
    solver.pop();

    // VC3: 5 = 5 is true → assert(not(5 = 5)) = assert(5 != 5) → UNSAT
    solver.push();
    let eq_5_5 = solver.eq(five, five);
    let not_vc3 = solver.not(eq_5_5);
    solver.assert_term(not_vc3);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Bug #2910: VC3 (5 != 5) should be UNSAT"
    );
    solver.pop();
}

/// Regression test for #2910 variant: API-level sequential push/pop with
/// variables (closer to real deductive-checks usage).
#[test]
fn test_deductive_checks_push_pop_api_sequential_variable_checks() {
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let five = solver.int_const(5);
    let ten = solver.int_const(10);
    let zero = solver.int_const(0);

    // Global: x = 5, y = 10
    let x_eq_5 = solver.eq(x, five);
    solver.assert_term(x_eq_5);
    let y_eq_10 = solver.eq(y, ten);
    solver.assert_term(y_eq_10);

    // VC1: x > 0 is true (x=5) → assert(x <= 0) → UNSAT
    solver.push();
    let not_vc1 = solver.le(x, zero);
    solver.assert_term(not_vc1);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Bug #2910: VC1 (x<=0 with x=5) should be UNSAT"
    );
    solver.pop();

    // VC2: x < y is true (5<10) → assert(x >= y) → UNSAT
    solver.push();
    let not_vc2 = solver.ge(x, y);
    solver.assert_term(not_vc2);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Bug #2910: VC2 (x>=y with x=5,y=10) should be UNSAT"
    );
    solver.pop();

    // VC3: x = 5 is true → assert(x != 5) → UNSAT
    solver.push();
    let eq_x_5 = solver.eq(x, five);
    let not_vc3 = solver.not(eq_x_5);
    solver.assert_term(not_vc3);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "Bug #2910: VC3 (x!=5 with x=5) should be UNSAT"
    );
    solver.pop();
}

/// Regression test for #8616: AUFLIA quantifier E-matching SAT model verification.
/// Mimics verification-consumer's quantifier_forall_trigger_instantiation test.
/// Axiom: forall x {:pattern f(x)} f(x) > 0
/// Ground: f(5)
/// Negate: f(5) <= 0
/// Expected: UNSAT via E-matching trigger instantiation.
#[test]
fn test_auflia_quantifier_forall_trigger_instantiation_8616() {
    let mut solver = Solver::new(Logic::Auflia);

    // declare-fun f (Int) Int
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);

    // Create bound variable x
    let x = solver.fresh_var("x", Sort::Int);

    // f(x) - the trigger pattern and the body term
    let f_x = solver.apply(&f, &[x]);

    // f(x) > 0
    let zero = solver.int_const(0);
    let f_x_gt_0 = solver.gt(f_x, zero);

    // forall x {:pattern f(x)} f(x) > 0
    let trigger = &[f_x];
    let forall = solver
        .try_forall_with_triggers(&[x], f_x_gt_0, &[trigger])
        .expect("valid forall with triggers");
    solver.assert_term(forall);

    // f(5) <= 0
    let five = solver.int_const(5);
    let f_5 = solver.apply(&f, &[five]);
    let f_5_le_0 = solver.le(f_5, zero);
    solver.assert_term(f_5_le_0);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "Expected UNSAT via E-matching trigger instantiation, got {result:?}"
    );
}

#[test]
fn test_auflia_quantifier_forall_trigger_ground_equality_conflict() {
    let mut solver = Solver::new(Logic::Auflia);
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let f_x = solver.apply(&f, &[x]);
    let zero = solver.int_const(0);
    let f_x_gt_0 = solver.gt(f_x, zero);
    let trigger = &[f_x];
    let forall = solver
        .try_forall_with_triggers(&[x], f_x_gt_0, &[trigger])
        .expect("valid forall with triggers");
    solver.assert_term(forall);

    let seven = solver.int_const(7);
    let f_7 = solver.apply(&f, &[seven]);
    let neg_one = solver.int_const(-1);
    let f_7_eq_neg_one = solver.eq(f_7, neg_one);
    solver.assert_term(f_7_eq_neg_one);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "Expected strictly certified UNSAT via E-matching, got {result:?}"
    );
}

/// #reserved-ops: `int2bv` is a builtin BV<->Int bridge operator (SMT-LIB
/// `(_ int2bv w)`). The forged-theory-symbol gate (ay commit e043cf97) must
/// keep rejecting EVERY `declare_fun("int2bv", ..)` — at any signature — so a
/// caller cannot forge the builtin as a user function and steer a wrong UNSAT.
/// The verify-time ICE fix routes legitimate int<->bv lowering through the REAL
/// builtin (`try_int2bv` / `mk_int2bv`), NOT through `declare_fun`, so this gate
/// stays fully closed. This pins that we did not reopen the forgery hole.
#[test]
fn test_int2bv_declare_fun_still_reserved_but_builtin_works() {
    let mut solver = Solver::new(Logic::QfAufbv);

    // Forgery block intact: declaring the reserved builtin name is rejected at
    // BOTH the plausible `(Int) -> (BitVec 8)` shape and a wrong signature.
    assert!(
        solver
            .try_declare_fun("int2bv", &[Sort::Int], Sort::bitvec(8))
            .is_err(),
        "declare_fun(int2bv) must stay rejected (reserved builtin) — the forgery \
         gate must not be reopened"
    );
    assert!(
        solver
            .try_declare_fun("int2bv", &[Sort::Bool, Sort::Int], Sort::Int)
            .is_err(),
        "wrong-signature declare_fun(int2bv) must also stay rejected"
    );
    // The named sibling `bv2nat` is likewise reserved and non-declarable.
    assert!(
        solver
            .try_declare_fun("bv2nat", &[Sort::bitvec(8)], Sort::Int)
            .is_err(),
        "declare_fun(bv2nat) must stay rejected (reserved builtin)"
    );

    // The legitimate path — the REAL builtin — is unaffected and semantically
    // correct: `bv2nat(int2bv(x, 8))` over a symbolic Int `x` is exactly
    // `x mod 256`. `x = 5` must force the residue to 5 (SAT), and asserting the
    // residue is 6 with `x = 5` must be UNSAT.
    let x = solver.declare_const("x", Sort::Int);
    let residue = solver.int2bv(x, 8); // builtin (_ int2bv 8) x
    let residue_nat = solver.bv2int(residue); // builtin bv2nat(...)
    let five = solver.int_const(5);
    let six = solver.int_const(6);
    let eq_x5 = solver.eq(x, five);
    solver.assert_term(eq_x5);

    solver.push();
    let eq_res5 = solver.eq(residue_nat, five);
    solver.assert_term(eq_res5);
    assert!(
        !solver.check_sat().is_unsat(),
        "bv2nat(int2bv(x,8))=5 with x=5 must be SAT (residue of 5 is 5)"
    );
    solver.pop();

    let eq_res6 = solver.eq(residue_nat, six);
    solver.assert_term(eq_res6);
    assert!(
        solver.check_sat().is_unsat(),
        "bv2nat(int2bv(x,8))=6 with x=5 must be UNSAT (residue of 5 is 5, not 6)"
    );
}
