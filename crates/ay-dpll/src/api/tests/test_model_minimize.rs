// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for explicit model minimization, projection, and variable inference API (#8297).

use ay_core::BitVecSort;
use num_bigint::BigInt;

use crate::api::*;

// ---------------------------------------------------------------------------
// try_minimize_model — BV
// ---------------------------------------------------------------------------

#[test]
fn test_minimize_bv_unconstrained_to_zero() {
    // Unconstrained 8-bit BV should be minimized to 0.
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    // x can be anything — just declare it.
    let zero = solver.bv_const(0, 8);
    let t = solver.bvuge(x, zero); // always true for unsigned
    solver.assert_term(t);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        assert_eq!(value, BigInt::from(0), "should minimize to 0");
    } else {
        panic!("expected BitVec model value for x");
    }

    // Pop the minimization scope to restore original state.
    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_bv_constrained_nonzero() {
    // x > 5 (unsigned 8-bit). Cannot be 0 or 1, keeps original or picks
    // all-ones/power-of-2 candidate.
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    let five = solver.bv_const(5, 8);
    let gt = solver.bvugt(x, five);
    solver.assert_term(gt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        assert!(value > BigInt::from(5), "x must be > 5, got {value}");
    } else {
        panic!("expected BitVec model value for x");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_bv_can_be_one() {
    // x > 0 and x < 3 (unsigned 8-bit). 0 is not valid, 1 is.
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    let zero = solver.bv_const(0, 8);
    let three = solver.bv_const(3, 8);
    let gt = solver.bvugt(x, zero);
    let lt = solver.bvult(x, three);
    solver.assert_term(gt);
    solver.assert_term(lt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        assert_eq!(
            value,
            BigInt::from(1),
            "should minimize to 1 (0 is invalid)"
        );
    } else {
        panic!("expected BitVec model value for x");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_preserves_constraints_between_vars() {
    // Two BV vars with an inter-variable constraint: x != y.
    // Minimization should still produce a valid model.
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8.clone());
    let y = solver.declare_const("y", bv8);
    let eq_xy = solver.eq(x, y);
    let neq = solver.not(eq_xy);
    solver.assert_term(neq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let (
        Some(ModelValue::BitVec { value: xv, .. }),
        Some(ModelValue::BitVec { value: yv, .. }),
    ) = (solver.value(x), solver.value(y))
    {
        assert_ne!(
            xv, yv,
            "minimized model must satisfy x != y, got x={xv} y={yv}"
        );
        // With greedy minimization: x tries 0 first (succeeds since y can differ),
        // then y tries 0 (fails since x=0), tries 1 (succeeds).
        assert_eq!(xv, BigInt::from(0), "x should be minimized to 0");
        assert_eq!(yv, BigInt::from(1), "y should be minimized to 1");
    } else {
        panic!("expected BitVec model values");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_bv_all_ones_candidate() {
    // x > 200 and x < 256 (unsigned 8-bit). 0xFF (255) should be a candidate
    // and should be feasible.
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    let lo = solver.bv_const(200, 8);
    let gt = solver.bvugt(x, lo);
    solver.assert_term(gt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        // 0xFF (255) is in the candidate list and satisfies x > 200
        assert_eq!(
            value,
            BigInt::from(255),
            "should minimize to 0xFF (all-ones), got {value}"
        );
    } else {
        panic!("expected BitVec model value for x");
    }

    solver.try_pop().expect("pop should succeed");
}

// ---------------------------------------------------------------------------
// try_minimize_model — Int
// ---------------------------------------------------------------------------

#[test]
fn test_minimize_int_to_zero() {
    // x >= 0 — minimizer should pick 0.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let zero = solver.int_const(0);
    let ge = solver.ge(x, zero);
    solver.assert_term(ge);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert_eq!(val, BigInt::from(0), "should minimize to 0");
    } else {
        panic!("expected Int model value for x");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_int_bounded_to_one() {
    // x > 0, x < 3 — minimizer should pick 1.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let zero = solver.int_const(0);
    let three = solver.int_const(3);
    let gt = solver.gt(x, zero);
    let lt = solver.lt(x, three);
    solver.assert_term(gt);
    solver.assert_term(lt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert_eq!(val, BigInt::from(1), "should minimize to 1");
    } else {
        panic!("expected Int model value for x");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_int_negative_to_neg_one() {
    // x < 0 — minimizer tries 0 (fails), 1 (fails), -1 (succeeds).
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let zero = solver.int_const(0);
    let lt = solver.lt(x, zero);
    solver.assert_term(lt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert_eq!(val, BigInt::from(-1), "should minimize to -1");
    } else {
        panic!("expected Int model value for x");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_int_preserves_constraints() {
    // x + y = 10, x >= 0, y >= 0. Minimization should keep constraint.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let sum = solver.add(x, y);
    let ten = solver.int_const(10);
    let zero = solver.int_const(0);
    let eq = solver.eq(sum, ten);
    let ge_x = solver.ge(x, zero);
    let ge_y = solver.ge(y, zero);
    solver.assert_term(eq);
    solver.assert_term(ge_x);
    solver.assert_term(ge_y);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed");

    if let (Some(ModelValue::Int(xv)), Some(ModelValue::Int(yv))) =
        (solver.value(x), solver.value(y))
    {
        assert_eq!(
            &xv + &yv,
            BigInt::from(10),
            "must satisfy x + y = 10, got x={xv} y={yv}"
        );
        // Greedy: first var (x) should be minimized to 0, then y must be 10.
        assert_eq!(xv, BigInt::from(0), "x should be minimized to 0");
        assert_eq!(yv, BigInt::from(10), "y should be 10 (since x=0)");
    } else {
        panic!("expected Int model values");
    }

    solver.try_pop().expect("pop should succeed");
}

#[test]
fn test_minimize_no_vars_is_noop() {
    // Bool-only problem with no Int or BV vars: minimization is a no-op.
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    solver.assert_term(a);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver
        .try_minimize_model()
        .expect("minimization should succeed (no-op)");
}

#[test]
fn test_minimize_errors_before_check_sat() {
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let _x = solver.declare_const("x", bv8);

    let err = solver.try_minimize_model();
    assert!(err.is_err(), "should error before check_sat");
}

// ---------------------------------------------------------------------------
// project_model
// ---------------------------------------------------------------------------

#[test]
fn test_project_model_filters_variables() {
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8.clone());
    let y = solver.declare_const("y", bv8.clone());
    let _z = solver.declare_const("z", bv8);

    let zero = solver.bv_const(0, 8);
    let eq_x = solver.eq(x, zero);
    let eq_y = solver.eq(y, zero);
    solver.assert_term(eq_x);
    solver.assert_term(eq_y);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let projected = solver.project_model(&["x", "y"]);
    assert!(projected.contains_key("x"), "projection should include x");
    assert!(projected.contains_key("y"), "projection should include y");
    assert!(!projected.contains_key("z"), "projection should exclude z");
    assert_eq!(projected.len(), 2);
}

#[test]
fn test_project_model_empty_vars() {
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let _x = solver.declare_const("x", bv8);

    let zero = solver.bv_const(0, 8);
    let eq = solver.eq(_x, zero);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let projected = solver.project_model(&[]);
    assert!(projected.is_empty(), "empty vars should give empty map");
}

#[test]
fn test_project_model_nonexistent_vars() {
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);

    let zero = solver.bv_const(0, 8);
    let eq = solver.eq(x, zero);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let projected = solver.project_model(&["nonexistent"]);
    assert!(
        projected.is_empty(),
        "nonexistent var should give empty map"
    );
}

#[test]
fn test_project_model_no_model_available() {
    let solver = Solver::new(Logic::QfBv);
    // No check_sat called, so no model.
    let projected = solver.project_model(&["x"]);
    assert!(projected.is_empty());
}

// ---------------------------------------------------------------------------
// infer_relevant_vars
// ---------------------------------------------------------------------------

#[test]
fn test_infer_relevant_vars_returns_user_declared() {
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let _x = solver.declare_const("x", bv8.clone());
    let _y = solver.declare_const("y", bv8);

    let relevant = solver.infer_relevant_vars();
    assert!(relevant.contains(&"x".to_string()), "x should be relevant");
    assert!(relevant.contains(&"y".to_string()), "y should be relevant");
    assert_eq!(relevant.len(), 2);
}

#[test]
fn test_infer_relevant_vars_empty_solver() {
    let solver = Solver::new(Logic::QfBv);
    let relevant = solver.infer_relevant_vars();
    assert!(relevant.is_empty());
}

// ---------------------------------------------------------------------------
// try_minimize_and_project
// ---------------------------------------------------------------------------

#[test]
fn test_minimize_and_project_combined() {
    // Use Int logic which is more stable with incremental push/pop during
    // minimization than BV arithmetic.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let y = solver.int_var("y");

    // x + y = 10, x >= 0, y >= 0
    let sum = solver.add(x, y);
    let ten = solver.int_const(10);
    let zero = solver.int_const(0);
    let eq = solver.eq(sum, ten);
    let ge_x = solver.ge(x, zero);
    let ge_y = solver.ge(y, zero);
    solver.assert_term(eq);
    solver.assert_term(ge_x);
    solver.assert_term(ge_y);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let projected = solver
        .try_minimize_and_project()
        .expect("minimize_and_project should succeed");

    // Both x and y should appear (user-declared, not internal).
    assert!(
        projected.contains_key("x"),
        "x should be in projected model"
    );
    assert!(
        projected.contains_key("y"),
        "y should be in projected model"
    );

    // Values should still satisfy x + y = 10.
    if let (Some(ModelValue::Int(xv)), Some(ModelValue::Int(yv))) =
        (projected.get("x"), projected.get("y"))
    {
        assert_eq!(
            xv + yv,
            BigInt::from(10),
            "minimized model must satisfy x + y = 10, got x={xv} y={yv}"
        );
        // Greedy minimization: x should be 0, y should be 10.
        assert_eq!(*xv, BigInt::from(0), "x should be minimized to 0");
        assert_eq!(*yv, BigInt::from(10), "y should be 10 (since x=0)");
    } else {
        panic!("expected Int model values in projection");
    }

    solver.try_pop().expect("pop should succeed");
}
