// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the panic-safe `try_check_sat` / `try_check_sat_assuming` API (#5057).

use crate::api::*;

#[test]
fn test_try_check_sat_returns_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let result = solver.try_check_sat();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), SolveResult::Sat);
}

#[test]
fn test_try_check_sat_returns_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // x > 0 AND x < 0 is unsatisfiable
    let gt = solver.gt(x, zero);
    let lt = solver.lt(x, zero);
    solver.assert_term(gt);
    solver.assert_term(lt);

    let result = solver.try_check_sat();
    assert!(result.is_ok());
    assert!(result.unwrap().is_unsat());
}

#[test]
fn test_try_check_sat_assuming_returns_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    let x_eq_1 = solver.eq(x, one);
    let result = solver.try_check_sat_assuming(&[x_eq_1]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), SolveResult::Sat);
}

#[test]
fn test_try_check_sat_assuming_returns_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    // Assumption x < 0 contradicts x >= 0
    let x_lt_0 = solver.lt(x, zero);
    let result = solver.try_check_sat_assuming(&[x_lt_0]);
    assert!(result.is_ok());
    assert!(result.unwrap().is_unsat());
}

#[test]
fn test_try_check_sat_interrupted_returns_unknown() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();

    let result = solver.try_check_sat();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), SolveResult::Unknown);
}

#[test]
fn test_try_check_sat_assuming_interrupted_returns_unknown() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);

    solver.interrupt();
    let result = solver.try_check_sat_assuming(&[gt]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), SolveResult::Unknown);
}

#[test]
fn test_solver_error_solver_panic_variant_display() {
    let err = SolverError::SolverPanic("test panic message".to_string());
    assert_eq!(err.to_string(), "solver panic: test panic message");
}

#[test]
fn test_solver_error_solver_panic_debug() {
    let err = SolverError::SolverPanic("boom".to_string());
    let debug = format!("{err:?}");
    assert!(debug.contains("SolverPanic"));
    assert!(debug.contains("boom"));
}

// =========================================================================
// try_check_sat_with_details (#6668)
// =========================================================================

#[test]
fn test_try_check_sat_with_details_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let result = solver.try_check_sat_with_details();
    assert!(result.is_ok());
    let details = result.unwrap();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(details.verification.sat_model_validated);
    assert!(details.executor_error.is_none());
}

#[test]
fn test_try_check_sat_with_details_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    let lt = solver.lt(x, zero);
    solver.assert_term(gt);
    solver.assert_term(lt);

    let result = solver.try_check_sat_with_details();
    assert!(result.is_ok());
    let details = result.unwrap();
    assert_eq!(details.result, SolveResult::unsat());
    assert!(!details.verification.sat_model_validated);
}

#[test]
fn test_try_check_sat_with_details_unknown_interrupted() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();

    let result = solver.try_check_sat_with_details();
    assert!(result.is_ok());
    let details = result.unwrap();
    assert_eq!(details.result, SolveResult::Unknown);
    assert_eq!(details.unknown_reason, Some(UnknownReason::Interrupted));
}

// =========================================================================
// try_check_sat_assuming_with_details (#6668)
// =========================================================================

#[test]
fn test_try_check_sat_assuming_with_details_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    let x_eq_1 = solver.eq(x, one);
    let result = solver.try_check_sat_assuming_with_details(&[x_eq_1]);
    assert!(result.is_ok());
    let details = result.unwrap();
    assert_eq!(details.solve.result, SolveResult::Sat);
    assert!(details.unsat_assumptions.is_none());
}

#[test]
fn test_try_check_sat_assuming_with_details_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    let x_lt_0 = solver.lt(x, zero);
    let result = solver.try_check_sat_assuming_with_details(&[x_lt_0]);
    assert!(result.is_ok());
    let details = result.unwrap();
    assert_eq!(details.solve.result, SolveResult::unsat());
    assert!(
        details.unsat_assumptions.is_some(),
        "unsat_assumptions should be populated on UNSAT"
    );
}

#[test]
fn test_try_check_sat_assuming_with_details_interrupted() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.interrupt();

    let result = solver.try_check_sat_assuming_with_details(&[x_ge_0]);
    assert!(result.is_ok());
    let details = result.unwrap();
    assert_eq!(details.solve.result, SolveResult::Unknown);
    assert_eq!(
        details.solve.unknown_reason,
        Some(UnknownReason::Interrupted)
    );
    assert!(details.unsat_assumptions.is_none());
}
