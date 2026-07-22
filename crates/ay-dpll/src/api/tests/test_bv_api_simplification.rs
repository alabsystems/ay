// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for BV API-path simplification behavior.

use crate::api::*;

#[test]
fn test_api_bvadd_zero_folds_to_operand() {
    let mut solver = Solver::new(Logic::QfBv);

    let x = solver.bv_const(0x2ai64, 64);
    let zero = solver.bv_const(0i64, 64);
    let sum = solver.bvadd(x, zero);

    assert_eq!(sum, x, "bvadd(x, 0) should canonicalize to x");
}

#[test]
fn test_api_bvsub_self_folds_to_zero() {
    let mut solver = Solver::new(Logic::QfBv);

    let x = solver.bv_const(0x55i64, 32);
    let diff = solver.bvsub(x, x);
    let expected = solver.bv_const(0i64, 32);

    assert_eq!(diff, expected, "bvsub(x, x) should canonicalize to zero");
}

#[test]
fn test_api_bvzeroext_constant_fold() {
    let mut solver = Solver::new(Logic::QfBv);

    let x = solver.bv_const(0x12i64, 8);
    let ext = solver.bvzeroext(x, 8);
    let expected = solver.bv_const(0x12i64, 16);

    assert_eq!(
        ext, expected,
        "bvzeroext(constant) should fold to widened constant"
    );
}
