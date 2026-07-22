// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for #8596: QF_AUFLIA false UNSAT on const-array model
//! equality benchmarks.
//!
//! Both benchmarks use `(as const (Array Int Int)) 0` with stores and require
//! the Nelson-Oppen combination to discover index equalities via model equality
//! splitting. Without the array rescue path in `try_array_rescue_on_arith_conflict`,
//! the LIA solver finds UNSAT before the array theory can request the needed
//! model equalities, producing a false UNSAT result.
//!
//! Reference: Z3 smt_context.cpp `assume_eq` + `try_true_first` pattern.
//! Part of #8596

use ntest::timeout;

/// Const array with single store: `a = store(const(0), x, 1)` and `select(a, y) = 1`.
///
/// SAT when x = y. The array theory must request the model equality x = y
/// before LIA can determine the assignment. Without model equality splitting,
/// LIA sees select(a, y) as the const-array default value 0 (when x != y)
/// and finds UNSAT against the constraint select(a, y) = 1.
///
/// Z3 confirms SAT.
#[test]
#[timeout(30_000)]
fn test_auflia_const_array_model_eq_single_store_8596() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (select a x) 1))
(assert (= (select a y) 1))
(assert (= a (store ((as const (Array Int Int)) 0) x 1)))
(assert (>= y 0))
(assert (<= y 10))
(assert (>= x 0))
(assert (<= x 10))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.len(),
        1,
        "expected exactly one output, got: {outputs:?}"
    );
    assert_eq!(
        outputs[0].trim(),
        "sat",
        "const array with single store should be sat (x = y): {outputs:?}"
    );
}

/// Two const arrays with stores: `a = store(const(0), z, 3)` and
/// `b = store(const(0), z, 7)`. Constraint: `select(a, x) + select(b, y) = 10`.
///
/// SAT when x = z and y = z: select(a, z) = 3, select(b, z) = 7, sum = 10.
/// Requires the array theory to request model equalities x = z and y = z.
///
/// Z3 confirms SAT.
#[test]
#[timeout(30_000)]
fn test_auflia_const_array_model_eq_two_arrays_8596() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (+ (select a x) (select b y)) 10))
(assert (= (select a z) 3))
(assert (= (select b z) 7))
(assert (= a (store ((as const (Array Int Int)) 0) z 3)))
(assert (= b (store ((as const (Array Int Int)) 0) z 7)))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.len(),
        1,
        "expected exactly one output, got: {outputs:?}"
    );
    assert_eq!(
        outputs[0].trim(),
        "sat",
        "two const arrays requiring x=z, y=z should be sat: {outputs:?}"
    );
}

/// Variant: const array with store and explicit disequality constraint.
///
/// `a = store(const(0), x, 5)` with `select(a, y) = 5` and `x != y`.
/// This is UNSAT: the only way select(a, y) = 5 is if y = x (the stored
/// index), but x != y is asserted.
///
/// Verifies that the model equality mechanism doesn't produce false SAT
/// when the formula genuinely requires UNSAT.
#[test]
#[timeout(30_000)]
fn test_auflia_const_array_model_eq_with_diseq_unsat_8596() {
    let outputs = crate::common::solve_vec(
        r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= a (store ((as const (Array Int Int)) 0) x 5)))
(assert (= (select a y) 5))
(assert (not (= x y)))
(assert (>= x 0))
(assert (<= x 10))
(assert (>= y 0))
(assert (<= y 10))
(check-sat)
"#,
    );
    assert_eq!(
        outputs.len(),
        1,
        "expected exactly one output, got: {outputs:?}"
    );
    assert_eq!(
        outputs[0].trim(),
        "unsat",
        "const array with forced disequality should be unsat: {outputs:?}"
    );
}
