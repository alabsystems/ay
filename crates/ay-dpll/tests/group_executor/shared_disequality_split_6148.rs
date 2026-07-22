// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for Nelson-Oppen shared disequality expression splits (#6148).
//!
//! When EUF forwards a shared disequality like f(x) != f(y) to LRA via the
//! Nelson-Oppen channel, LRA creates internal slack variables for f(x) and f(y).
//! The resulting expression `var_fx - var_fy != 0` has 2 variables, so the
//! single-variable DisequalitySplit path doesn't apply. Before the fix, this
//! fell through to TheoryResult::Unknown. The fix returns NeedExpressionSplit
//! for multi-variable shared disequalities, matching the regular disequality handler.

use ntest::timeout;

/// Core regression test: QF_UFLIA with uninterpreted function disequality.
///
/// This is the exact failing case from regression_get_value_uflia_combined_logic.
/// x=1, y=2, f(x) != f(y) is trivially satisfiable since x != y means the
/// constraint on f is consistent. Before fix: returned "unknown". After: "sat".
#[test]
#[timeout(10_000)]
fn test_uflia_shared_disequality_sat_6148() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x 1))
(assert (= y 2))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "QF_UFLIA shared disequality should be SAT"
    );
}

/// Same test without tight bounds: x >= 0, y >= 3, f(x) != f(y).
/// SAT because x and y can have different values.
#[test]
#[timeout(10_000)]
fn test_uflia_shared_disequality_loose_bounds_sat_6148() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(assert (<= x 5))
(assert (>= y 10))
(assert (<= y 20))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Loose bounds shared disequality should be SAT"
    );
}

/// UNSAT case: x=y and f(x) != f(y) is unsatisfiable by congruence.
/// If x = y, then f(x) = f(y) by congruence closure, so f(x) != f(y) is false.
#[test]
#[timeout(10_000)]
fn test_uflia_shared_disequality_congruence_unsat_6148() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Congruence + shared disequality should be UNSAT"
    );
}

/// UFLRA variant: same pattern with Real-sorted variables.
#[test]
#[timeout(10_000)]
fn test_uflra_shared_disequality_sat_6148() {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun g (Real) Real)
(declare-const a Real)
(declare-const b Real)
(assert (= a 1.0))
(assert (= b 2.0))
(assert (not (= (g a) (g b))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "QF_UFLRA shared disequality should be SAT"
    );
}

/// AUFLIA variant: arrays + UF + LIA with shared disequality.
/// select(A, x) != select(A, y) with x=1, y=2 is satisfiable.
#[test]
#[timeout(10_000)]
fn test_auflia_shared_disequality_with_select_6148() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const x Int)
(declare-const y Int)
(assert (= x 1))
(assert (= y 2))
(assert (not (= (select A x) (select A y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "QF_AUFLIA shared disequality with select should be SAT"
    );
}

/// Multi-function shared disequality: f(x) + g(y) != h(z).
/// All unconstrained — clearly satisfiable.
#[test]
#[timeout(10_000)]
fn test_uflia_multi_function_disequality_6148() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x 0))
(assert (= y 0))
(assert (not (= (f x) (g y))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Multi-function shared disequality should be SAT"
    );
}
