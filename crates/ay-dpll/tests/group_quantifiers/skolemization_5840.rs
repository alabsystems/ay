// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #5840: Existential Skolemization.
//!
//! Tests that positive `Exists` and negative `Forall` quantifiers are
//! Skolemized (bound variables replaced with fresh constants) so the
//! solver can find satisfying assignments without relying on E-matching.

use ntest::timeout;

/// Acceptance criterion: `(assert (exists ((x Int)) (= x 5)))` returns sat.
///
/// Without Skolemization, the E-matching engine may return Unknown because
/// there is no ground term to trigger on. With Skolemization, the exists is
/// replaced by `(= sk!x 5)`, which is trivially satisfiable.
#[test]
#[timeout(10000)]
fn test_simple_exists_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (exists ((x Int)) (= x 5)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "simple exists should be sat");
}

/// Acceptance criterion: `(assert (not (forall ((x Int)) (not (= x 5)))))` returns sat.
///
/// `not(forall x. not(= x 5))` ≡ `exists x. (= x 5)` — Skolemization
/// replaces x with a fresh constant and the body becomes `(= sk 5)`.
#[test]
#[timeout(10000)]
fn test_negated_forall_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (not (forall ((x Int)) (not (= x 5)))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "negated forall (= hidden exists) should be sat"
    );
}

/// Multi-variable existential: exists x, y such that x + y = 10.
#[test]
#[timeout(10000)]
fn test_multi_variable_exists_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (exists ((x Int) (y Int)) (= (+ x y) 10)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "multi-variable exists should be sat");
}

/// Existential combined with ground constraints.
///
/// The existential claims there is some x = a, combined with a >= 5.
/// This is satisfiable (e.g., a = 5, x = 5).
#[test]
#[timeout(10000)]
fn test_exists_with_ground_constraint() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun a () Int)
        (assert (>= a 5))
        (assert (exists ((x Int)) (= x a)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "exists with ground constraint should be sat"
    );
}

/// Unsatisfiable existential: exists x such that x > x.
///
/// This is UNSAT regardless of Skolemization — the Skolemized body
/// `(> sk sk)` is immediately false.
#[test]
#[timeout(10000)]
fn test_exists_unsat() {
    let smt = r#"
        (set-logic LIA)
        (assert (exists ((x Int)) (> x x)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["unsat"], "exists x. x > x should be unsat");
}

/// Mixed quantifiers: forall combined with exists (both at top level).
///
/// forall x. x + 1 > x is valid (SAT).
/// exists y. y = 0 is satisfiable.
/// Together the formula is SAT.
#[test]
#[timeout(10000)]
fn test_forall_and_exists_mixed() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (> (+ x 1) x)))
        (assert (exists ((y Int)) (= y 0)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "valid forall + simple exists should be sat"
    );
}

/// LRA existential: exists a real x equal to 1.5.
#[test]
#[timeout(10000)]
fn test_exists_real_sat() {
    let smt = r#"
        (set-logic LRA)
        (assert (exists ((x Real)) (= x 1.5)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "real-valued exists should be sat");
}

/// Boolean existential: exists a Bool b such that b is true.
#[test]
#[timeout(10000)]
fn test_exists_bool_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (exists ((b Bool)) b))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "bool exists should be sat");
}

// ---- Deep Skolemization tests (existentials nested inside Boolean connectives) ----

/// Existential nested inside AND at assertion level.
///
/// `(and (exists ((x Int)) (= x 5)) (> y 0))` should Skolemize the exists
/// to `(and (= sk!x 5) (> y 0))`, which is SAT with y=1.
#[test]
#[timeout(10000)]
fn test_exists_nested_in_and() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun y () Int)
        (assert (and (exists ((x Int)) (= x 5)) (> y 0)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "exists nested inside and should be Skolemized and sat"
    );
}

/// Negated forall nested inside AND: `(and (not (forall x. x > 0)) (= y 5))`.
///
/// `not(forall x. x > 0)` ≡ `exists x. not(x > 0)` → Skolemized to `not(sk > 0)`,
/// combined with `y = 5` is SAT.
#[test]
#[timeout(10000)]
fn test_neg_forall_nested_in_and() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun y () Int)
        (assert (and (not (forall ((x Int)) (> x 0))) (= y 5)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "not(forall) nested inside and should be Skolemized and sat"
    );
}

/// Existential nested inside OR: `(or (exists x. x > 100 and x < 0) (> y 0))`.
///
/// The existential is UNSAT (no x satisfies x > 100 and x < 0), but the
/// disjunction is SAT because (> y 0) is satisfiable.
#[test]
#[timeout(10000)]
fn test_exists_nested_in_or() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun y () Int)
        (assert (or (exists ((x Int)) (and (> x 100) (< x 0))) (> y 0)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "exists nested inside or should be Skolemized and sat"
    );
}

/// Multiple existentials nested inside AND.
///
/// `(and (exists ((x Int)) (= x 5)) (exists ((y Int)) (= y 10)))` →
/// Skolemized to `(and (= sk!x 5) (= sk!y 10))`, SAT.
#[test]
#[timeout(10000)]
fn test_multiple_exists_nested_in_and() {
    let smt = r#"
        (set-logic LIA)
        (assert (and (exists ((x Int)) (= x 5)) (exists ((y Int)) (= y 10))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "multiple exists nested inside and should be sat"
    );
}
