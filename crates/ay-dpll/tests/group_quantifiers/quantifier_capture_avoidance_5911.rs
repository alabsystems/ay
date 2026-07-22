// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end tests for issue #5911: capture-avoiding substitution in
//! quantifier instantiation.
//!
//! These tests exercise the full solver pipeline (frontend → preprocessing →
//! Skolemization → E-matching/CEGQI → SAT) with nested quantifiers where
//! inner and outer scopes share variable names. The key invariant: substituting
//! a term for an outer variable must never corrupt an inner variable with the
//! same name.

use ntest::timeout;

/// Nested forall with same-named bound variables.
///
/// (forall ((x Int)) (forall ((x Int)) (= x 0))) says "for all x, for all x,
/// x = 0" which is equivalent to "for all y, 0 = 0" (the inner x shadows the
/// outer x). This is UNSAT because the inner forall claims every integer is 0.
///
/// If capture-avoidance is broken, the outer x substitution could leak into the
/// inner forall, producing a SAT result (the solver would think the inner body
/// only needs to hold for the specific outer x value).
#[test]
#[timeout(30_000)]
fn test_nested_forall_same_name_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (= (f a) 5))
        (assert (forall ((x Int))
          (! (forall ((x Int)) (= x 0))
             :pattern ((f x)))))
        (check-sat)
    "#,
    );
    // Inner forall (= x 0) is false (not every int is 0).
    // Accept unsat or unknown (CEGQI may not be complete).
    // MUST NOT return sat — that would indicate capture failure.
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "Must not return SAT (would indicate capture failure): got {result:?}",
    );
}

/// Exists-forall with Skolem function depending on outer variable.
///
/// (forall ((y Int)) (exists ((x Int)) (> x y)))
/// This is SAT: for any y, choose x = y + 1.
/// Skolemization: x → sk(y) where sk depends on the outer y.
///
/// The key test: after Skolemization, the formula becomes
/// (forall ((y Int)) (> (sk y) y)) which should be satisfiable.
/// If Skolem functions don't correctly reference the outer variable,
/// sk becomes a constant and the formula may wrongly become UNSAT.
#[test]
#[timeout(30_000)]
fn test_skolem_function_references_outer_universal() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic LIA)
        (assert (forall ((y Int)) (exists ((x Int)) (> x y))))
        (check-sat)
    "#,
    );
    // SAT: for any y, x = y + 1 works. Accept sat or unknown.
    // UNSAT would indicate Skolem function lost its dependency on y.
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "Must not return UNSAT (would indicate broken Skolem dependency): got {result:?}",
    );
}

/// Exact reproduction of #5911: forall-exists-forall with y-shadowing.
///
/// (forall ((y Int)) (exists ((x Int)) (forall ((y Int)) (> (+ x y) 0))))
///
/// Skolemization of exists x produces x → sk(y) where y is the outer universal.
/// If capture-avoidance is broken, the free y in sk(y) gets captured by the
/// inner forall's binding of y, changing the semantics.
///
/// The formula is satisfiable: for any outer y, choose x = 1; then inner
/// forall y. (1 + y > 0) is false (y = -2 gives -1). So with correct scoping
/// the whole formula is UNSAT (the inner forall is too strong). With broken
/// capture, the inner y refers to the Skolem's y, collapsing the formula.
#[test]
#[timeout(30_000)]
fn test_issue_5911_exact_reproduction_forall_exists_forall_y_shadow() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic LIA)
        (assert (forall ((y Int))
          (exists ((x Int))
            (forall ((y Int))
              (> (+ x y) 0)))))
        (check-sat)
    "#,
    );
    // Inner forall says (x + y > 0) for ALL y. No x satisfies this (y can be
    // arbitrarily negative). So the exists has no witness, and the whole formula
    // is UNSAT. Accept unsat or unknown (quantifier alternation may be incomplete).
    // MUST NOT return sat — that would indicate the inner y was captured.
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "Must not return SAT (would indicate #5911 capture bug): got {result:?}",
    );
}

/// Triple-nested quantifier scoping with distinct variable names at each level.
///
/// forall x. exists y. forall z. (x + y > z)
/// This is UNSAT: for any x and y, there exists z > x+y.
#[test]
#[timeout(30_000)]
fn test_triple_nested_quantifier_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (forall ((z Int)) (> (+ x y) z)))))
        (check-sat)
    "#,
    );
    // UNSAT or unknown (quantifier alternation may be incomplete).
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "Must not return SAT: got {result:?}",
    );
}

/// Let-binding shadowing: substitution must respect let-bound variable scope.
///
/// (forall ((x Int)) (let ((y (+ x 1))) (> y 0)))
/// After substituting x=a, should get (let ((y (+ a 1))) (> y 0)).
/// The y inside the let body must refer to the let-bound y, not any outer y.
#[test]
#[timeout(30_000)]
fn test_let_binding_shadow_in_quantifier() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (= y (- 5)))
        (assert (forall ((x Int)) (let ((y (+ x 1))) (> y 0))))
        (check-sat)
    "#,
    );
    // The forall says for all x, x+1 > 0, which is false (x = -1 gives 0, not > 0).
    // Accept unsat or unknown. SAT would be wrong.
    // Actually: x+1 > 0 iff x > -1, so x = -2 gives -1 which is not > 0. UNSAT.
    // The key is that the outer y = -5 must not leak into the let-bound y.
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "Must not return SAT: got {result:?}",
    );
}
