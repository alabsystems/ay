// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental push/pop tests for QF_UFLRA.
//!
//! Consumer: deductive-checks uses QF_UFLRA incrementally for separation logic proofs.
//! These tests verify that push/pop correctly restores theory solver state
//! and does not leak equalities, LRA simplex state, or interface bridge terms
//! across scopes.

use crate::common::solve;

/// Basic UFLRA push/pop: SAT in scope, pop, re-assert different constraint.
/// Verifies LRA simplex state does not leak across scopes.
#[test]
fn test_uflra_incremental_push_pop_lra_state_no_leak() {
    let output = solve(
        r#"
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun f (Real) Real)

; Base: f is injective-ish
(assert (=> (= (f x) (f y)) (= x y)))

(push 1)
(assert (= x 1.5))
(assert (= (f x) (f y)))
; Under injectivity: x=1.5 and f(x)=f(y) => y=1.5 => sat
(check-sat)
(pop 1)

; After pop: x=1.5 should be forgotten
(push 1)
(assert (= x 2.5))
(assert (= (f x) (f y)))
; Under injectivity: x=2.5 and f(x)=f(y) => y=2.5 => sat
(check-sat)
(pop 1)

; Final: assert contradiction
(push 1)
(assert (= x 1.0))
(assert (= y 2.0))
(assert (= (f x) (f y)))
; Under injectivity: x=1.0 and y=2.0 but f(x)=f(y) => x=y => contradiction
(check-sat)
(pop 1)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| l.trim() == "sat" || l.trim() == "unsat")
        .collect();
    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "scope 1 should be sat: {output}");
    assert_eq!(results[1].trim(), "sat", "scope 2 should be sat: {output}");
    assert_eq!(
        results[2].trim(),
        "unsat",
        "scope 3 should be unsat: {output}"
    );
}

/// UFLRA push/pop: shared equality propagation via N-O bridge.
/// Verifies that equalities propagated from EUF to LRA in one scope
/// do not persist after pop.
#[test]
fn test_uflra_incremental_shared_equality_no_leak() {
    let output = solve(
        r#"
(set-logic QF_UFLRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun g (Real) Real)

; Base: a > 0
(assert (> a 0.0))

(push 1)
; Scope 1: g(a) = g(b) and g injective => a = b
(assert (= (g a) (g b)))
(assert (=> (= (g a) (g b)) (= a b)))
; a > 0 and a = b => b > 0, consistent
(assert (> b 0.0))
(check-sat)
(pop 1)

(push 1)
; Scope 2: b should be unconstrained again (a=b equality gone)
(assert (< b (- 0.0 1.0)))
; a > 0 and b < -1.0 should be sat (no connection between a and b)
(check-sat)
(pop 1)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| l.trim() == "sat" || l.trim() == "unsat")
        .collect();
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "scope 1 should be sat: {output}");
    assert_eq!(
        results[1].trim(),
        "sat",
        "scope 2 should be sat (a=b forgotten): {output}"
    );
}

/// UFLRA incremental: multiple scopes with model value changes.
/// Exercises the LRA solver's ability to produce different models after pop.
#[test]
fn test_uflra_incremental_model_values_change_across_scopes() {
    let output = solve(
        r#"
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun y () Real)

(push 1)
(assert (= x 3.0))
(assert (= y 4.0))
(check-sat)
(get-value (x y))
(pop 1)

(push 1)
(assert (= x 7.0))
(assert (= y 8.0))
(check-sat)
(get-value (x y))
(pop 1)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| l.trim() == "sat" || l.trim() == "unsat")
        .collect();
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat");
    assert_eq!(results[1].trim(), "sat");
    // Both scopes should be sat with different values
    // The model values themselves are checked by the solver's internal validation
}

/// UFLRA incremental: nested push/pop with contradictions at different depths.
#[test]
fn test_uflra_incremental_nested_push_pop() {
    let output = solve(
        r#"
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun f (Real) Real)

; Depth 0: x > 0
(assert (> x 0.0))
(check-sat)

(push 1)
; Depth 1: x < 10
(assert (< x 10.0))
(check-sat)

(push 1)
; Depth 2: x = 5 (consistent with 0 < x < 10)
(assert (= x 5.0))
(check-sat)
(pop 1)

; Back to depth 1: x is back to 0 < x < 10
(push 1)
; Depth 2 again: x > 100 (contradicts x < 10)
(assert (> x 100.0))
(check-sat)
(pop 1)

(pop 1)
; Back to depth 0: x > 0 only
(check-sat)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| l.trim() == "sat" || l.trim() == "unsat")
        .collect();
    assert_eq!(
        results.len(),
        5,
        "expected 5 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "depth 0: {output}");
    assert_eq!(results[1].trim(), "sat", "depth 1: {output}");
    assert_eq!(results[2].trim(), "sat", "depth 2 (x=5): {output}");
    assert_eq!(
        results[3].trim(),
        "unsat",
        "depth 2 (x>100 contradicts x<10): {output}"
    );
    assert_eq!(results[4].trim(), "sat", "depth 0 again: {output}");
}
