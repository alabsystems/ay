// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for LIA incremental push/pop correctness.
//!
//! These tests exercise the interaction between incremental LIA solving
//! and push/pop scope management. The key invariant: assertions added inside
//! a push scope must not leak into subsequent scopes after pop.
//!
//! Regression context: issue #2777 fixed a scope-sync bug between SMT scopes and
//! `lia_persistent_sat`. These tests ensure scope soundness stays intact across
//! incremental path and fallback interleavings.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Basic push/pop with LIA incremental path (no equality substitution).
/// Scoped assertions must not leak after pop.
#[test]
#[timeout(10_000)]
fn test_lia_incremental_push_pop_no_leak() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        ; Base: x + y = 10
        (assert (= (+ x y) 10))

        ; First check: SAT (creates lia_persistent_sat)
        (check-sat)

        ; Push and add constraint x >= 100 (contradicts x+y=10 with y>=0...
        ; actually x+y=10 allows x=100,y=-90, so add more)
        (push 1)
        (assert (>= x 100))
        (assert (>= y 100))
        ; x >= 100 AND y >= 100 AND x + y = 10 is UNSAT
        (check-sat)
        (pop 1)

        ; After pop, only x + y = 10 survives. Should be SAT.
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Interleaved incremental/fallback across push/pop scopes.
/// Tests the scenario where:
/// 1. Incremental path used at global scope (creates lia_persistent_sat)
/// 2. Push + equality assertion triggers fallback to non-incremental
/// 3. Pop
/// 4. Incremental path used again (lia_persistent_sat was never pushed/popped)
#[test]
#[timeout(10_000)]
fn test_lia_incremental_fallback_interleave() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        ; Base: x + y >= 0
        (assert (>= (+ x y) 0))

        ; First check: incremental (SAT)
        (check-sat)

        ; Push and add equality (triggers non-incremental fallback)
        (push 1)
        (declare-const z Int)
        (assert (= z (+ x 1)))
        (assert (> z 1000))
        ; z > 1000 and z = x+1 and x+y >= 0 is SAT (x=1000, y=-1000, z=1001)
        (check-sat)
        (pop 1)

        ; After pop: only x + y >= 0. Should be SAT.
        (check-sat)

        ; Push different constraint
        (push 1)
        (assert (< x (- 0 5)))
        ; x < -5 and x + y >= 0 is SAT (x=-6, y=6)
        (check-sat)
        (pop 1)

        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat", "sat"]);
}

/// Multiple push/pop cycles with LIA incremental path.
/// Tests that assertion activations from earlier scopes don't accumulate.
#[test]
#[timeout(10_000)]
fn test_lia_incremental_multi_push_pop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)

        ; Base: x >= 0
        (assert (>= x 0))

        (check-sat)

        ; Scope 1: x >= 100
        (push 1)
        (assert (>= x 100))
        (check-sat)
        (pop 1)

        ; Scope 2: x <= 5 — should be SAT if scope 1 didn't leak
        (push 1)
        (assert (<= x 5))
        (check-sat)
        (pop 1)

        ; Scope 3: x = 3 — should be SAT
        (push 1)
        (assert (<= x 3))
        (assert (>= x 3))
        (check-sat)
        (pop 1)

        ; Global check: just x >= 0
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat", "sat"]);
}

/// Nested push/pop with LIA incremental path.
/// Tests scope depth > 1 handling.
#[test]
#[timeout(10_000)]
fn test_lia_incremental_nested_push_pop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        (assert (>= x 0))
        (assert (>= y 0))

        ; Level 0: SAT
        (check-sat)

        (push 1)
        (assert (<= x 10))
        ; Level 1: SAT (0 <= x <= 10, y >= 0)
        (check-sat)

        (push 1)
        (assert (>= x 20))
        ; Level 2: UNSAT (x <= 10 AND x >= 20)
        (check-sat)
        (pop 1)

        ; Back to level 1: SAT (0 <= x <= 10, y >= 0)
        (check-sat)
        (pop 1)

        ; Back to level 0: SAT (x >= 0, y >= 0)
        (check-sat)

        ; Verify no leaks: x = -1 should be UNSAT at level 0 (x >= 0)
        ; but x = 100 should be SAT (no x <= 10 leaked)
        (push 1)
        (assert (>= x 100))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["sat", "sat", "unsat", "sat", "sat", "sat"]
    );
}

/// Regression test for #2822: global assertions must survive scope cycling.
///
/// The bug: pre-push LIA assertions were encoded with an activation literal
/// scoped to the push level, then deactivated after pop. This test verifies
/// that global constraints remain active across push/pop cycles by checking
/// that a scoped constraint contradicting a global one produces UNSAT.
#[test]
#[timeout(10_000)]
fn test_lia_global_assertion_survives_scope_cycle() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)

        (assert (>= x 0))
        (assert (< x 10))
        (check-sat)

        (push 1)
        (assert (>= x 5))
        (check-sat)
        (pop 1)

        ; Second scope: x >= 10 contradicts global x < 10
        ; If global x < 10 was lost after first pop, this would be SAT
        (push 1)
        (assert (>= x 10))
        (check-sat)
        (pop 1)

        ; Global constraints still hold
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "unsat", "sat"]);
}

/// Regression for #6661: if the first solve happens after `push`, global
/// assertions that require preprocessing must still survive the later `pop`.
#[test]
#[timeout(10_000)]
fn test_lia_preprocessed_global_assertion_survives_scope_cycle() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)

        ; Global assertion needs preprocessing.
        (assert (= (mod x 3) 0))

        ; First solve happens only after push, so pre-push tracking must still
        ; keep the global assertion active after the pop.
        (push 1)
        (assert (>= x 0))
        (check-sat)
        (pop 1)

        ; x = 1 contradicts the global mod constraint. If the global assertion
        ; was incorrectly scoped to the popped frame, this would become SAT.
        (push 1)
        (assert (= x 1))
        (check-sat)
        (pop 1)

        ; The global constraint alone is still satisfiable.
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Regression for native #6661/#6687 preprocessing: if the first solve happens
/// in a nested scope, derived assertions must attach to the shallowest source
/// scope rather than the current deepest scope.
#[test]
#[timeout(10_000)]
fn test_lia_preprocessed_parent_scope_survives_nested_first_solve() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        ; Global mod constraint: y is divisible by 3.
        (assert (= (mod y 3) 0))

        ; Scope 1 introduces equality substitution.
        (push 1)
        (assert (= y (+ x 1)))

        ; First solve only happens in nested scope 2.
        (push 1)
        (assert (>= x 2))
        (check-sat)
        (pop 1)

        ; Back at scope 1, y = x+1 must still interact with the global mod constraint.
        ; x = 0 forces y = 1, which violates y mod 3 = 0.
        (push 1)
        (assert (= x 0))
        (check-sat)
        (pop 1)

        ; After popping scope 1, only the global mod constraint remains.
        ; y = 1 is still inconsistent with the global constraint.
        (push 1)
        (assert (= y 1))
        (check-sat)
        (pop 1)

        ; The base global constraint is satisfiable.
        (check-sat)
    "#;

    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "unsat", "sat"]);
}

/// Proof-enabled push/pop must preserve structured LIA conflict proofs (#6725).
///
/// Uses a multi-variable sum constraint so that bound axiom injection on
/// individual variables does not create a SAT-level conflict. The theory
/// solver must detect the infeasibility of x+y >= 10 with x <= 3, y <= 3.
#[test]
#[timeout(10_000)]
fn test_lia_incremental_push_pop_proof_uses_lia_generic_6725() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (>= (+ x y) 10))
        (assert (<= x 3))
        (assert (<= y 3))
        (check-sat)
        (get-proof)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(output.len(), 2);
    assert_eq!(output[0].trim(), "unsat");
    // The split-loop theory dispatch should produce a structured theory
    // annotation (lia_generic or la_generic/lra_farkas) instead of trust.
    let proof = &output[1];
    let has_structured_rule = proof.contains(":rule lia_generic")
        || proof.contains(":rule la_generic")
        || proof.contains(":rule lra_farkas");
    assert!(
        has_structured_rule,
        "expected structured theory proof rule (lia_generic/la_generic/lra_farkas) in push/pop LIA path:\n{proof}",
    );
    assert!(
        !proof.contains(":rule trust"),
        "push/pop LIA proof must not fall back to trust:\n{proof}",
    );
}
