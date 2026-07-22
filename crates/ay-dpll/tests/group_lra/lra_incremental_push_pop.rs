// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for LRA incremental push/pop correctness.
//!
//! Mirrors lia_incremental_push_pop.rs pattern for linear real arithmetic.
//! Key invariant: rational constraints asserted inside a push scope must not
//! leak after pop.
//!
//! Part of #2812

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Basic push/pop: scoped bound must not leak.
#[test]
#[timeout(10_000)]
fn test_lra_incremental_push_pop_no_leak() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)

        ; Base: x + y = 10.0
        (assert (= (+ x y) 10.0))
        (check-sat)

        ; Push: x >= 100 AND y >= 100 contradicts x + y = 10
        (push 1)
        (assert (>= x 100.0))
        (assert (>= y 100.0))
        (check-sat)
        (pop 1)

        ; After pop: only x + y = 10 => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Multiple push/pop cycles with LRA.
#[test]
#[timeout(10_000)]
fn test_lra_incremental_multi_push_pop() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)

        ; Base: x >= 0
        (assert (>= x 0.0))
        (check-sat)

        ; Scope 1: x >= 100
        (push 1)
        (assert (>= x 100.0))
        (check-sat)
        (pop 1)

        ; Scope 2: x <= 0.5 — SAT if scope 1 didn't leak
        (push 1)
        (assert (<= x 0.5))
        (check-sat)
        (pop 1)

        ; Scope 3: x = 0.25
        (push 1)
        (assert (<= x 0.25))
        (assert (>= x 0.25))
        (check-sat)
        (pop 1)

        ; Global: just x >= 0
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat", "sat"]);
}

/// Nested push/pop with LRA.
#[test]
#[timeout(10_000)]
fn test_lra_incremental_nested_push_pop() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)

        (assert (>= x 0.0))
        (assert (>= y 0.0))

        ; Level 0: SAT
        (check-sat)

        (push 1)
        (assert (<= x 10.0))
        ; Level 1: 0 <= x <= 10, y >= 0 => SAT
        (check-sat)

        (push 1)
        (assert (>= x 20.0))
        ; Level 2: x <= 10 AND x >= 20 => UNSAT
        (check-sat)
        (pop 1)

        ; Back to level 1: SAT
        (check-sat)
        (pop 1)

        ; Back to level 0: SAT
        (check-sat)

        ; Verify no leak: x = 100 should be SAT (no x <= 10 leaked)
        (push 1)
        (assert (>= x 100.0))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["sat", "sat", "unsat", "sat", "sat", "sat"]
    );
}

/// Strict inequalities with LRA incremental push/pop.
/// Tests non-strict inequality contradiction after prior push/pop cycle.
#[test]
#[timeout(10_000)]
fn test_lra_incremental_contradiction_after_pop() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)

        ; Base: x > 0
        (assert (> x 0.0))
        (check-sat)

        ; Push: x = -1 contradicts x > 0 => UNSAT
        (push 1)
        (assert (= x (- 1.0)))
        (check-sat)
        (pop 1)

        ; After pop: x > 0 => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat", "sat"]);
}

/// Proof-enabled push/pop must preserve structured arithmetic proofs (#6716).
#[test]
#[timeout(10_000)]
fn test_lra_incremental_push_pop_proof_uses_la_generic_6716() {
    let smt = r#"
        (set-logic QF_LRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (push 1)
        (assert (> x 1))
        (assert (< x 0))
        (check-sat)
        (get-proof)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(output.len(), 2);
    assert_eq!(output[0].trim(), "unsat");
    assert!(
        output[1].contains(":rule la_generic"),
        "expected la_generic proof in push/pop LRA path:\n{}",
        output[1]
    );
    assert!(
        output[1].contains(":args ("),
        "expected la_generic proof arguments in push/pop LRA path:\n{}",
        output[1]
    );
    assert!(
        !output[1].contains(":rule trust"),
        "push/pop LRA proof must not fall back to trust:\n{}",
        output[1]
    );
}
