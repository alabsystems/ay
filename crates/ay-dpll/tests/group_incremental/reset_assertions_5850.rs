// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for (reset-assertions) incremental state cleanup (#5850).
//!
//! Verifies that (reset-assertions) properly clears all executor incremental
//! state (persistent SAT solvers, scope stacks, activation caches) so
//! subsequent queries are not corrupted by stale learned clauses.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// After reset-assertions, an UNSAT query should become SAT when the
/// contradicting assertion is removed.
#[test]
#[timeout(10_000)]
fn test_reset_assertions_clears_lia_state() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (> x 10))
        (assert (< x 5))
        (check-sat)
        (pop 1)
        (reset-assertions)
        (declare-const y Int)
        (assert (> y 3))
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    let r = results(&out);
    assert_eq!(
        r,
        vec!["unsat", "sat"],
        "After reset-assertions, stale UNSAT state must not persist: {out}"
    );
}

/// After reset-assertions, scoped definitions from prior push/pop
/// do not leak into subsequent solving.
#[test]
#[timeout(10_000)]
fn test_reset_assertions_clears_lra_state() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (assert (= x 3.14))
        (check-sat)
        (pop 1)
        (reset-assertions)
        (declare-const y Real)
        (assert (> y 0.0))
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    let r = results(&out);
    assert_eq!(
        r,
        vec!["sat", "sat"],
        "LRA state must be fresh after reset-assertions: {out}"
    );
}

/// After reset-assertions inside a push scope, scope tracking is reset.
/// Subsequent push/pop should work from depth 0.
#[test]
#[timeout(10_000)]
fn test_reset_assertions_resets_scope_depth() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (push 1)
        (assert (= x 42))
        (check-sat)
        (pop 1)
        (pop 1)
        (reset-assertions)
        (declare-const y Int)
        (push 1)
        (assert (= y 7))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    let r = results(&out);
    assert_eq!(
        r,
        vec!["sat", "sat", "sat"],
        "Scope tracking must be fresh after reset-assertions: {out}"
    );
}

/// After reset-assertions with BV theory, persistent SAT solver is discarded.
#[test]
#[timeout(10_000)]
fn test_reset_assertions_clears_bv_state() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #xFF))
        (assert (= x #x00))
        (check-sat)
        (pop 1)
        (reset-assertions)
        (declare-const y (_ BitVec 8))
        (assert (bvugt y #x00))
        (check-sat)
    "#;
    let out = crate::common::solve(smt);
    let r = results(&out);
    assert_eq!(
        r,
        vec!["unsat", "sat"],
        "BV state must be fresh after reset-assertions: {out}"
    );
}
