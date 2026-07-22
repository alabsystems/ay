// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for NRA double-push scope leak (#6183).
//!
//! The NRA solver pushes two LRA scopes during check():
//!   1. Sign-cut scope (lib.rs:322) — model-derived sign bounds
//!   2. Patch scope (patch.rs:245) — tentative monomial patches
//!
//! Before the fix, `undo_tentative_patch()` used a boolean flag and
//! only popped ONE scope. This leaked the sign-cut scope's model-derived
//! bounds into future queries, potentially causing false UNSAT when the
//! leaked bounds excluded valid solutions.
//!
//! This test exercises the incremental path (push/pop) where sign-cut
//! scope leak would cause the second check-sat to fail.

use ntest::timeout;

/// Test that NRA correctly handles two queries where the first triggers
/// sign-cut + tentative patch, and the second should be SAT with a
/// different sign assignment.
///
/// If the sign-cut scope leaks, the second query inherits model-dependent
/// bounds (e.g., x > 0) that exclude the valid solution (e.g., x = -2).
#[test]
#[timeout(30_000)]
fn nra_scope_leak_incremental_sign_change() {
    // First check-sat: x > 0 AND x * y = 6 AND y > 0
    // This should be SAT (e.g., x=2, y=3). The NRA solver will push
    // sign-cut scope (x > 0, y > 0) and try_tentative_patch.
    //
    // Second check-sat (after pop + new assertions):
    // x < 0 AND x * y = 6 AND y < 0
    // This should also be SAT (e.g., x=-2, y=-3). If sign-cut scope
    // leaked x > 0 from the first query, this would be UNSAT.
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)

        (push 1)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (assert (= (* x y) 6.0))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (< x 0.0))
        (assert (< y 0.0))
        (assert (= (* x y) 6.0))
        (check-sat)
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // Both queries should be SAT (or at worst unknown — not unsat)
    assert_ne!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "x > 0 AND y > 0 AND x*y = 6 is SAT (e.g., x=2, y=3)"
    );
    assert_ne!(
        outputs.get(1).map(String::as_str),
        Some("unsat"),
        "x < 0 AND y < 0 AND x*y = 6 is SAT (e.g., x=-2, y=-3). \
         If this fails, sign-cut scope leaked from the first query."
    );
}

/// Simpler scope leak test: two queries with opposite variable signs.
/// Both queries are satisfiable. The second query's SAT depends on
/// the first query's sign-cut scope being fully cleaned up.
#[test]
#[timeout(30_000)]
fn nra_scope_leak_opposite_sign_queries() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)

        (push 1)
        (assert (> x 1.0))
        (assert (< (* x x) 10.0))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (< x (- 1.0)))
        (assert (< (* x x) 10.0))
        (check-sat)
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // First: x > 1 AND x^2 < 10 → SAT (e.g., x=2)
    assert_ne!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "x > 1 AND x^2 < 10 is SAT (e.g., x=2)"
    );
    // Second: x < -1 AND x^2 < 10 → SAT (e.g., x=-2)
    assert_ne!(
        outputs.get(1).map(String::as_str),
        Some("unsat"),
        "x < -1 AND x^2 < 10 is SAT (e.g., x=-2). \
         Failure indicates sign-cut scope leak."
    );
}
