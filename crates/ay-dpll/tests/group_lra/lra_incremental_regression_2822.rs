// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for LRA incremental push/pop bugs.
//!
//! Part of #2822.

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn test_strict_ineq_contradiction_after_scope_cycle() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)

        (assert (> x 0.0))
        (assert (< x 1.0))
        (check-sat)

        (push 1)
        (assert (> x 0.5))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (>= x 1.0))
        (check-sat)
        (pop 1)

        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat", "sat", "unsat", "sat"]);
}
