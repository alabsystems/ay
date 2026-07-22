// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Performance regression tests for LRA simplex pivot operations.
//!
//! These tests exercise the simplex solver with wide rows (many variables per
//! constraint) to guard against complexity regressions in the pivot operation.
//!
//! Key complexity findings (P1:105 performance_proofs audit):
//! - `add_sparse_term` uses sorted Vec with O(n) insert/remove per call
//! - Pivot temp allocation: O(R * w) temporary Vecs per pivot for col_index diff
//! - `col_index_add` has O(col_size) defensive contains() check
//! - Total pivot cost: O(R * (w^2 + w * col_size)) where R = affected rows, w = row width
//!
//! Reference: simplex.rs:543-585, types.rs:18-31

use ntest::timeout;

/// Wide-row SAT: 20 variables in a single sum constraint.
/// Tests that simplex pivot handles wide rows without excessive slowdown.
/// At w=20, per-pivot cost is O(20^2)=400 operations (acceptable).
/// Timeout guards against regression to O(n^3) or worse.
#[test]
#[timeout(5_000)]
fn test_lra_wide_row_20_vars_sat() {
    // Sum of 20 variables = 100, each in [0, 10]
    let mut smt = String::from("(set-logic QF_LRA)\n");
    for i in 0..20 {
        smt.push_str(&format!("(declare-const x{i} Real)\n"));
    }
    for i in 0..20 {
        smt.push_str(&format!("(assert (>= x{i} 0.0))\n"));
        smt.push_str(&format!("(assert (<= x{i} 10.0))\n"));
    }
    // Sum constraint: x0 + x1 + ... + x19 = 100
    let sum_terms: Vec<String> = (0..20).map(|i| format!("x{i}")).collect();
    smt.push_str(&format!("(assert (= (+ {}) 100.0))\n", sum_terms.join(" ")));
    smt.push_str("(check-sat)\n");

    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "20-var sum constraint with feasible bounds must be SAT"
    );
}

/// Dense system: 10 variables with 5 overlapping sum constraints.
/// Forces multiple pivots with row substitution across shared variables.
/// Tests that col_index maintenance doesn't blow up with many shared columns.
#[test]
#[timeout(5_000)]
fn test_lra_dense_system_10_vars_5_constraints() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x0 Real) (declare-const x1 Real)
(declare-const x2 Real) (declare-const x3 Real)
(declare-const x4 Real) (declare-const x5 Real)
(declare-const x6 Real) (declare-const x7 Real)
(declare-const x8 Real) (declare-const x9 Real)
(assert (>= x0 0.0)) (assert (<= x0 10.0))
(assert (>= x1 0.0)) (assert (<= x1 10.0))
(assert (>= x2 0.0)) (assert (<= x2 10.0))
(assert (>= x3 0.0)) (assert (<= x3 10.0))
(assert (>= x4 0.0)) (assert (<= x4 10.0))
(assert (>= x5 0.0)) (assert (<= x5 10.0))
(assert (>= x6 0.0)) (assert (<= x6 10.0))
(assert (>= x7 0.0)) (assert (<= x7 10.0))
(assert (>= x8 0.0)) (assert (<= x8 10.0))
(assert (>= x9 0.0)) (assert (<= x9 10.0))
; 5 overlapping sum constraints — forces many pivots
(assert (= (+ x0 x1 x2 x3) 20.0))
(assert (= (+ x2 x3 x4 x5) 20.0))
(assert (= (+ x4 x5 x6 x7) 20.0))
(assert (= (+ x6 x7 x8 x9) 20.0))
(assert (= (+ x0 x1 x8 x9) 20.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Dense 10-var system with overlapping constraints must be SAT"
    );
}

/// Wide UNSAT: 15 variables with contradictory bounds.
/// Forces simplex to detect infeasibility through pivot iterations.
#[test]
#[timeout(5_000)]
fn test_lra_wide_row_unsat_contradiction() {
    // x0 + x1 + ... + x14 = 100, but each xi in [0, 5] → max sum = 75 < 100
    let mut smt = String::from("(set-logic QF_LRA)\n");
    for i in 0..15 {
        smt.push_str(&format!("(declare-const x{i} Real)\n"));
    }
    for i in 0..15 {
        smt.push_str(&format!("(assert (>= x{i} 0.0))\n"));
        smt.push_str(&format!("(assert (<= x{i} 5.0))\n"));
    }
    let sum_terms: Vec<String> = (0..15).map(|i| format!("x{i}")).collect();
    smt.push_str(&format!("(assert (= (+ {}) 100.0))\n", sum_terms.join(" ")));
    smt.push_str("(check-sat)\n");

    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "15-var sum=100 with bounds [0,5] must be UNSAT (max=75)"
    );
}

/// Scaling test: 50 variables with chain constraints.
/// Each variable linked to neighbors: xi + x(i+1) <= 5.
/// This creates a sparse system that still requires many pivots.
/// Timeout is generous (10s) to allow for current O(n^2) behavior
/// but would catch O(n^3) or worse regressions.
#[test]
#[timeout(10_000)]
fn test_lra_50_var_chain_constraints() {
    let mut smt = String::from("(set-logic QF_LRA)\n");
    for i in 0..50 {
        smt.push_str(&format!("(declare-const x{i} Real)\n"));
    }
    for i in 0..50 {
        smt.push_str(&format!("(assert (>= x{i} 0.0))\n"));
        smt.push_str(&format!("(assert (<= x{i} 10.0))\n"));
    }
    // Chain constraints: x_i + x_{i+1} <= 5 for adjacent pairs
    for i in 0..49 {
        smt.push_str(&format!("(assert (<= (+ x{} x{}) 5.0))\n", i, i + 1));
    }
    // Force some positive values
    smt.push_str("(assert (>= x0 2.0))\n");
    smt.push_str("(assert (>= x49 2.0))\n");
    smt.push_str("(check-sat)\n");

    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "50-var chain system with feasible bounds must be SAT"
    );
}
