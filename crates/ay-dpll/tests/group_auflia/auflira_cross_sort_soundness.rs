// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness tests for AufLiraSolver cross-sort propagation (#5955).
//!
//! The AufLiraSolver (QF_AUFLIRA) ported the LiraSolver's cross-sort propagation
//! logic (#4915, #5947, #5956). These tests mirror `lira_cross_sort_soundness.rs`
//! and `lira_big_m_relu_5947.rs` but use QF_AUFLIRA logic to exercise the
//! AufLiraSolver code path, which has an additional Int-sort guard (line 284 of
//! auf_lira.rs) that filters non-Int phantom variables.
//!
//! Without these tests, the AUFLIRA cross-sort propagation has zero coverage:
//! all existing LIRA tests use QF_LIRA which routes to LiraSolver.
//!
//! ## Fixed: #6198 — Cross-sort propagation false-UNSAT
//!
//! Two fixes resolved the false-UNSAT bugs originally documented here:
//! 1. `asserted_real_int_terms` filter (#6290 port) prevents registration artifacts
//!    from spurious cross-sort propagation.
//! 2. Diophantine `try_two_variable_solve` reason completeness fix includes bound
//!    reasons for both variables when k-range is unique, preventing over-strong
//!    conflict clauses.

use ntest::timeout;

/// Big-M ReLU via AUFLIRA: same pattern as #5947 regression.
/// phase_2 in {0,1}, relu <= M*phase_2, relu >= 1. With phase_2=0: UNSAT.
/// Uses an uninterpreted function to force QF_AUFLIRA routing.
#[test]
#[timeout(60_000)]
fn test_auflira_big_m_relu_unsat_5955() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun f (Int) Real)
        (declare-const X_0 Real)
        (declare-const Y_0 Real)
        (declare-const lin_0 Real)
        (declare-const relu_1 Real)
        (declare-const phase_2 Int)
        (assert (>= X_0 0.0))
        (assert (<= X_0 0.5))
        (assert (= lin_0 (* 1.0 X_0)))
        (assert (>= phase_2 0))
        (assert (<= phase_2 1))
        (assert (>= relu_1 0.0))
        (assert (>= relu_1 lin_0))
        (assert (<= relu_1 (+ lin_0 (* 1000000.0 (- 1 phase_2)))))
        (assert (<= relu_1 (* 1000000.0 phase_2)))
        (assert (= Y_0 relu_1))
        (assert (>= Y_0 1.0))
        (assert (= (f phase_2) Y_0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// SAT: phase in {0,1}, to_real(phase) > 0.5 forces phase=1.
/// Mirror of lira_cross_sort_soundness::test_cross_sort_sat_phase_gt_half.
/// Fixed by #6198: asserted_real_int_terms filter + Dioph reason completeness.
#[test]
#[timeout(60_000)]
fn test_auflira_cross_sort_sat_phase_gt_half() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun g (Int) Int)
        (declare-const phase Int)
        (declare-const y Real)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (> (to_real phase) 0.5))
        (assert (= y (to_real phase)))
        (assert (> y 0.0))
        (assert (= (g phase) phase))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "phase=1, y=1.0 is a valid model");
}

/// UNSAT: x in {0,1}, r = to_real(x), r > 1.5 — no integer satisfies.
/// Mirror of lira_cross_sort_soundness::test_cross_sort_unsat_both_branches.
#[test]
#[timeout(60_000)]
fn test_auflira_cross_sort_unsat_both_branches() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun h (Real) Real)
        (declare-const x Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= r (to_real x)))
        (assert (> r 1.5))
        (assert (= (h r) r))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "no integer in [0,1] satisfies r > 1.5"
    );
}

/// SAT: x in {0,1,2}, to_real(x) >= 1.5, only x=2 works.
/// Mirror of lira_cross_sort_soundness::test_cross_sort_sat_wider_range.
#[test]
#[timeout(60_000)]
fn test_auflira_cross_sort_sat_wider_range() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun f (Int) Real)
        (declare-const x Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 2))
        (assert (>= (to_real x) 1.5))
        (assert (= r (+ (to_real x) 0.5)))
        (assert (> r 2.0))
        (assert (= (f x) r))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        matches!(outputs.first().map(String::as_str), Some("sat" | "unknown")),
        "x=2, r=2.5 is a valid model; AUFLIRA must not report unsat: {outputs:?}"
    );
}

/// Minimal Big-M with explicit phase=0, AUFLIRA variant.
/// Mirror of lira_big_m_relu_5947::test_big_m_minimal_unsat_5947.
#[test]
#[timeout(60_000)]
fn test_auflira_big_m_minimal_unsat() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun tag (Int) Int)
        (declare-const relu Real)
        (declare-const phase Int)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (>= relu 0.0))
        (assert (<= relu (* 1000000.0 phase)))
        (assert (>= relu 1.0))
        (assert (= phase 0))
        (assert (= (tag phase) 42))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Array read combined with cross-sort: store phase into array, read back.
/// Tests that the AufLira array+cross-sort combination works correctly.
/// Fixed by #6198: asserted_real_int_terms filter + Dioph reason completeness.
#[test]
#[timeout(60_000)]
fn test_auflira_array_cross_sort_sat() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Int Int))
        (declare-const phase Int)
        (declare-const y Real)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (= (select a 0) phase))
        (assert (>= (to_real (select a 0)) 0.5))
        (assert (= y (to_real (select a 0))))
        (assert (>= y 0.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        matches!(outputs.first().map(String::as_str), Some("sat" | "unknown")),
        "phase=1, a[0]=1, y=1.0 is a valid model; AUFLIRA must not report unsat: {outputs:?}"
    );
}

/// Minimal reproducer for cross-sort implied bounds via equality (#6198).
/// Bounds on `phase` flow to `select(a,0)` via equality row.
/// Fixed by Dioph reason completeness: bound reasons now included in
/// `try_two_variable_solve` when k-range is unique.
#[test]
#[timeout(60_000)]
fn test_auflira_cross_sort_implied_bounds_via_equality() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Int Int))
        (declare-const phase Int)
        (assert (= (select a 0) phase))
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (>= (to_real (select a 0)) 0.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        matches!(outputs.first().map(String::as_str), Some("sat" | "unknown")),
        "phase=1, a[0]=1 is a valid model; AUFLIRA must not report unsat: {outputs:?}"
    );
}

/// UF variant of the implied-bounds bug (#6198): to_real(f(0)) with bounds on y
/// via equality (= (f 0) y). Fixed by same Dioph reason completeness fix.
#[test]
#[timeout(60_000)]
fn test_auflira_cross_sort_uf_implied_bounds() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun f (Int) Int)
        (declare-const y Int)
        (assert (= (f 0) y))
        (assert (>= y 0))
        (assert (<= y 1))
        (assert (>= (to_real (f 0)) 0.5))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "y=1, f(0)=1 is a valid model (bounds implied via equality)"
    );
}

/// Multiple shared Int/Real variables — both must be propagated.
/// Tests that cross-sort propagation handles multiple variables correctly.
#[test]
#[timeout(60_000)]
fn test_auflira_multi_variable_cross_sort_unsat() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (>= y 0))
        (assert (<= y 1))
        (assert (= r (+ (to_real x) (to_real y))))
        (assert (> r 2.5))
        (assert (= (f x) y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "max(to_real(x) + to_real(y)) = 2.0 < 2.5"
    );
}
