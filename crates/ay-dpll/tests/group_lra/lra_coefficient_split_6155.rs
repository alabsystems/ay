// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for LRA disequality split with non-unit coefficients (#6155).
//!
//! The LRA solver's DisequalitySplit computes the excluded value as `-constant`
//! without dividing by the coefficient. For `coeff*x + constant = 0`, the
//! excluded value should be `-constant/coeff`, not `-constant`.
//!
//! These tests verify correctness of disequality handling when coefficients
//! are non-trivial (e.g., `2*x != 6` means `x != 3`, not `x != 6`).

use ntest::timeout;

/// Basic: 2*x != 6 means x != 3. With x=3 forced, should be UNSAT.
#[test]
#[timeout(10_000)]
fn test_lra_scaled_disequality_forced_unsat_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* 2.0 x) 6.0)))
(assert (= x 3.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "2*x != 6 with x=3 should be UNSAT");
}

/// 2*x != 6 with bounds excluding x=3 — SAT.
/// x in [0, 2] means 2*x in [0, 4], so 2*x != 6 is trivially satisfied.
#[test]
#[timeout(10_000)]
fn test_lra_scaled_disequality_bounds_sat_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* 2.0 x) 6.0)))
(assert (>= x 0.0))
(assert (<= x 2.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "2*x != 6 with x in [0,2] is trivially SAT"
    );
}

/// 2*x != 6 with x in [2.5, 3.5] — SAT (x=2.5 or x=3.5 work).
/// The excluded point x=3 is in the interior, but other values exist.
#[test]
#[timeout(10_000)]
fn test_lra_scaled_disequality_tight_bounds_sat_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* 2.0 x) 6.0)))
(assert (>= x 2.5))
(assert (<= x 3.5))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "2*x != 6 with x in [2.5,3.5] SAT — x=3 excluded but other values exist"
    );
}

/// Negative coefficient: -3*x != -9 means x != 3.
#[test]
#[timeout(10_000)]
fn test_lra_negative_coeff_disequality_unsat_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* (- 3.0) x) (- 9.0))))
(assert (= x 3.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "-3*x != -9 with x=3 should be UNSAT"
    );
}

/// Fractional coefficient: (1/2)*x != 3 means x != 6.
#[test]
#[timeout(10_000)]
fn test_lra_fractional_coeff_disequality_sat_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* 0.5 x) 3.0)))
(assert (>= x 0.0))
(assert (<= x 5.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    // x in [0,5] and (1/2)*x != 3 means x != 6, but x <= 5, so always true
    assert_eq!(
        outputs,
        vec!["sat"],
        "(1/2)*x != 3 with x in [0,5] is trivially SAT"
    );
}

/// Fractional coefficient forced: (1/2)*x != 3 with x=6 is UNSAT.
#[test]
#[timeout(10_000)]
fn test_lra_fractional_coeff_forced_unsat_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* 0.5 x) 3.0)))
(assert (= x 6.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "(1/2)*x != 3 with x=6 is UNSAT since 0.5*6 = 3"
    );
}

/// LIA variant: 2*x != 6 means x != 3 (integers).
#[test]
#[timeout(10_000)]
fn test_lia_scaled_disequality_forced_unsat_6155() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (not (= (* 2 x) 6)))
(assert (= x 3))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "LIA: 2*x != 6 with x=3 should be UNSAT"
    );
}

/// LIA: 2*x != 6 with x in [1,5] — SAT (x=1,2,4,5 all work).
#[test]
#[timeout(10_000)]
fn test_lia_scaled_disequality_bounded_sat_6155() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (not (= (* 2 x) 6)))
(assert (>= x 1))
(assert (<= x 5))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "LIA: 2*x != 6 with x in [1,5] SAT — x=1,2,4,5 work"
    );
}

/// Regression test for #6155: triggers the actual DisequalitySplit code path.
///
/// With `2*x != 6` and `x >= 3, x <= 5`, simplex places x=3 (lower bound).
/// The disequality `2*3 - 6 = 0` is violated, and x is NOT pinned (lower=3, upper=5).
/// This reaches the single-variable DisequalitySplit at lib.rs:3363-3384.
///
/// Bug: excluded value is computed as -constant = 6, producing split `x < 6 OR x > 6`.
///      With x in [3, 5], `x < 6` is always true → solver loops.
/// Fix: excluded = -constant/coeff = 6/2 = 3, producing split `x < 3 OR x > 3`.
///      With x in [3, 5], `x > 3` → SAT at some x in (3, 5].
///
/// This test has a 3-second timeout because the bug causes an infinite loop.
#[test]
#[timeout(3_000)]
fn test_lra_coefficient_split_exercises_bug_path_6155() {
    let smt = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (* 2.0 x) 6.0)))
(assert (>= x 3.0))
(assert (<= x 5.0))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "#6155: 2*x != 6 with x in [3,5] must be SAT (x=3 excluded, but x>3 works)"
    );
}

// NOTE: The following tests are deferred until #6155 is fixed.
// AY currently times out on LIA with multiple scaled disequalities
// (e.g., 2*x != 6 AND 3*x != 12 with x in [3,4]).
// Z3 solves these instantly. The root cause is the coefficient bug
// in the DisequalitySplit path at lib.rs:3368 and lib.rs:3518.
//
// After #6155 is fixed, add these tests:
// - test_lia_multiple_scaled_disequalities_unsat_6155: x in {3,4}, x!=3 and x!=4 → UNSAT
// - test_lia_multiple_scaled_disequalities_sat_6155: x in {1..5}, x!=3 and x!=4 → SAT
