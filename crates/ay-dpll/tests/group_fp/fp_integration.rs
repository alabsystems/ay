// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end integration tests for QF_FP (IEEE 754 floating-point).
//!
//! Verifies that FP formulas route through the FP bit-blasting pipeline
//! and produce correct SAT/UNSAT results (#4127).

use ntest::timeout;

/// FP classification: x cannot be both NaN and Infinite.
#[test]
#[timeout(30_000)]
fn test_fp_nan_and_infinite_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (assert (fp.isInfinite x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "NaN AND Infinite should be UNSAT");
}

/// FP classification: NaN is satisfiable.
#[test]
#[timeout(30_000)]
fn test_fp_is_nan_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "isNaN should be SAT");
}

/// FP comparison: x <= y is satisfiable.
#[test]
#[timeout(30_000)]
fn test_fp_le_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (fp.leq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "x <= y should be SAT");
}

/// FP classification: x cannot be simultaneously zero and normal.
#[test]
#[timeout(30_000)]
fn test_fp_zero_and_normal_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isZero x))
        (assert (fp.isNormal x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "zero AND normal should be UNSAT");
}

/// FP model extraction: get-value returns a valid FP literal for a NaN variable.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    // The model value should be a NaN representation
    let model_str = &outputs[1];
    assert!(
        model_str.contains("NaN"),
        "Expected NaN in model, got: {model_str}"
    );
}

/// FP model extraction: get-value returns +zero for a zero variable.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isZero x))
        (assert (fp.isPositive x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    assert!(
        model_str.contains("+zero"),
        "Expected +zero in model, got: {model_str}"
    );
}

/// FP model extraction: get-value returns a valid (fp ...) triple for a finite value.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNormal x))
        (assert (fp.isPositive x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    // Should be a (fp #b... #b... #b...) triple, not a placeholder +zero
    assert!(
        model_str.contains("(fp #b"),
        "Expected (fp ...) triple in model, got: {model_str}"
    );
}

/// QF_FP logic detection: verify FP formulas no longer fall back to QF_UF.
#[test]
#[timeout(30_000)]
fn test_fp_logic_detection() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (assert (fp.isPositive x))
        (assert (fp.isNegative x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // Under QF_UF fallback, both predicates are uninterpreted → SAT (wrong).
    // Under QF_FP, positive AND negative is UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "positive AND negative should be UNSAT (not QF_UF fallback)"
    );
}

// ── Concrete FP value tests: semantic correctness (#3586) ────────────
// IEEE 754 Float32 bit patterns:
//   1.0  = (fp #b0 #b01111111 #b00000000000000000000000)
//   -1.0 = (fp #b1 #b01111111 #b00000000000000000000000)
//   2.0  = (fp #b0 #b10000000 #b00000000000000000000000)
//   -2.0 = (fp #b1 #b10000000 #b00000000000000000000000)

/// Concrete comparison: 1.0 < 2.0 should be satisfiable (it's true).
#[test]
#[timeout(30_000)]
fn test_fp_concrete_lt_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 < 2.0 should be SAT");
}

/// Concrete comparison: 2.0 < 1.0 should be UNSAT (it's false).
#[test]
#[timeout(30_000)]
fn test_fp_concrete_lt_positive_reversed() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "2.0 < 1.0 should be UNSAT");
}

/// Concrete comparison: -2.0 < -1.0 should be SAT.
/// Regression test for negative number comparison (e457cd1a4).
#[test]
#[timeout(30_000)]
fn test_fp_concrete_lt_negative() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b10000000 #b00000000000000000000000)))
        (assert (= y (fp #b1 #b01111111 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "-2.0 < -1.0 should be SAT");
}

/// Concrete comparison: -1.0 < -2.0 should be UNSAT.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_lt_negative_reversed() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b1 #b10000000 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "-1.0 < -2.0 should be UNSAT");
}

/// Cross-sign comparison: -1.0 < 1.0 should be SAT.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_lt_cross_sign() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "-1.0 < 1.0 should be SAT");
}

/// Concrete equality: 1.0 = 1.0 should be SAT.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_eq_same() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (fp.eq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 = 1.0 should be SAT");
}

/// Concrete inequality: 1.0 = 2.0 should be UNSAT.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_eq_different() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.eq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "1.0 = 2.0 should be UNSAT");
}

/// IEEE 754: +zero and -zero are fp.eq (but not structurally =).
#[test]
#[timeout(30_000)]
fn test_fp_concrete_zero_signs_equal() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (_ +zero 8 24)))
        (assert (= y (_ -zero 8 24)))
        (assert (fp.eq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "+zero fp.eq -zero should be SAT (IEEE 754)"
    );
}

/// NaN is not fp.eq to itself (IEEE 754).
#[test]
#[timeout(30_000)]
fn test_fp_nan_not_eq_self() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (assert (fp.eq x x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "NaN fp.eq NaN should be UNSAT (IEEE 754)"
    );
}

/// Concrete classification: +zero is zero and positive.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_classification_pzero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= x (_ +zero 8 24)))
        (assert (fp.isZero x))
        (assert (fp.isPositive x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "+zero should be zero and positive");
}

/// Concrete classification: +infinity is infinite.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_classification_infinity() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= x (_ +oo 8 24)))
        (assert (fp.isInfinite x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "+oo should be infinite");
}

/// Concrete comparison: +zero < 1.0 should be SAT.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_lt_zero_vs_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (_ +zero 8 24)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "0.0 < 1.0 should be SAT");
}

/// IEEE 754: -0 < +0 should be UNSAT (they are equal).
/// Regression test for both-zero guard in make_lt_result.
#[test]
#[timeout(30_000)]
fn test_fp_neg_zero_lt_pos_zero_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b00000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b00000000 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "-0 < +0 should be UNSAT (IEEE 754: -0 == +0)"
    );
}

/// IEEE 754: +0 < -0 should be UNSAT (they are equal).
#[test]
#[timeout(30_000)]
fn test_fp_pos_zero_lt_neg_zero_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b00000000 #b00000000000000000000000)))
        (assert (= y (fp #b1 #b00000000 #b00000000000000000000000)))
        (assert (fp.lt x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "+0 < -0 should be UNSAT (IEEE 754: +0 == -0)"
    );
}

/// IEEE 754: -0 <= +0 should be SAT (they are equal).
#[test]
#[timeout(30_000)]
fn test_fp_neg_zero_leq_pos_zero_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b00000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b00000000 #b00000000000000000000000)))
        (assert (fp.leq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "-0 <= +0 should be SAT (IEEE 754: -0 == +0)"
    );
}

/// IEEE 754: +0 <= -0 should be SAT (they are equal).
#[test]
#[timeout(30_000)]
fn test_fp_pos_zero_leq_neg_zero_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b00000000 #b00000000000000000000000)))
        (assert (= y (fp #b1 #b00000000 #b00000000000000000000000)))
        (assert (fp.leq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "+0 <= -0 should be SAT (IEEE 754: +0 == -0)"
    );
}

/// IEEE 754: fp.eq(-0, +0) should be SAT.
#[test]
#[timeout(30_000)]
fn test_fp_neg_zero_eq_pos_zero_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b00000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b00000000 #b00000000000000000000000)))
        (assert (fp.eq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "fp.eq(-0, +0) should be SAT (IEEE 754: -0 == +0)"
    );
}

/// Concrete leq: 1.0 <= 1.0 should be SAT.
#[test]
#[timeout(30_000)]
fn test_fp_concrete_leq_equal() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (fp.leq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 <= 1.0 should be SAT");
}

include!("fp_integration/arithmetic_and_comparisons.rs");
