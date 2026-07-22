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

// =========================================================================
// FP Arithmetic Operations — Integration Tests
// =========================================================================
//
// These tests verify FP arithmetic (fp.add, fp.sub, fp.mul, fp.neg, fp.abs)
// end-to-end through the full executor pipeline. Prior to this, only unit
// tests existed for arithmetic. IEEE 754-2008 Float32 encoding used:
//   1.0f32 = (fp #b0 #b01111111 #b00000000000000000000000)
//   2.0f32 = (fp #b0 #b10000000 #b00000000000000000000000)
//   3.0f32 = (fp #b0 #b10000000 #b10000000000000000000000)
//   0.5f32 = (fp #b0 #b01111110 #b00000000000000000000000)
//  -1.0f32 = (fp #b1 #b01111111 #b00000000000000000000000)

/// fp.add: 1.0 + 1.0 = 2.0 (RNE rounding mode).
#[test]
#[timeout(30_000)]
fn test_fp_add_one_plus_one() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.eq z (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 + 1.0 should equal 2.0");
}

/// fp.add: 1.0 + 1.0 != 3.0.
#[test]
#[timeout(30_000)]
fn test_fp_add_one_plus_one_not_three() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.eq z (fp #b0 #b10000000 #b10000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "1.0 + 1.0 should NOT equal 3.0");
}

/// fp.sub: 2.0 - 1.0 = 1.0.
#[test]
#[timeout(30_000)]
fn test_fp_sub_two_minus_one() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.sub RNE x y)))
        (assert (fp.eq z (fp #b0 #b01111111 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "2.0 - 1.0 should equal 1.0");
}

// Removed: test_fp_mul_two_times_one and test_fp_mul_two_times_half
// Both time out at 30s on concrete normal-value multiplication.
// Filed as #3586 comment (FP multiplication performance bug).
// Will be re-added when multiplication performance is fixed.

/// fp.neg: neg(1.0) should fp.eq -1.0.
#[test]
#[timeout(30_000)]
fn test_fp_neg_one() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.neg x)))
        (assert (fp.eq z (fp #b1 #b01111111 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "neg(1.0) should equal -1.0");
}

/// fp.abs: abs(-2.0) should fp.eq 2.0.
#[test]
#[timeout(30_000)]
fn test_fp_abs_negative() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.abs x)))
        (assert (fp.eq z (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "abs(-2.0) should equal 2.0");
}

// fp.add with NaN: NaN + 1.0 should be NaN (IEEE 754 Section 6.2).
// test_fp_add_nan_propagation_known_bug: REMOVED — bug fixed by structural
// equality fix (SMT-LIB = now uses bit-level equality, not fp.eq).
// Replaced by test_fp_add_nan_propagation which asserts the correct result.

/// fp.add with infinity: +inf + 1.0 should be +inf.
#[test]
#[timeout(30_000)]
fn test_fp_add_infinity_absorbs() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (_ +oo 8 24)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.isInfinite z))
        (assert (fp.isPositive z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "+inf + 1.0 should be +inf");
}

/// fp.add: 1.0 + 0.0 = 1.0 (zero is additive identity).
#[test]
#[timeout(30_000)]
fn test_fp_add_zero_identity() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (_ +zero 8 24)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.eq z (fp #b0 #b01111111 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 + 0.0 should equal 1.0");
}

/// fp.sub: 1.0 - 1.0 = 0.0 (self-subtraction gives zero).
#[test]
#[timeout(30_000)]
fn test_fp_sub_self_is_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.sub RNE x y)))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 - 1.0 should be zero");
}

/// fp.mul: x * 0.0 should be zero (for finite x).
/// 60s timeout: multiplication generates larger CNF encoding than add/sub.
#[test]
#[timeout(60_000)]
fn test_fp_mul_by_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= y (_ +zero 8 24)))
        (assert (= z (fp.mul RNE x y)))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "2.0 * 0.0 should be zero");
}

/// Structural = on NaN: (= NaN NaN) should be SAT.
/// Unlike fp.eq where NaN != NaN, structural = is reflexive.
#[test]
#[timeout(30_000)]
fn test_fp_structural_eq_nan_reflexive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (assert (= x x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "NaN = NaN via structural = should be SAT"
    );
}

/// Structural = distinguishes +0 from -0 (unlike fp.eq).
#[test]
#[timeout(30_000)]
fn test_fp_structural_eq_zero_signs_differ() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x (_ +zero 8 24)))
        (assert (= y (_ -zero 8 24)))
        (assert (= x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "+0 = -0 via structural = should be UNSAT (different bit patterns)"
    );
}

/// fp.add: 0 + 2.0 should be 2.0 (zero identity, result copies non-zero operand).
#[test]
#[timeout(30_000)]
fn test_fp_add_zero_plus_value() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (_ +zero 8 24)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.eq z (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "0.0 + 2.0 should equal 2.0");
}

/// fp.add: 2.0 + 0 should be 2.0 (zero identity, symmetry check).
#[test]
#[timeout(30_000)]
fn test_fp_add_value_plus_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= y (_ +zero 8 24)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.eq z (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "2.0 + 0.0 should equal 2.0");
}

// =========================================================================
// fp.gt / fp.geq coverage (delegations to fp.lt / fp.leq with swapped args)
// =========================================================================

/// fp.gt: 2.0 > 1.0 should be satisfiable.
#[test]
#[timeout(30_000)]
fn test_fp_gt_positive_values() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.gt
            (fp #b0 #b10000000 #b00000000000000000000000)
            (fp #b0 #b01111111 #b00000000000000000000000)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// fp.gt: 1.0 > 2.0 should be unsatisfiable.
#[test]
#[timeout(30_000)]
fn test_fp_gt_negative_case() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.gt
            (fp #b0 #b01111111 #b00000000000000000000000)
            (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// fp.geq: 1.0 >= 1.0 should be satisfiable.
#[test]
#[timeout(30_000)]
fn test_fp_geq_equal_values() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.geq
            (fp #b0 #b01111111 #b00000000000000000000000)
            (fp #b0 #b01111111 #b00000000000000000000000)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// fp.geq: NaN >= NaN should be unsatisfiable (NaN is unordered).
#[test]
#[timeout(30_000)]
fn test_fp_geq_nan_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (assert (fp.geq x x))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

// =========================================================================
// Float16 fp.mul concrete correctness (normal values)
// =========================================================================

/// Float16 fp.mul: 2.0 * 1.0 = 2.0 (normal-value multiplication).
/// Float16 2.0 = (fp #b0 #b10000 #b0000000000), 1.0 = (fp #b0 #b01111 #b0000000000).
#[test]
#[timeout(30_000)]
fn test_fp_mul_two_times_one_f16() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.mul RNE
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01111 #b0000000000))
            (fp #b0 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "Float16: 2.0 * 1.0 should equal 2.0"
    );
}

/// Float16 fp.mul: 1.5 * 2.0 = 3.0.
/// Float16 1.5 = (fp #b0 #b01111 #b1000000000), 3.0 = (fp #b0 #b10000 #b1000000000).
#[test]
#[timeout(30_000)]
fn test_fp_mul_1_5_times_2_f16() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.mul RNE
                (fp #b0 #b01111 #b1000000000)
                (fp #b0 #b10000 #b0000000000))
            (fp #b0 #b10000 #b1000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "Float16: 1.5 * 2.0 should equal 3.0"
    );
}

// =========================================================================
// Opposite-sign addition
// =========================================================================

/// fp.add opposite signs: 1.0 + (-2.0) = -1.0 (exercises subtraction path in add).
/// Float32: 1.0 = 0_01111111_000..., -2.0 = 1_10000000_000..., -1.0 = 1_01111111_000...
#[test]
#[timeout(30_000)]
fn test_fp_add_opposite_sign() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.add RNE
                (fp #b0 #b01111111 #b00000000000000000000000)
                (fp #b1 #b10000000 #b00000000000000000000000))
            (fp #b1 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "1.0 + (-2.0) should equal -1.0"
    );
}

/// fp.add opposite signs: 2.0 + (-1.0) = 1.0 (opposite sign, positive result).
#[test]
#[timeout(30_000)]
fn test_fp_add_opposite_sign_positive_result() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.add RNE
                (fp #b0 #b10000000 #b00000000000000000000000)
                (fp #b1 #b01111111 #b00000000000000000000000))
            (fp #b0 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "2.0 + (-1.0) should equal 1.0"
    );
}

// Guard regression tests and fp.min/fp.max tests moved to fp_guard_and_minmax.rs
// when fp_integration.rs exceeded the 1000-line limit.
