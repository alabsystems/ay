// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! FP model extraction edge case tests (proof_coverage phase).
//!
//! Covers get-value paths for FP special values that were identified
//! as untested: negative zero, infinity, subnormal, and negative finite.
//! Also tests multi-ITE over FP, and mixed FP arithmetic model extraction.

use ntest::timeout;

/// Model extraction: get-value returns -zero for a negative zero variable.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_negative_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isZero x))
        (assert (fp.isNegative x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    assert!(
        model_str.contains("-zero"),
        "Expected -zero in model, got: {model_str}"
    );
}

/// Model extraction: get-value returns +oo for positive infinity.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_positive_infinity() {
    let smt = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isInfinite x))
        (assert (fp.isPositive x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    // +oo is typically represented as (fp #b0 #b11111111 #b00000000000000000000000)
    // or +oo / +infinity
    assert!(
        model_str.contains("+oo")
            || model_str.contains("fp #b0 #b11111111 #b0000000000000000000000"),
        "Expected +oo or infinity bit pattern in model, got: {model_str}"
    );
}

/// Model extraction: get-value returns -oo for negative infinity.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_negative_infinity() {
    let smt = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isInfinite x))
        (assert (fp.isNegative x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    assert!(
        model_str.contains("-oo")
            || model_str.contains("fp #b1 #b11111111 #b0000000000000000000000"),
        "Expected -oo or infinity bit pattern in model, got: {model_str}"
    );
}

/// Model extraction: get-value returns a valid (fp ...) triple for a negative finite value.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_negative_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isNormal x))
        (assert (fp.isNegative x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    // Should be (fp #b1 ...) — sign bit is 1 for negative
    assert!(
        model_str.contains("(fp #b1"),
        "Expected negative (fp #b1 ...) in model, got: {model_str}"
    );
}

/// Model extraction: get-value returns a subnormal value.
/// Subnormals have exponent field all zeros but significand non-zero.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_subnormal() {
    let smt = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.isSubnormal x))
        (assert (fp.isPositive x))
        (check-sat)
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    let model_str = &outputs[1];
    // Subnormal: sign=0, exponent=00000000, significand != 0
    assert!(
        model_str.contains("(fp #b0 #b00000000"),
        "Expected subnormal (fp #b0 #b00000000 ...) in model, got: {model_str}"
    );
    // Significand must not be all zeros (that would be zero, not subnormal)
    assert!(
        !model_str.contains("#b00000000000000000000000)"),
        "Subnormal significand should be non-zero, got: {model_str}"
    );
}

/// FP ITE with multiple ITE terms in one formula.
/// Tests that the ITE decomposition handles >1 FP-sorted ITE correctly.
#[test]
#[timeout(30_000)]
fn test_fp_ite_multiple_in_formula() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (declare-const c (_ FloatingPoint 8 24))
        (assert (fp.eq a (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (fp.eq b (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.eq c (fp #b0 #b10000001 #b00000000000000000000000)))
        ; Two distinct ITE-over-FP terms
        (assert (fp.eq
            (ite (fp.lt a b) a b)
            a))
        (assert (fp.eq
            (ite (fp.lt b c) b c)
            b))
        (check-sat)
    "#;
    // a=1.0, b=2.0, c=4.0
    // ite(1.0 < 2.0, 1.0, 2.0) = 1.0 = a -- SAT
    // ite(2.0 < 4.0, 2.0, 4.0) = 2.0 = b -- SAT
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// FP ITE soundness: false branch should be selected when condition is false.
#[test]
#[timeout(30_000)]
fn test_fp_ite_false_condition_selects_false_branch() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (assert (fp.eq a (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.eq b (fp #b0 #b01111111 #b00000000000000000000000)))
        ; a=2.0, b=1.0, so (fp.lt a b) is false
        ; ite(false, a, b) = b = 1.0
        ; Asserting the result equals a (2.0) should be UNSAT
        (assert (fp.eq (ite (fp.lt a b) a b) a))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// FP model extraction: get-value on arithmetic result.
/// Tests that the model evaluator can compute fp.add results.
#[test]
#[timeout(30_000)]
fn test_fp_model_extraction_arithmetic_result() {
    let smt = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
        (check-sat)
        (get-value ((fp.add RNE x x)))
    "#;
    // x = 1.0, so fp.add RNE x x = 2.0
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    // get-value should return 2.0 = (fp #b0 #b10000000 #b00000000000000000000000)
    let model_str = &outputs[1];
    assert!(
        model_str.contains("(fp #b"),
        "Expected (fp ...) triple in get-value result, got: {model_str}"
    );
}
