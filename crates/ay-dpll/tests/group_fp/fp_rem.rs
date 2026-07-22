// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Integration tests for fp.rem (IEEE 754 remainder).
//!
//! Tests that FP remainder correctly computes x - y*n where n = nearest
//! integer to x/y (ties to even).

use ntest::timeout;

// ========== fp.rem special cases ==========

/// rem(NaN, y) = NaN
#[test]
#[timeout(30_000)]
fn test_rem_nan_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.rem (_ NaN 5 11) (fp #b0 #b01111 #b0000000000)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(NaN, 1.0) should be NaN"
    );
}

/// rem(x, NaN) = NaN
#[test]
#[timeout(30_000)]
fn test_rem_nan_divisor() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.rem (fp #b0 #b01111 #b0000000000) (_ NaN 5 11)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(1.0, NaN) should be NaN"
    );
}

/// rem(+inf, y) = NaN
#[test]
#[timeout(30_000)]
fn test_rem_inf_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.rem (_ +oo 5 11) (fp #b0 #b01111 #b0000000000)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(+inf, 1.0) should be NaN"
    );
}

/// rem(x, 0) = NaN
#[test]
#[timeout(30_000)]
fn test_rem_zero_divisor() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.rem (fp #b0 #b01111 #b0000000000) (_ +zero 5 11)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(1.0, +0.0) should be NaN"
    );
}

/// rem(x, +inf) = x
#[test]
#[timeout(30_000)]
fn test_rem_inf_divisor() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b01111 #b0000000000) (_ +oo 5 11))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(1.0, +inf) should be 1.0"
    );
}

/// rem(+0, y) = +0 (verify sign with structural = not fp.eq)
#[test]
#[timeout(30_000)]
fn test_rem_zero_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.rem (_ +zero 5 11) (fp #b0 #b01111 #b0000000000))))
        (assert (fp.isZero z))
        (assert (not (= z (fp #b0 #b00000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(+0, 1.0) should be +0.0 (structural)"
    );
}

// ========== fp.rem concrete value tests ==========

/// rem(3.0, 2.0) = -1.0 (nearest integer quotient is 2, so 3 - 2*2 = -1)
/// Wait: IEEE 754: rem(3, 2) → n = round(3/2) = round(1.5) = 2 (ties to even)
/// rem = 3 - 2*2 = -1. But sign follows dividend? No, IEEE remainder can be negative.
/// Actually: rem(3.0, 2.0) = 3.0 - 2.0*2 = -1.0
/// Float16: 3.0 = (fp #b0 #b10000 #b1000000000), 2.0 = (fp #b0 #b10000 #b0000000000)
/// -1.0 = (fp #b1 #b01111 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_three_mod_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b10000 #b1000000000) (fp #b0 #b10000 #b0000000000))
            (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(3.0, 2.0) should be -1.0"
    );
}

/// rem(1.0, 2.0) = 1.0 (nearest integer quotient is 0, so 1 - 2*0 = 1)
/// Actually: round(1/2) = round(0.5) = 0 (ties to even), rem = 1 - 2*0 = 1.0
#[test]
#[timeout(60_000)]
fn test_rem_one_mod_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b01111 #b0000000000) (fp #b0 #b10000 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(1.0, 2.0) should be 1.0"
    );
}

/// rem(5.0, 3.0) = -1.0 (round(5/3) = round(1.667) = 2, rem = 5 - 3*2 = -1)
/// Float16: 5.0 = (fp #b0 #b10001 #b0100000000), 3.0 = (fp #b0 #b10000 #b1000000000)
/// -1.0 = (fp #b1 #b01111 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_five_mod_three() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b10001 #b0100000000) (fp #b0 #b10000 #b1000000000))
            (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(5.0, 3.0) should be -1.0"
    );
}

/// rem(4.0, 2.0) = +0.0 (verify sign with structural = not fp.eq)
/// Float16: 4.0 = (fp #b0 #b10001 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_four_mod_two() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.rem (fp #b0 #b10001 #b0000000000) (fp #b0 #b10000 #b0000000000))))
        (assert (fp.isZero z))
        (assert (not (= z (fp #b0 #b00000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(4.0, 2.0) should be +0.0 (structural)"
    );
}

// ========== fp.rem negative operand tests ==========

/// rem(-3.0, 2.0) = 1.0
/// n = round(-3/2) = round(-1.5) = -2 (ties to even), rem = -3 - 2*(-2) = 1.0
/// Float16: -3.0 = (fp #b1 #b10000 #b1000000000), 1.0 = (fp #b0 #b01111 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_neg_three_mod_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b1 #b10000 #b1000000000) (fp #b0 #b10000 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(-3.0, 2.0) should be 1.0"
    );
}

/// rem(3.0, -2.0) = -1.0
/// n = round(3/-2) = round(-1.5) = -2, rem = 3 - (-2)*(-2) = 3 - 4 = -1.0
/// Float16: -2.0 = (fp #b1 #b10000 #b0000000000), -1.0 = (fp #b1 #b01111 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_three_mod_neg_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b10000 #b1000000000) (fp #b1 #b10000 #b0000000000))
            (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(3.0, -2.0) should be -1.0"
    );
}

/// rem(-3.0, -2.0) = 1.0
/// n = round(-3/-2) = round(1.5) = 2 (ties to even), rem = -3 - (-2)*2 = -3 + 4 = 1.0
#[test]
#[timeout(60_000)]
fn test_rem_neg_three_mod_neg_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b1 #b10000 #b1000000000) (fp #b1 #b10000 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(-3.0, -2.0) should be 1.0"
    );
}

/// rem(-4.0, 2.0) = -0.0 (sign of zero matches dividend sign per IEEE 754)
/// n = round(-4/2) = -2 exactly, rem = -4 - 2*(-2) = 0
/// Zero result should have sign of dividend (-4.0 is negative → -0.0)
/// Float16: -4.0 = (fp #b1 #b10001 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_neg_four_mod_two_sign_of_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.rem (fp #b1 #b10001 #b0000000000) (fp #b0 #b10000 #b0000000000))))
        (assert (fp.isZero z))
        (assert (not (= z (fp #b1 #b00000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(-4.0, 2.0) should be -0.0 (sign of dividend)"
    );
}

/// rem(-0.0, 1.0) = -0.0 (sign of zero dividend preserved)
#[test]
#[timeout(60_000)]
fn test_rem_neg_zero_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.rem (_ -zero 5 11) (fp #b0 #b01111 #b0000000000))))
        (assert (fp.isZero z))
        (assert (not (= z (fp #b1 #b00000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(-0.0, 1.0) should be -0.0"
    );
}

/// rem(x, -inf) = x (IEEE 754: when divisor is infinite, result is dividend)
/// Test with negative infinity divisor.
#[test]
#[timeout(30_000)]
fn test_rem_neg_inf_divisor() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b01111 #b0000000000) (_ -oo 5 11))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(1.0, -inf) should be 1.0"
    );
}

/// rem(-inf, y) = NaN (negative infinity dividend)
#[test]
#[timeout(30_000)]
fn test_rem_neg_inf_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.rem (_ -oo 5 11) (fp #b0 #b01111 #b0000000000)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(-inf, 1.0) should be NaN"
    );
}

// ========== fp.rem ties-to-even discrimination ==========

/// rem(5.0, 2.0) = 1.0 (NOT -1.0)
/// 5.0 / 2.0 = 2.5, round(2.5) = 2 (ties to EVEN), rem = 5 - 2*2 = 1.0
/// If round-half-up were used: round(2.5) = 3, rem = 5 - 2*3 = -1.0 (WRONG)
/// This test discriminates ties-to-even from round-half-up.
/// Float16: 5.0 = (fp #b0 #b10001 #b0100000000), 1.0 = (fp #b0 #b01111 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_rem_ties_to_even_five_mod_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b10001 #b0100000000) (fp #b0 #b10000 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(5.0, 2.0) should be 1.0 (ties to even)"
    );
}

// ========== fp.rem subnormal tests ==========

/// rem with subnormal dividend: smallest positive subnormal rem(2^-24, 1.0) = 2^-24
/// Float16 smallest subnormal: (fp #b0 #b00000 #b0000000001) = 2^(-14) * 2^(-10) = 2^(-24)
/// n = round(2^-24 / 1.0) = round(2^-24) = 0, rem = 2^-24 - 1.0 * 0 = 2^-24
#[test]
#[timeout(60_000)]
fn test_rem_subnormal_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem (fp #b0 #b00000 #b0000000001) (fp #b0 #b01111 #b0000000000))
            (fp #b0 #b00000 #b0000000001))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(subnormal, 1.0) should be subnormal"
    );
}

// ========== fp.rem Float32 tests (regression for #5950) ==========

/// Float32 concrete fp.rem: verify barrel shifter handles 280-bit extended precision
/// without overflow. With Float32 (eb=8, sb=24), the barrel shifter operates on
/// 280-bit vectors where shift amount bits i >= 64 previously caused `1 << i`
/// overflow (#5950). Fixed by #5869 (checked_shl with OR-reduce overflow).
///
/// Uses concrete Float32 values to exercise the encoding without the combinatorial
/// explosion of fully-symbolic Float32 fp.rem (which generates ~280-bit barrel
/// shifter clauses and times out).
///
/// rem(3.0f32, 2.0f32) = -1.0f32
/// Float32: 3.0 = 0 10000000 10000000000000000000000
///          2.0 = 0 10000000 00000000000000000000000
///         -1.0 = 1 01111111 00000000000000000000000
#[test]
#[timeout(120_000)]
fn test_rem_float32_concrete() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.rem
                (fp #b0 #b10000000 #b10000000000000000000000)
                (fp #b0 #b10000000 #b00000000000000000000000))
            (fp #b1 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "rem(3.0f32, 2.0f32) should be -1.0f32"
    );
}
