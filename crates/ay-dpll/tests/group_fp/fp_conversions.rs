// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! FP conversion operation tests: to_fp, to_fp_unsigned (#3586, #5883).
//!
//! Tests for the newly implemented FP conversion bit-blasting:
//! - to_fp from BV (1-arg reinterpretation)
//! - to_fp from signed BV (2-arg, rm + BV)
//! - to_fp_unsigned from BV (2-arg, rm + BV)
//! - to_fp from FP (2-arg, rm + FP) — precision conversion

use ntest::timeout;

// =========================================================================
// to_fp BV reinterpretation (1-arg variant)
// =========================================================================

/// to_fp from BV: Float32 1.0 = 0x3F800000
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) #b00111111100000000000000000000000)
            (fp #b0 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: Float32 2.0 = 0x40000000
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) #b01000000000000000000000000000000)
            (fp #b0 #b10000000 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: Float32 -1.0 = 0xBF800000
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_neg_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) #b10111111100000000000000000000000)
            (fp #b1 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: Float32 +0 = all zeros
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_pos_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) #b00000000000000000000000000000000)
            (_ +zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: Float32 -0 = 0x80000000
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_neg_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) #b10000000000000000000000000000000)
            (_ -zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: quiet NaN (exponent all 1s, sig MSB set)
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            ((_ to_fp 8 24) #b01111111110000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: +infinity
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_pos_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            ((_ to_fp 8 24) #b01111111100000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: -infinity
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_neg_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            ((_ to_fp 8 24) #b11111111100000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp from BV: 0.5f = 0x3F000000 (sign=0, exp=126, sig=0)
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_half() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) #b00111111000000000000000000000000)
            (fp #b0 #b01111110 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp BV reinterpret: smallest Float32 subnormal (exp=0, sig=1).
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_smallest_subnormal() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isSubnormal
            ((_ to_fp 8 24) #b00000000000000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp BV reinterpret: largest Float32 subnormal (exp=0, sig all 1s).
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_largest_subnormal() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isSubnormal
            ((_ to_fp 8 24) #b00000000011111111111111111111111))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp BV reinterpret: negative subnormal.
#[test]
#[timeout(30_000)]
fn test_to_fp_bv_reinterpret_neg_subnormal() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNegative
            ((_ to_fp 8 24) #b10000000000000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

// =========================================================================
// to_fp from signed BV (2-arg: rm + signed BV)
// =========================================================================

/// to_fp signed: 0 → +0.0
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000000000000000000000000000000)
            (_ +zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: 1 → 1.0f
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000000000000000000000000000001)
            (fp #b0 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: -1 (2's complement all 1s) → -1.0f
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_neg_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b11111111111111111111111111111111)
            (fp #b1 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: 2 → 2.0f
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000000000000000000000000000010)
            (fp #b0 #b10000000 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: 42 → 42.0f
/// Float32 42.0 = 0_10000100_01010000000000000000000
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_42() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000000000000000000000000101010)
            (fp #b0 #b10000100 #b01010000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: -42 → -42.0f
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_neg_42() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b11111111111111111111111111010110)
            (fp #b1 #b10000100 #b01010000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: 8-bit signed int. 5 → 5.0f
/// Float32 5.0 = 0_10000001_01000000000000000000000
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_small_bv() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000101)
            (fp #b0 #b10000001 #b01000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: INT8_MIN = -128 → -128.0f.
/// Float32 -128.0 = 1_10000110_00000000000000000000000.
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_int8_min() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b10000000)
            (fp #b1 #b10000110 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: INT8_MAX = 127 → 127.0f.
/// Float32 127.0 = 0_10000101_11111100000000000000000.
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_int8_max() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b01111111)
            (fp #b0 #b10000101 #b11111100000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: INT32_MIN (-2_147_483_648 = 0x80000000) → -2147483648.0f.
/// Float32: sign=1, exp=158, sig=0. (2^31, biased exp = 31+127 = 158.)
/// This is the #5883 bug: wide path off-by-one lost the leading 1.
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_int32_min() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b10000000000000000000000000000000)
            (fp #b1 #b10011110 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: 2^24 + 1 = 16777217 requires rounding in Float32.
/// In RNE, this rounds to 16777216.0 (ties to even → round down).
/// Float32 16777216.0 = 0_10010111_00000000000000000000000.
#[test]
#[timeout(60_000)]
fn test_to_fp_signed_rne_rounding_tie() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000001000000000000000000000001)
            (fp #b0 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: 2^24 + 3 = 16777219 requires rounding in Float32.
/// RNE ties to even: 16777220.
/// Float32 16777220.0 = 0_10010111_00000000000000000000010.
#[test]
#[timeout(60_000)]
fn test_to_fp_signed_rne_rounding_tie_up() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b00000001000000000000000000000011)
            (fp #b0 #b10010111 #b00000000000000000000010))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

include!("fp_conversions/unsigned_and_cross_format.rs");
