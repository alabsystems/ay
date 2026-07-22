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

// =========================================================================
// to_fp_unsigned (2-arg: rm + unsigned BV)
// =========================================================================

/// to_fp_unsigned: 0 → +0.0
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b00000000000000000000000000000000)
            (_ +zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 1 → 1.0f
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b00000000000000000000000000000001)
            (fp #b0 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 255 (8-bit) → 255.0f
/// Float32 255.0 = 0_10000110_11111110000000000000000
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_255() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b11111111)
            (fp #b0 #b10000110 #b11111110000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 256 → 256.0f
/// Float32 256.0 = 0_10000111_00000000000000000000000
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_256() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b0000000100000000)
            (fp #b0 #b10000111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 2^24 = 16777216 is exactly representable in Float32.
#[test]
#[timeout(60_000)]
fn test_to_fp_unsigned_2_pow_24() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b00000001000000000000000000000000)
            (fp #b0 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 2^24 + 2 = 16777218 is exactly representable.
/// Float32: 0_10010111_00000000000000000000001.
#[test]
#[timeout(60_000)]
fn test_to_fp_unsigned_2_pow_24_plus_2() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b00000001000000000000000000000010)
            (fp #b0 #b10010111 #b00000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 16777217 (2^24 + 1) with RNE ties to even → 16777216.0.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_rounding_tie_rne_even() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b00000001000000000000000000000001)
            (fp #b0 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 16777219 (2^24 + 3) with RNE ties to even → 16777220.0.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_rounding_tie_rne_odd() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNE #b00000001000000000000000000000011)
            (fp #b0 #b10010111 #b00000000000000000000010))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 16777217 with RNA → rounds UP to 16777218.0.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_rounding_tie_rna() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RNA #b00000001000000000000000000000001)
            (fp #b0 #b10010111 #b00000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 16777217 with RTP → rounds UP = 16777218.0.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_rounding_tie_rtp() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RTP #b00000001000000000000000000000001)
            (fp #b0 #b10010111 #b00000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 16777217 with RTZ → truncates to 16777216.0.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_rounding_tie_rtz() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RTZ #b00000001000000000000000000000001)
            (fp #b0 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 16777217 with RTN → truncates for positive = 16777216.0.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_rounding_tie_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 8 24) RTN #b00000001000000000000000000000001)
            (fp #b0 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

// =========================================================================
// Edge case: signed rounding with negative values (non-RNE modes)
// =========================================================================

/// to_fp signed: -16777217 with RNE → -16777216.0 (ties to even).
/// -16777217 as 32-bit = 0xFEFFFFFF.
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_neg_rounding_rne() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE #b11111110111111111111111111111111)
            (fp #b1 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: -16777217 with RTN → -16777218.0 (round away from zero).
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_neg_rounding_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RTN #b11111110111111111111111111111111)
            (fp #b1 #b10010111 #b00000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp signed: -16777217 with RTP → -16777216.0 (truncate magnitude).
#[test]
#[timeout(30_000)]
fn test_to_fp_signed_neg_rounding_rtp() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RTP #b11111110111111111111111111111111)
            (fp #b1 #b10010111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

// =========================================================================
// Edge case: overflow to infinity (#5883)
// =========================================================================

/// to_fp_unsigned: 65536 to Float16 with RNE → +infinity (exceeds max finite 65504).
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_overflow_to_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            ((_ to_fp_unsigned 5 11) RNE #b00000000000000010000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned: 65536 to Float16 with RTZ → max finite (clamp, not infinity).
/// Float16 max finite = sign=0, exp=30, sig=1023.
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_overflow_rtz_max_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp_unsigned 5 11) RTZ #b00000000000000010000000000000000)
            (fp #b0 #b11110 #b1111111111))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

// =========================================================================
// Guard tests: unsupported conversions still return Unknown
// =========================================================================

/// to_fp from a constant Real is now folded to the correctly-rounded IEEE bit
/// pattern (the standard FP-literal syntax). `x = ((_ to_fp 8 24) RNE 1.0)` is
/// satisfiable with x = 1.0f.
#[test]
#[timeout(30_000)]
fn test_to_fp_real_constant_folded_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= x ((_ to_fp 8 24) RNE 1.0)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// The folded constant has the right VALUE: `to_fp(RNE, 1.0)` and
/// `to_fp(RNE, 2.0)` are distinct FP numbers, so equating them is UNSAT.
#[test]
#[timeout(30_000)]
fn test_to_fp_real_constant_distinct_values_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.eq ((_ to_fp 8 24) RNE 1.0) ((_ to_fp 8 24) RNE 2.0)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// Rounding mode matters: 1/3 is not representable, so RTN (toward -inf) gives a
/// strictly smaller value than RTP (toward +inf) — equating them is UNSAT.
#[test]
#[timeout(30_000)]
fn test_to_fp_real_rounding_modes_differ_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.eq ((_ to_fp 8 24) RTN (/ 1.0 3.0))
                       ((_ to_fp 8 24) RTP (/ 1.0 3.0))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// to_fp_unsigned with BV variable: BV = 1, to_fp_unsigned → 1.0f, isNaN(1.0f) = false → UNSAT.
/// Variable BV to_fp_unsigned is now fully supported via symbolic bit-level circuit (#3586).
#[test]
#[timeout(30_000)]
fn test_to_fp_unsigned_variable_bv_not_nan() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const bv (_ BitVec 32))
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= bv #x00000001))
        (assert (= x ((_ to_fp_unsigned 8 24) RNE bv)))
        (assert (fp.isNaN x))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// fp.rem now supported: basic satisfiability check.
#[test]
#[timeout(60_000)]
fn test_fp_rem_supported() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (assert (not (fp.isNaN x)))
        (assert (not (fp.isNaN y)))
        (assert (not (fp.isZero y)))
        (assert (not (fp.isInfinite x)))
        (assert (fp.eq (fp.rem x y) x))
        (check-sat)
    "#;
    // Should be SAT: e.g. x=1.0, y=2.0 => rem(1.0, 2.0) = 1.0
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

// =========================================================================
// FP-to-FP precision conversion (#5883)
// =========================================================================

/// FP-to-FP: Float16 1.0 → Float32 1.0 (widening, exact).
#[test]
#[timeout(30_000)]
fn test_to_fp_float_widen_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE (fp #b0 #b01111 #b0000000000))
            (fp #b0 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float16 -2.0 → Float32 -2.0 (widening, exact, preserves sign).
#[test]
#[timeout(30_000)]
fn test_to_fp_float_widen_neg_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE (fp #b1 #b10000 #b0000000000))
            (fp #b1 #b10000000 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float16 +0 → Float32 +0 (zero preserves sign).
#[test]
#[timeout(30_000)]
fn test_to_fp_float_widen_pos_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE (_ +zero 5 11))
            (_ +zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float16 -0 → Float32 -0 (negative zero preserved).
#[test]
#[timeout(30_000)]
fn test_to_fp_float_widen_neg_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE (_ -zero 5 11))
            (_ -zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float16 NaN → Float32 NaN.
#[test]
#[timeout(30_000)]
fn test_to_fp_float_widen_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            ((_ to_fp 8 24) RNE (_ NaN 5 11)))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float16 +inf → Float32 +inf.
#[test]
#[timeout(30_000)]
fn test_to_fp_float_widen_pos_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            ((_ to_fp 8 24) RNE (_ +oo 5 11)))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float64 1.0 → Float32 1.0 (narrowing, exact).
#[test]
#[timeout(30_000)]
fn test_to_fp_float64_to_float32_one() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 8 24) RNE
                (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))
            (fp #b0 #b01111111 #b00000000000000000000000))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float32 NaN → Float16 NaN.
#[test]
#[timeout(30_000)]
fn test_to_fp_float32_nan_to_float16() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            ((_ to_fp 5 11) RNE
                (fp #b0 #b11111111 #b10000000000000000000000)))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float32 +inf → Float16 +inf.
#[test]
#[timeout(30_000)]
fn test_to_fp_float32_inf_to_float16() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            ((_ to_fp 5 11) RNE
                (fp #b0 #b11111111 #b00000000000000000000000)))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}

/// FP-to-FP: Float32 -0 → Float16 -0 (zero sign preservation).
#[test]
#[timeout(30_000)]
fn test_to_fp_float32_neg_zero_to_float16() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            ((_ to_fp 5 11) RNE
                (fp #b1 #b00000000 #b00000000000000000000000))
            (_ -zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["unsat"]);
}
