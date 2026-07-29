// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Integration tests for fp.to_ieee_bv (FP-to-BV bit-pattern reinterpretation).
//!
//! Tests that FP values correctly convert to their IEEE 754 bitvector encoding
//! via pure reinterpretation (no rounding mode, no value conversion).

use ntest::timeout;

// ========== Float32 round-trip tests ==========

/// Float32 1.0 = 0x3f800000: fp literal → fp.to_ieee_bv → BV.
/// IEEE 754 Float32 1.0 = sign=0, exp=01111111, sig=00000000000000000000000.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float32_one() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b0 #b01111111 #b00000000000000000000000)) #x3f800000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(1.0f32) should be 0x3f800000"
    );
}

/// Float32 -1.0 = 0xbf800000
/// IEEE 754 Float32 -1.0 = sign=1, exp=01111111, sig=00000000000000000000000.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float32_neg_one() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b1 #b01111111 #b00000000000000000000000)) #xbf800000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(-1.0f32) should be 0xbf800000"
    );
}

/// Float32 +0.0 = 0x00000000
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float32_pos_zero() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b0 #b00000000 #b00000000000000000000000)) #x00000000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(+0.0) should be 0x00000000"
    );
}

/// Float32 -0.0 = 0x80000000
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float32_neg_zero() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b1 #b00000000 #b00000000000000000000000)) #x80000000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(-0.0) should be 0x80000000"
    );
}

/// Float32 +Inf = 0x7f800000
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float32_pos_inf() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b0 #b11111111 #b00000000000000000000000)) #x7f800000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(+Inf) should be 0x7f800000"
    );
}

/// Float32 -Inf = 0xff800000
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float32_neg_inf() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b1 #b11111111 #b00000000000000000000000)) #xff800000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(-Inf) should be 0xff800000"
    );
}

// ========== Float16 tests ==========

/// Float16 1.0 = (fp #b0 #b01111 #b0000000000) = 0x3c00
#[test]
#[timeout(30_000)]
fn test_ieee_bv_float16_one() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b0 #b01111 #b0000000000)) #x3c00)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(Float16 1.0) should be 0x3c00"
    );
}

// ========== NaN shape tests ==========
//
// A `(_ FloatingPoint eb sb)` sort has exactly ONE NaN element but IEEE 754
// has many NaN bit-patterns for it, so `fp.to_ieee_bv` leaves the returned
// pattern UNSPECIFIED on NaN. Unspecified is not non-functional: SMT-LIB 2.6
// §5.2 makes every function symbol denote a total function and `=` denote
// identity, so equal arguments must give equal results. These tests pin both
// halves of that — free choice of pattern, single-valued per argument — rather
// than any one encoding.

/// Every NaN-typed argument gets the SAME bitvector: `fp.to_ieee_bv` is a
/// function, and `(fp.neg NaN)` denotes the very same element as `NaN`
/// (its raw sign bit flips, but that is an encoding detail, not a value).
#[test]
#[timeout(30_000)]
fn test_ieee_bv_nan_is_functional_across_neg() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (_ NaN 8 24))
                        (fp.to_ieee_bv (fp.neg (_ NaN 8 24))))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv must be single-valued on the one NaN element"
    );
}

/// The same obligation with the NaN reached through a variable and through
/// two different spellings of the constant.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_nan_is_functional_across_spellings() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b11111111 #b00000000000000000000001)))
        (assert (not (= (fp.to_ieee_bv x) (fp.to_ieee_bv (_ NaN 8 24)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "all NaN encodings denote one element, so all give one fp.to_ieee_bv result"
    );
}

/// Which NaN pattern comes back is unspecified — a sign-set quiet NaN is an
/// admissible answer, so demanding it must NOT be refuted.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_nan_pattern_is_unspecified() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (= (fp.to_ieee_bv (_ NaN 8 24)) #xffc00000))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "no particular NaN encoding may be forced on fp.to_ieee_bv"
    );
}

/// Unspecified among NaN *encodings* only: the result still has to be one,
/// or reinterpreting it back could not recover NaN.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_nan_result_is_a_nan_encoding() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (= (fp.to_ieee_bv (_ NaN 8 24)) #x00000000))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(NaN) is a NaN encoding, never +zero's"
    );
}

/// The unspecified NaN case must not leak into ordinary values: `fp.neg` is
/// still a plain sign flip on everything else.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_neg_is_exact_on_non_nan() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp.neg (_ +zero 8 24))) #x80000000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(fp.neg +zero) is exactly 0x80000000"
    );
}

// ========== Sort inference tests ==========

/// fp.to_ieee_bv on Float32 should produce BV32.
#[test]
#[timeout(30_000)]
fn test_ieee_bv_sort_float32() {
    // If the sort is wrong, this would fail during elaboration/sort checking.
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const bv (_ BitVec 32))
        (assert (= bv (fp.to_ieee_bv x)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "fp.to_ieee_bv(Float32) should have sort BV32"
    );
}

/// fp.to_ieee_bv on Float64 should produce BV64.
#[test]
#[timeout(60_000)]
fn test_ieee_bv_sort_float64() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 11 53))
        (declare-const bv (_ BitVec 64))
        (assert (= bv (fp.to_ieee_bv x)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "fp.to_ieee_bv(Float64) should have sort BV64"
    );
}
