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

/// NaN literal: fp.to_ieee_bv must produce a valid NaN BV encoding.
/// Canonical quiet NaN for Float32 = 0x7fc00000 (sign=0, exp=0xFF, sig=0x400000).
#[test]
#[timeout(30_000)]
fn test_ieee_bv_nan_literal_float32() {
    // Use a NaN literal (sign=0, exp=all-ones, sig MSB=1, rest=0) and verify
    // fp.to_ieee_bv produces the expected BV. This is UNSAT if the bit-blast
    // correctly maps the NaN literal to its IEEE 754 encoding.
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= (fp.to_ieee_bv (fp #b0 #b11111111 #b10000000000000000000000)) #x7fc00000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "fp.to_ieee_bv(quiet NaN literal) should be 0x7fc00000"
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
