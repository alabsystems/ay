// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Integration tests for fp.to_ubv and fp.to_sbv (FP-to-BV conversion).
//!
//! Tests that FP values correctly convert to unsigned/signed bitvectors
//! with proper rounding, overflow handling, and special case treatment.

use ntest::timeout;

// ========== fp.to_ubv tests ==========

/// Float16 1.0 -> unsigned 8-bit BV = 1
#[test]
#[timeout(30_000)]
fn test_to_ubv_one_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b01111 #b0000000000)) #x01)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(1.0) should be 1"
    );
}

/// Float16 2.0 -> unsigned 8-bit BV = 2
#[test]
#[timeout(30_000)]
fn test_to_ubv_two_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b10000 #b0000000000)) #x02)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(2.0) should be 2"
    );
}

/// Float16 0.0 -> unsigned 8-bit BV = 0
#[test]
#[timeout(30_000)]
fn test_to_ubv_zero_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b00000 #b0000000000)) #x00)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(+0.0) should be 0"
    );
}

/// Float16 -0.0 -> unsigned 8-bit BV = 0 (negative zero rounds to 0)
#[test]
#[timeout(30_000)]
fn test_to_ubv_neg_zero_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b1 #b00000 #b0000000000)) #x00)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(-0.0) should be 0"
    );
}

// ========== fp.to_sbv tests ==========

/// Float16 1.0 -> signed 8-bit BV = 1
#[test]
#[timeout(30_000)]
fn test_to_sbv_one_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b0 #b01111 #b0000000000)) #x01)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(1.0) should be 1"
    );
}

/// Float16 -1.0 -> signed 8-bit BV = -1 (0xFF in two's complement)
#[test]
#[timeout(30_000)]
fn test_to_sbv_neg_one_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b1 #b01111 #b0000000000)) #xFF)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(-1.0) should be -1 (0xFF)"
    );
}

/// Float16 -2.0 -> signed 8-bit BV = -2 (0xFE in two's complement)
#[test]
#[timeout(30_000)]
fn test_to_sbv_neg_two_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b1 #b10000 #b0000000000)) #xFE)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(-2.0) should be -2 (0xFE)"
    );
}

/// Float16 0.0 -> signed 8-bit BV = 0
#[test]
#[timeout(30_000)]
fn test_to_sbv_zero_f16() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b0 #b00000 #b0000000000)) #x00)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(0.0) should be 0"
    );
}

// ========== fp.to_ubv rounding tests ==========

/// Float16 1.5 -> unsigned 8-bit BV with RNE = 2 (ties to even)
/// 1.5 is exactly halfway between 1 and 2; RNE rounds to 2 (even)
#[test]
#[timeout(30_000)]
fn test_to_ubv_rne_half_ties_to_even() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b01111 #b1000000000)) #x02)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RNE, 1.5) should be 2 (round to even)"
    );
}

/// Float16 2.5 -> unsigned 8-bit BV with RNE = 2 (ties to even)
/// 2.5 is exactly halfway between 2 and 3; RNE rounds to 2 (even)
/// Float16 2.5 = (fp #b0 #b10000 #b0100000000) = 1.01 × 2^1 = 2.5
#[test]
#[timeout(30_000)]
fn test_to_ubv_rne_2_5_ties_to_even() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b10000 #b0100000000)) #x02)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RNE, 2.5) should be 2 (round to even)"
    );
}

/// Float16 1.5 -> unsigned 8-bit BV with RTZ = 1 (truncate toward zero)
#[test]
#[timeout(30_000)]
fn test_to_ubv_rtz_truncates() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RTZ (fp #b0 #b01111 #b1000000000)) #x01)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RTZ, 1.5) should be 1 (truncate)"
    );
}

/// Float16 1.5 -> unsigned 8-bit BV with RTP = 2 (toward positive infinity)
#[test]
#[timeout(30_000)]
fn test_to_ubv_rtp_rounds_up() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RTP (fp #b0 #b01111 #b1000000000)) #x02)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RTP, 1.5) should be 2 (toward +inf)"
    );
}

/// Float16 1.75 -> unsigned 8-bit BV with RTN = 1 (toward negative infinity)
/// Float16 1.75 = (fp #b0 #b01111 #b1100000000) = 1.11 × 2^0 = 1.75
#[test]
#[timeout(30_000)]
fn test_to_ubv_rtn_rounds_down() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RTN (fp #b0 #b01111 #b1100000000)) #x01)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RTN, 1.75) should be 1 (toward -inf)"
    );
}

// ========== fp.to_sbv rounding tests ==========

/// Float16 -1.5 -> signed 8-bit BV with RNE = -2 (0xFE) (ties to even)
#[test]
#[timeout(30_000)]
fn test_to_sbv_rne_neg_half_ties_to_even() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b1 #b01111 #b1000000000)) #xFE)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(RNE, -1.5) should be -2 (round to even)"
    );
}

/// Float16 -1.5 -> signed 8-bit BV with RTZ = -1 (0xFF) (truncate toward zero)
#[test]
#[timeout(30_000)]
fn test_to_sbv_rtz_neg_truncates() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RTZ (fp #b1 #b01111 #b1000000000)) #xFF)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(RTZ, -1.5) should be -1 (truncate toward zero)"
    );
}

/// Float16 127.0 -> signed 8-bit BV = 127 (0x7F) (max positive value)
/// Float16 127.0 = (fp #b0 #b10101 #b1111110000) = 1.111111 × 2^6 = 127
#[test]
#[timeout(30_000)]
fn test_to_sbv_max_positive() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b0 #b10101 #b1111110000)) #x7F)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(127.0) should be 127 (0x7F)"
    );
}

/// Float16 255.0 -> unsigned 8-bit BV = 255 (0xFF) (max unsigned 8-bit)
/// 255 = 1.1111111 × 2^7, Float16: sign=0, biased_exp=22=10110, sig=1111111000
#[test]
#[timeout(30_000)]
fn test_to_ubv_max_unsigned() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b10110 #b1111111000)) #xFF)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(255.0) should be 255 (0xFF)"
    );
}

// ========== Unspecified behavior tests (NaN, Inf, overflow) ==========
// SMT-LIB: to_ubv/to_sbv with NaN, Inf, or out-of-range produces an
// unspecified bitvector. Solver must not crash or return unsat.
// AY currently returns Unknown for these (safe, conservative behavior).

/// to_ubv(NaN) does not crash or produce unsat
#[test]
#[timeout(30_000)]
fn test_to_ubv_nan_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_ubv 8) RNE (_ NaN 5 11))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_ubv(NaN) should be sat or unknown, got {result:?}"
    );
}

/// to_ubv(+Inf) does not crash or produce unsat
#[test]
#[timeout(30_000)]
fn test_to_ubv_inf_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_ubv 8) RNE (_ +oo 5 11))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_ubv(+Inf) should be sat or unknown, got {result:?}"
    );
}

/// to_ubv(-1.0) does not crash or produce unsat (negative → unsigned is out-of-range)
#[test]
#[timeout(30_000)]
fn test_to_ubv_negative_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_ubv 8) RNE (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_ubv(-1.0) should be sat or unknown, got {result:?}"
    );
}

/// to_ubv(256.0) does not crash (overflow: 256 > max unsigned 8-bit = 255)
/// Float16 256.0 = (fp #b0 #b10111 #b0000000000) = 1.0 × 2^8 = 256
#[test]
#[timeout(30_000)]
fn test_to_ubv_overflow_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_ubv 8) RNE (fp #b0 #b10111 #b0000000000))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_ubv(256.0→8bit) should be sat or unknown, got {result:?}"
    );
}

/// to_sbv(128.0) does not crash (overflow: 128 > max signed 8-bit = 127)
/// Float16 128.0 = (fp #b0 #b10110 #b0000000000) = 1.0 × 2^7 = 128
#[test]
#[timeout(30_000)]
fn test_to_sbv_overflow_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_sbv 8) RNE (fp #b0 #b10110 #b0000000000))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_sbv(128.0→8bit) should be sat or unknown, got {result:?}"
    );
}

/// to_sbv(-256.0) does not crash (underflow: -256 < min signed 8-bit = -128)
/// Float16 -256.0 = (fp #b1 #b10111 #b0000000000)
#[test]
#[timeout(30_000)]
fn test_to_sbv_underflow_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_sbv 8) RNE (fp #b1 #b10111 #b0000000000))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_sbv(-256.0→8bit) should be sat or unknown, got {result:?}"
    );
}

/// to_sbv(NaN) does not crash or produce unsat
#[test]
#[timeout(30_000)]
fn test_to_sbv_nan_does_not_crash() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const r (_ BitVec 8))
        (assert (= r ((_ fp.to_sbv 8) RNE (_ NaN 5 11))))
        (check-sat)
    "#;
    let result = crate::common::solve_vec(smt);
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "to_sbv(NaN) should be sat or unknown, got {result:?}"
    );
}

// ========== Subnormal input tests ==========

/// Float16 smallest subnormal to_ubv should be 0 (value ≈ 5.96e-8, rounds to 0)
#[test]
#[timeout(30_000)]
fn test_to_ubv_subnormal() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNE (fp #b0 #b00000 #b0000000001)) #x00)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(smallest subnormal) should be 0"
    );
}

/// Float16 -128.0 -> signed 8-bit BV = -128 (0x80) (min signed 8-bit)
/// Float16 -128.0 = (fp #b1 #b10110 #b0000000000) = -1.0 × 2^7 = -128
#[test]
#[timeout(30_000)]
fn test_to_sbv_min_signed() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_sbv 8) RNE (fp #b1 #b10110 #b0000000000)) #x80)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_sbv(-128.0) should be -128 (0x80)"
    );
}

/// Float16 RNA (round away from zero): 1.5 -> ubv 8 = 2
#[test]
#[timeout(30_000)]
fn test_to_ubv_rna_half_away() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNA (fp #b0 #b01111 #b1000000000)) #x02)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RNA, 1.5) should be 2 (away from zero)"
    );
}

/// Float16 RNA: 2.5 -> ubv 8 = 3 (NOT 2 — RNA rounds away from zero, unlike RNE)
/// This discriminates RNA from RNE: RNE gives 2, RNA gives 3.
#[test]
#[timeout(30_000)]
fn test_to_ubv_rna_2_5_discriminates_from_rne() {
    let smt = r#"
        (set-logic QF_BVFP)
        (assert (not (= ((_ fp.to_ubv 8) RNA (fp #b0 #b10000 #b0100000000)) #x03)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "to_ubv(RNA, 2.5) should be 3 (round away from zero, not 2 like RNE)"
    );
}
