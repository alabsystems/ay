// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Integration tests for fp.roundToIntegral.
//!
//! |x| < 1 tests: Regression for #5902 (hardcoded round/sticky bits).
//! |x| > 1 tests: Coverage for general masking path (mask fractional bits,
//! compute last/round/sticky, apply rounding increment).

use ntest::timeout;

// ========== RNE (Round to Nearest, ties to Even) ==========

/// roundToIntegral(RNE, 0.75) = 1.0
/// 0.75 is in (0.5, 1.0), so rounds up to 1.0.
/// This is the primary regression test for #5902.
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_075() {
    // Float16: 0.75 = (fp #b0 #b01110 #b1000000000)
    // 1.0 = (fp #b0 #b01111 #b0000000000)
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b01110 #b1000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 0.75) should be 1.0"
    );
}

/// roundToIntegral(RNE, 0.5) = 0.0
/// Exactly 0.5 ties to even: 0 is even, so rounds to 0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_05() {
    // Float16: 0.5 = (fp #b0 #b01110 #b0000000000)
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b01110 #b0000000000))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 0.5) should be +0.0 (ties to even)"
    );
}

/// roundToIntegral(RNE, 0.25) = 0.0
/// 0.25 < 0.5, so rounds to 0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_025() {
    // Float16: 0.25 = (fp #b0 #b01101 #b0000000000)
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b01101 #b0000000000))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 0.25) should be +0.0"
    );
}

/// roundToIntegral(RNE, -0.75) = -1.0
/// -0.75 is in (-1.0, -0.5), rounds to -1.0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_neg_075() {
    // Float16: -0.75 = (fp #b1 #b01110 #b1000000000)
    // -1.0 = (fp #b1 #b01111 #b0000000000)
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b1 #b01110 #b1000000000))
            (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, -0.75) should be -1.0"
    );
}

// ========== RNA (Round to Nearest, ties Away from zero) ==========

/// roundToIntegral(RNA, 0.5) = 1.0
/// Exactly 0.5 rounds away from zero to 1.0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rna_05() {
    // Float16: 0.5 = (fp #b0 #b01110 #b0000000000)
    // 1.0 = (fp #b0 #b01111 #b0000000000)
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNA (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNA, 0.5) should be 1.0 (ties away)"
    );
}

/// roundToIntegral(RNA, 0.25) = 0.0
/// 0.25 < 0.5, rounds to 0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rna_025() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNA (fp #b0 #b01101 #b0000000000))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNA, 0.25) should be +0.0"
    );
}

// ========== RTP (Round Toward Positive infinity) ==========

/// roundToIntegral(RTP, 0.25) = 1.0
/// Any positive value with |x| < 1 rounds up to 1.0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rtp_025() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTP (fp #b0 #b01101 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTP, 0.25) should be 1.0"
    );
}

/// roundToIntegral(RTP, -0.75) = -0.0
/// Negative value rounds toward +inf, which is -0.0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rtp_neg_075() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTP (fp #b1 #b01110 #b1000000000))
            (_ -zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTP, -0.75) should be -0.0"
    );
}

// ========== RTN (Round Toward Negative infinity) ==========

/// roundToIntegral(RTN, 0.75) = 0.0
/// Positive value rounds toward -inf, which is +0.0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rtn_075() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTN (fp #b0 #b01110 #b1000000000))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTN, 0.75) should be +0.0"
    );
}

/// roundToIntegral(RTN, -0.25) = -1.0
/// Negative value rounds toward -inf, which is -1.0.
#[test]
#[timeout(60_000)]
fn test_round_integral_rtn_neg_025() {
    // Float16: -0.25 = (fp #b1 #b01101 #b0000000000)
    // -1.0 = (fp #b1 #b01111 #b0000000000)
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTN (fp #b1 #b01101 #b0000000000))
            (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTN, -0.25) should be -1.0"
    );
}

// ========== RTZ (Round Toward Zero) ==========

/// roundToIntegral(RTZ, 0.75) = 0.0
/// Truncates toward zero.
#[test]
#[timeout(60_000)]
fn test_round_integral_rtz_075() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTZ (fp #b0 #b01110 #b1000000000))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTZ, 0.75) should be +0.0"
    );
}

/// roundToIntegral(RTZ, -0.75) = -0.0
/// Truncates toward zero.
#[test]
#[timeout(60_000)]
fn test_round_integral_rtz_neg_075() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTZ (fp #b1 #b01110 #b1000000000))
            (_ -zero 5 11))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTZ, -0.75) should be -0.0"
    );
}

// =====================================================================
// Values > 1: general masking path (mask fractional bits + rounding)
// =====================================================================

// ========== RNE ties-to-even for values > 1 ==========

/// roundToIntegral(RNE, 2.5) = 2.0 (tie rounds to even: 2 is even)
/// Float16: 2.5 = 1.01 × 2^1 → (fp #b0 #b10000 #b0100000000)
/// 2.0 = (fp #b0 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b10000 #b0100000000))
            (fp #b0 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 2.5) should be 2.0 (tie to even)"
    );
}

/// roundToIntegral(RNE, 3.5) = 4.0 (tie rounds to even: 4 is even)
/// Float16: 3.5 = 1.11 × 2^1 → (fp #b0 #b10000 #b1100000000)
/// 4.0 = (fp #b0 #b10001 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_3_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b10000 #b1100000000))
            (fp #b0 #b10001 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 3.5) should be 4.0 (tie to even)"
    );
}

/// roundToIntegral(RNE, 1.75) = 2.0 (above midpoint, rounds up)
/// Float16: 1.75 = 1.11 × 2^0 → (fp #b0 #b01111 #b1100000000)
/// 2.0 = (fp #b0 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_1_75() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b01111 #b1100000000))
            (fp #b0 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 1.75) should be 2.0"
    );
}

/// roundToIntegral(RNE, 2.25) = 2.0 (below midpoint, rounds down)
/// Float16: 2.25 = 1.001 × 2^1 → (fp #b0 #b10000 #b0010000000)
/// 2.0 = (fp #b0 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_2_25() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b10000 #b0010000000))
            (fp #b0 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 2.25) should be 2.0"
    );
}

// ========== RNE negative values > 1 ==========

/// roundToIntegral(RNE, -2.5) = -2.0 (tie rounds to even: 2 is even)
/// Float16: -2.5 = (fp #b1 #b10000 #b0100000000)
/// -2.0 = (fp #b1 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_neg_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b1 #b10000 #b0100000000))
            (fp #b1 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, -2.5) should be -2.0 (tie to even)"
    );
}

/// roundToIntegral(RNE, -1.5) = -2.0 (tie rounds to even: 2 is even)
/// This also tests sig overflow: 1.1 × 2^0 rounded up → 10.0 × 2^0 = 1.0 × 2^1
/// Float16: -1.5 = (fp #b1 #b01111 #b1000000000)
/// -2.0 = (fp #b1 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_neg_1_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b1 #b01111 #b1000000000))
            (fp #b1 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, -1.5) should be -2.0 (tie to even, sig overflow)"
    );
}

// ========== RNA (Round to Nearest, ties Away) for values > 1 ==========

/// roundToIntegral(RNA, 2.5) = 3.0 (tie rounds away from zero)
/// Discriminates RNA from RNE: RNE→2.0, RNA→3.0
/// Float16: 3.0 = (fp #b0 #b10000 #b1000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rna_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNA (fp #b0 #b10000 #b0100000000))
            (fp #b0 #b10000 #b1000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNA, 2.5) should be 3.0 (tie away)"
    );
}

/// roundToIntegral(RNA, -2.5) = -3.0 (tie rounds away from zero)
/// Float16: -3.0 = (fp #b1 #b10000 #b1000000000)
#[test]
#[timeout(60_000)]
fn test_round_integral_rna_neg_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNA (fp #b1 #b10000 #b0100000000))
            (fp #b1 #b10000 #b1000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNA, -2.5) should be -3.0 (tie away)"
    );
}

// ========== RTP (Round Toward Positive infinity) for values > 1 ==========

/// roundToIntegral(RTP, 2.5) = 3.0 (ceil)
#[test]
#[timeout(60_000)]
fn test_round_integral_rtp_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTP (fp #b0 #b10000 #b0100000000))
            (fp #b0 #b10000 #b1000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTP, 2.5) should be 3.0"
    );
}

/// roundToIntegral(RTP, -2.5) = -2.0 (toward +inf)
#[test]
#[timeout(60_000)]
fn test_round_integral_rtp_neg_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTP (fp #b1 #b10000 #b0100000000))
            (fp #b1 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTP, -2.5) should be -2.0"
    );
}

include!("fp_round_integral/rtn_rtz_and_boundaries.rs");
