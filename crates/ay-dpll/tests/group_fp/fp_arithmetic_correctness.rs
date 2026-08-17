// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Semantic correctness tests for FP arithmetic operations (#3586).
//!
//! Tests fp.div, fp.sqrt, fp.fma, and fp.roundToIntegral through the full
//! executor pipeline (parse → Tseitin → FP bit-blasting → SAT → result).
//!
//! Uses Float16 (5,11) to keep CNF size small and avoid SAT solver timeouts.
//! Float16 bit patterns (bias=15):
//!   1.0  = (fp #b0 #b01111 #b0000000000)   exp=15 → real_exp=0
//!   2.0  = (fp #b0 #b10000 #b0000000000)   exp=16 → real_exp=1
//!   4.0  = (fp #b0 #b10001 #b0000000000)   exp=17 → real_exp=2
//!   0.5  = (fp #b0 #b01110 #b0000000000)   exp=14 → real_exp=-1
//!   3.0  = (fp #b0 #b10000 #b1000000000)   exp=16, sig=1.1 → 1.5*2=3
//!  10.0  = (fp #b0 #b10010 #b0100000000)   exp=18, sig=1.01 → 1.25*8=10
//!   1.5  = (fp #b0 #b01111 #b1000000000)   exp=15, sig=1.1 → 1.5

use ntest::timeout;

// =========================================================================
// fp.div — IEEE 754 Division
// =========================================================================

/// fp.div: 1.0 / 2.0 = 0.5 (simple division, RNE).
#[test]
#[timeout(60_000)]
fn test_fp_div_one_over_two() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b01111 #b0000000000)))
        (assert (= y (fp #b0 #b10000 #b0000000000)))
        (assert (= z (fp.div RNE x y)))
        (assert (fp.eq z (fp #b0 #b01110 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 / 2.0 should equal 0.5");
}

/// fp.div: 4.0 / 2.0 = 2.0 (exact division).
#[test]
#[timeout(60_000)]
fn test_fp_div_four_over_two() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b10001 #b0000000000)))
        (assert (= y (fp #b0 #b10000 #b0000000000)))
        (assert (= z (fp.div RNE x y)))
        (assert (fp.eq z (fp #b0 #b10000 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "4.0 / 2.0 should equal 2.0");
}

/// fp.div: x / 0.0 should be infinite (for finite nonzero x).
#[test]
#[timeout(60_000)]
fn test_fp_div_by_zero_is_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b01111 #b0000000000)))
        (assert (= y (_ +zero 5 11)))
        (assert (= z (fp.div RNE x y)))
        (assert (fp.isInfinite z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "1.0 / 0.0 should be infinite");
}

/// fp.div: 0.0 / 0.0 should be NaN.
#[test]
#[timeout(60_000)]
fn test_fp_div_zero_over_zero_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ +zero 5 11)))
        (assert (= z (fp.div RNE x y)))
        (assert (fp.isNaN z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "0.0 / 0.0 should be NaN");
}

/// fp.div: 1.0 / 3.0 should produce a correctly-rounded Float16 result (RNE).
/// 1/3 = 0.3333... = 1.0101010101... × 2^(-2)
/// Float16 (5,11) stores 10 significand bits, so 1.0101010101 × 2^(-2)
/// Bit pattern: sign=0, biased_exp=13=01101, sig=0101010101
/// Value = 2^(-2) × (1 + 341/1024) = 0.333251953125
#[test]
#[timeout(60_000)]
fn test_fp_div_one_over_three_rne() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RNE (fp #b0 #b01111 #b0000000000) (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b01101 #b0101010101))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "1.0 / 3.0 should be correctly rounded (RNE)"
    );
}

/// fp.div: (-1.0) / 2.0 = -0.5 (negative dividend, positive divisor)
#[test]
#[timeout(60_000)]
fn test_fp_div_neg_one_over_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RNE (fp #b1 #b01111 #b0000000000) (fp #b0 #b10000 #b0000000000))
            (fp #b1 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "(-1.0) / 2.0 should be -0.5");
}

/// fp.div: 1.0 / (-2.0) = -0.5 (positive dividend, negative divisor)
#[test]
#[timeout(60_000)]
fn test_fp_div_one_over_neg_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RNE (fp #b0 #b01111 #b0000000000) (fp #b1 #b10000 #b0000000000))
            (fp #b1 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "1.0 / (-2.0) should be -0.5");
}

/// fp.div: (-1.0) / (-2.0) = 0.5 (both negative → positive result)
#[test]
#[timeout(60_000)]
fn test_fp_div_neg_one_over_neg_two() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RNE (fp #b1 #b01111 #b0000000000) (fp #b1 #b10000 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "(-1.0) / (-2.0) should be 0.5");
}

/// fp.div: inf / inf = NaN
#[test]
#[timeout(60_000)]
fn test_fp_div_inf_over_inf_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.div RNE (_ +oo 5 11) (_ +oo 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "inf / inf should be NaN");
}

/// fp.div: 1.0 / 3.0 with RTZ rounding mode should truncate toward zero.
/// RTZ truncates, so 1/3 rounded toward zero: 1.0101010101 × 2^(-2)
/// (same as RNE in this case since the discarded bits are 01... which is < 0.5 ULP)
#[test]
#[timeout(60_000)]
fn test_fp_div_one_over_three_rtz() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RTZ (fp #b0 #b01111 #b0000000000) (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b01101 #b0101010101))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "1.0 / 3.0 with RTZ should truncate correctly"
    );
}

/// fp.div: subnormal / 1.0 = subnormal (denormal dividend exercises unpack with lz > 0).
/// Float16 subnormal: (fp #b0 #b00000 #b0100000000) = 0.01 × 2^(-14) = 2^(-16)
/// Dividing by 1.0 should return the subnormal unchanged.
#[test]
#[timeout(60_000)]
fn test_fp_div_subnormal_dividend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RNE (fp #b0 #b00000 #b0100000000) (fp #b0 #b01111 #b0000000000))
            (fp #b0 #b00000 #b0100000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "subnormal / 1.0 should be the subnormal itself"
    );
}

/// fp.div: 1.0 / subnormal should produce a large result (exercises subnormal divisor path).
/// Float16 subnormal: (fp #b0 #b00000 #b0100000000) = 2^(-16)
/// 1.0 / 2^(-16) = 2^16 = 65536, which overflows Float16 max (65504) → result is +infinity.
#[test]
#[timeout(60_000)]
fn test_fp_div_subnormal_divisor_overflows() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            (fp.div RNE (fp #b0 #b01111 #b0000000000) (fp #b0 #b00000 #b0100000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "1.0 / subnormal should overflow to +infinity"
    );
}

/// fp.div: overflow to infinity when quotient exceeds max normal.
/// max_normal / 0.5 = 65504 / 0.5 = 131008, which exceeds Float16 max → +infinity.
/// Float16 max normal: (fp #b0 #b11110 #b1111111111) = 65504.0
/// Float16 0.5: (fp #b0 #b01110 #b0000000000) = 0.5
#[test]
#[timeout(60_000)]
fn test_fp_div_overflow_to_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isInfinite
            (fp.div RNE (fp #b0 #b11110 #b1111111111) (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "max_normal / 0.5 should overflow to +infinity"
    );
}

// =========================================================================
// fp.sqrt — IEEE 754 Square Root
// =========================================================================

/// fp.sqrt: sqrt(4.0) = 2.0 (exact square root).
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_four() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b10001 #b0000000000)))
        (assert (= z (fp.sqrt RNE x)))
        (assert (fp.eq z (fp #b0 #b10000 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "sqrt(4.0) should equal 2.0");
}

/// fp.sqrt: sqrt(1.0) = 1.0.
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_one() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b01111 #b0000000000)))
        (assert (= z (fp.sqrt RNE x)))
        (assert (fp.eq z (fp #b0 #b01111 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "sqrt(1.0) should equal 1.0");
}

/// fp.sqrt: sqrt(-1.0) should be NaN.
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_negative_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b1 #b01111 #b0000000000)))
        (assert (= z (fp.sqrt RNE x)))
        (assert (fp.isNaN z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "sqrt(-1.0) should be NaN");
}

/// fp.sqrt: sqrt(+0) should be +0.
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= z (fp.sqrt RNE x)))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "sqrt(+0) should be zero");
}

/// fp.sqrt: sqrt(2.0) correctly rounded (inexact result).
/// sqrt(2) = 1.01101010000010011110... in binary.
/// Float16 (10 stored bits): sig = 0110101000, round bit = 0 → round down.
/// Result: (fp #b0 #b01111 #b0110101000) ≈ 1.4140625
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_two_rne() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.sqrt RNE (fp #b0 #b10000 #b0000000000))
            (fp #b0 #b01111 #b0110101000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sqrt(2.0) should be correctly rounded (RNE)"
    );
}

/// fp.sqrt: sqrt(+inf) = +inf
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_inf() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.sqrt RNE (_ +oo 5 11))
            (_ +oo 5 11))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "sqrt(+inf) should be +inf");
}

/// fp.sqrt: sqrt(-0) = -0 (IEEE 754: sign preserved for zero)
#[test]
#[timeout(60_000)]
fn test_fp_sqrt_neg_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.sqrt RNE (_ -zero 5 11))))
        (assert (fp.isZero z))
        (assert (not (= z (fp #b1 #b00000 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sqrt(-0) should be -0.0 (structural)"
    );
}

// =========================================================================
// fp.fma — Fused Multiply-Add (single rounding)
// =========================================================================

include!("fp_arithmetic_correctness/fma.rs");

include!("fp_arithmetic_correctness/rounding_edges.rs");
