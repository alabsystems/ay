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

/// fp.fma: fma(2.0, 3.0, 4.0) = 10.0 (2*3+4 = 10, single rounding).
#[test]
#[timeout(60_000)]
fn test_fp_fma_two_three_four() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 5 11))
        (declare-const b (_ FloatingPoint 5 11))
        (declare-const c (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= a (fp #b0 #b10000 #b0000000000)))
        (assert (= b (fp #b0 #b10000 #b1000000000)))
        (assert (= c (fp #b0 #b10001 #b0000000000)))
        (assert (= z (fp.fma RNE a b c)))
        (assert (fp.eq z (fp #b0 #b10010 #b0100000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "fma(2.0, 3.0, 4.0) should equal 10.0");
}

/// fp.fma: fma(1.0, 1.0, 0.0) = 1.0 (identity-like).
#[test]
#[timeout(60_000)]
fn test_fp_fma_identity() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 5 11))
        (declare-const b (_ FloatingPoint 5 11))
        (declare-const c (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= a (fp #b0 #b01111 #b0000000000)))
        (assert (= b (fp #b0 #b01111 #b0000000000)))
        (assert (= c (_ +zero 5 11)))
        (assert (= z (fp.fma RNE a b c)))
        (assert (fp.eq z (fp #b0 #b01111 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "fma(1.0, 1.0, 0.0) should equal 1.0");
}

/// fp.fma: fma(inf, 0, x) should be NaN.
#[test]
#[timeout(60_000)]
fn test_fp_fma_inf_times_zero_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 5 11))
        (declare-const b (_ FloatingPoint 5 11))
        (declare-const c (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= a (_ +oo 5 11)))
        (assert (= b (_ +zero 5 11)))
        (assert (= c (fp #b0 #b01111 #b0000000000)))
        (assert (= z (fp.fma RNE a b c)))
        (assert (fp.isNaN z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "fma(+inf, 0, 1.0) should be NaN");
}

/// fp.fma: fma(2.0, -3.0, 4.0) = -2.0 (negative product plus positive addend)
/// 2.0 * (-3.0) + 4.0 = -6.0 + 4.0 = -2.0
/// Float16: -3.0 = (fp #b1 #b10000 #b1000000000), -2.0 = (fp #b1 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_fp_fma_neg_product() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (fp #b0 #b10000 #b0000000000)
                (fp #b1 #b10000 #b1000000000)
                (fp #b0 #b10001 #b0000000000))
            (fp #b1 #b10000 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(2.0, -3.0, 4.0) should be -2.0");
}

/// fp.fma: fma(a, b, NaN) = NaN (NaN propagation from addend)
#[test]
#[timeout(60_000)]
fn test_fp_fma_nan_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (fp #b0 #b01111 #b0000000000)
                (fp #b0 #b10000 #b0000000000)
                (_ NaN 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(1.0, 2.0, NaN) should be NaN");
}

/// fp.fma: fma(+inf, 1.0, -inf) = NaN (inf + (-inf) cancellation)
#[test]
#[timeout(60_000)]
fn test_fp_fma_inf_cancel() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +oo 5 11)
                (fp #b0 #b01111 #b0000000000)
                (_ -oo 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(+inf, 1.0, -inf) should be NaN");
}

// =========================================================================
// fp.fma zero-factor rewrite (Z3 PR #9038 / issue #8185)
//
// When one multiplicand is a concrete FP zero, the fma bit-blast is
// replaced by a reduced encoding:
//   ite(isNaN(other) | isInf(other), NaN, add(product_zero, z))
// where product_zero's sign = sign(zero) XOR sign(other).
// =========================================================================

/// fma(+0, 2.0, 0.5) = 0.5 (0 * finite + c = c for nonzero c).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_pos_zero_times_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(+0, 2.0, 0.5) should equal 0.5");
}

/// fma(-0, 2.0, 0.5) = 0.5 (sign(-0 * +2.0) = -0; -0 + 0.5 = 0.5).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_neg_zero_times_pos_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ -zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(-0, 2.0, 0.5) should equal 0.5");
}

/// fma(+0, +inf, 0.5) = NaN (0 * inf = NaN, NaN + anything = NaN).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_zero_times_inf_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +zero 5 11)
                (_ +oo 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, +inf, 0.5) should be NaN (0 * inf = NaN)"
    );
}

/// fma(+0, NaN, 0.5) = NaN (NaN propagation through multiplication).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_zero_times_nan_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +zero 5 11)
                (_ NaN 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, NaN, 0.5) should be NaN (NaN propagation)"
    );
}

/// fma(+0, -1.0, +0) = +0 under RNE (sign(+0 * -1) = -0; -0 + +0 = +0).
/// IEEE 754 § 6.3: the sign of a sum of zeros of opposite sign is +0
/// under RNE, RNA, RTP, RTZ (only RTN gives -0).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_sign_rne() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ +zero 5 11)
                (fp #b1 #b01111 #b0000000000)
                (_ +zero 5 11))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, -1.0, +0) RNE: (-0)+(+0) = +0"
    );
}

/// fma(-0, -1.0, -0) = -0 (sign(-0 * -1) = +0; +0 + -0 = +0 under RNE, but
/// here addend is -0 and product is +0, so (+0)+(-0) = +0 under RNE.
/// We only check structural result: the sum is zero (not infinity/NaN).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_neg_zero_neg_finite_is_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isZero
            (fp.fma RNE
                (_ -zero 5 11)
                (fp #b1 #b01111 #b0000000000)
                (_ -zero 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(-0, -1.0, -0) should be zero (product is +0, +0+(-0)=+0)"
    );
}

/// fma(x, +0, 0.5) = 0.5 (symmetry: zero can be either multiplicand).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_finite_times_pos_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (fp #b0 #b10000 #b0000000000)
                (_ +zero 5 11)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(2.0, +0, 0.5) should equal 0.5");
}

/// fma(-0, +0, +0) = +0 (both multiplicands zero, addend also +0).
/// product sign = sign(-0) XOR sign(+0) = 1 XOR 0 = 1 → product = -0.
/// Under RNE: (-0) + (+0) = +0.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_both_zero_multiplicands() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ -zero 5 11)
                (_ +zero 5 11)
                (_ +zero 5 11))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(-0, +0, +0) RNE: product=-0, -0 + +0 = +0"
    );
}

/// fma(+0, -1.0, +0) under RTN = -0 (sign-of-sum special rule).
/// IEEE 754 § 6.3: `(+x) + (-x) = -0` only under RTN, `+0` under other modes.
/// Here product = -0, addend = +0, so sum is (-0) + (+0) = -0 under RTN.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_sign_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z
            (fp.fma RTN
                (_ +zero 5 11)
                (fp #b1 #b01111 #b0000000000)
                (_ +zero 5 11))))
        (assert (= z (_ -zero 5 11)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "fma(+0, -1.0, +0) RTN: product=-0, -0 + +0 = -0"
    );
}

/// fma(+0, 2.0, 0.5) under RTZ = 0.5 (no rounding; 0 + 0.5 is exact).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_rtz_finite_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTZ
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, 2.0, 0.5) RTZ should equal 0.5"
    );
}

/// fma(+0, 2.0, 0.5) under RTP = 0.5 (no rounding needed).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_rtp_finite_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTP
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, 2.0, 0.5) RTP should equal 0.5"
    );
}

/// fma(+0, 2.0, 0.5) under RNA = 0.5 (ties away; 0+0.5 needs no rounding).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_rna_finite_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNA
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, 2.0, 0.5) RNA should equal 0.5"
    );
}

/// fma(+0, -inf, 0.5) = NaN (0 * -inf = NaN per IEEE-754).
/// Symmetric with test_fp_fma_zero_factor_zero_times_inf_is_nan but negative inf.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_zero_times_neg_inf_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +zero 5 11)
                (_ -oo 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, -inf, 0.5) should be NaN (0 * -inf = NaN)"
    );
}

/// fma(-0, NaN, 0.5) = NaN (NaN propagates regardless of zero sign).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_neg_zero_times_nan_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ -zero 5 11)
                (_ NaN 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(-0, NaN, 0.5) should be NaN");
}

/// Z3 #8185 reproducer core pattern: `fma(+0, finite, 0.5) = 0.5` exactly.
/// This is the simplification Z3 failed to apply in time, producing an invalid
/// model. The rewrite in `fma.rs::try_make_fma_zero_factor` catches this.
///
/// Note: the full #8185 benchmark uses an integer→real→fp chain; this test
/// exercises only the fma-zero rewrite, which is the specific Z3 fix target.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_z3_issue_8185_pattern() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.fma RNE (_ +zero 5 11) x (fp #b0 #b01110 #b0000000000))))
        (assert (fp.isNormal z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // When x is finite, z = 0.5 (normal). When x is inf or NaN, z is NaN
    // (non-normal). The assertion fp.isNormal z is satisfiable via any finite
    // x; the rewriter must propagate z ≈ 0.5 for finite x.
    assert_eq!(
        outputs,
        vec!["sat"],
        "#8185 pattern: fma(+0, finite_x, 0.5) should be 0.5 (normal)"
    );
}

/// fp.fma single-rounding discrimination: fma(a, b, c) ≠ round(round(a*b) + c)
///
/// a = 1025/1024 = 1 + 2^(-10) = (fp #b0 #b01111 #b0000000001)
/// b = 1023/1024 = 1 - 2^(-10) = (fp #b0 #b01110 #b1111111110)
/// c = -(1023/1024)            = (fp #b1 #b01110 #b1111111110)
///
/// Exact a*b = 1 - 2^(-20) (21 sig bits; exceeds Float16's 11 sig bits)
/// round(a*b) = 1.0 (rounds up since trailing bits > 0.5 ULP)
///
/// Separate (double-round): round(1.0 + c) = round(1.0 - 1023/1024) = 2^(-10)
/// = (fp #b0 #b00101 #b0000000000)
///
/// Fused (single-round): exact a*b + c = (1 - 2^(-20)) - (1 - 2^(-10))
///   = 2^(-10) - 2^(-20) = 2^(-10) × (1 - 2^(-10))
///   = 1.111111111_0 × 2^(-11) = (fp #b0 #b00100 #b1111111110)
///
/// The fused result is smaller than the separate result by 2^(-20).
#[test]
#[timeout(120_000)]
fn test_fp_fma_single_rounding_discrimination() {
    // Verify fma gives the fused (single-round) result
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b01110 #b1111111110)
                (fp #b1 #b01110 #b1111111110))
            (fp #b0 #b00100 #b1111111110))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma should give single-round result (2^(-10) - 2^(-20)), not double-round (2^(-10))"
    );
}

// =========================================================================
// fp.add — IEEE 754 Addition (rounding path)
// =========================================================================

/// fp.add: 1.0 + 2^(-11) = 1.0 (RNE tie, last=0 → round down to even)
/// Float16: 1.0 = (fp #b0 #b01111 #b0000000000), stored LSB = 0
/// 2^(-11) = 1.0 × 2^(-11), biased exp = 4 = (fp #b0 #b00100 #b0000000000)
/// Exact sum: 1.00000000001 (12 sig bits). Rounding: last=0, round=1, sticky=0.
/// RNE tie: 0 is even → round down → result stays 1.0.
#[test]
#[timeout(60_000)]
fn test_fp_add_rne_tie_round_down() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.add RNE
                (fp #b0 #b01111 #b0000000000)
                (fp #b0 #b00100 #b0000000000))
            (fp #b0 #b01111 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "1.0 + 2^(-11) RNE should stay 1.0 (tie to even, round down)"
    );
}

/// fp.add: (1 + 2^(-10)) + 2^(-11) = 1 + 2^(-9) (RNE tie, last=1 → round up to even)
/// Float16: 1+2^(-10) = (fp #b0 #b01111 #b0000000001), stored LSB = 1
/// Exact sum: 1.00000000011 (12 sig bits). Rounding: last=1, round=1, sticky=0.
/// RNE tie: 1 is odd → round up → result = 1.0000000010 = 1 + 2^(-9).
/// Together with test_fp_add_rne_tie_round_down, this discriminates ties-to-even.
#[test]
#[timeout(60_000)]
fn test_fp_add_rne_tie_round_up() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.add RNE
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b00100 #b0000000000))
            (fp #b0 #b01111 #b0000000010))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "(1+2^(-10)) + 2^(-11) RNE should round up to 1+2^(-9) (tie to even, round up)"
    );
}

/// fp.add: 1.0 + 2^(-11) = 1 + 2^(-10) (RTP rounds up)
/// Same inputs as tie-round-down test, but RTP always rounds toward +inf.
/// Result: 1.0000000001 = 1 + 2^(-10) = (fp #b0 #b01111 #b0000000001)
#[test]
#[timeout(60_000)]
fn test_fp_add_rtp_rounds_up() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.add RTP
                (fp #b0 #b01111 #b0000000000)
                (fp #b0 #b00100 #b0000000000))
            (fp #b0 #b01111 #b0000000001))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "1.0 + 2^(-11) RTP should round up to 1+2^(-10)"
    );
}

/// fp.add: negative rounding: (-1.0) + (-2^(-11)) = -1.0 (RNE tie, round to even)
/// Mirror of tie-round-down test with negative values.
#[test]
#[timeout(60_000)]
fn test_fp_add_neg_rne_tie() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.add RNE
                (fp #b1 #b01111 #b0000000000)
                (fp #b1 #b00100 #b0000000000))
            (fp #b1 #b01111 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "(-1.0) + (-2^(-11)) RNE should stay -1.0"
    );
}

// =========================================================================
// fp.mul — IEEE 754 Multiplication (rounding path)
// =========================================================================

/// fp.mul: (1.5 + 2^(-10)) × 3.0, inexact product requiring rounding.
/// a = 1537/1024 = (fp #b0 #b01111 #b1000000001) (1.1000000001 × 2^0)
/// b = 3.0 = (fp #b0 #b10000 #b1000000000) (1.1 × 2^1)
/// Exact product: 4611/1024 = 100.1000000011 = 1.001000000011 × 2^2 (13 sig bits)
/// Stored 10 bits: 0010000000, extra: 11 → round=1, sticky=1 → round up
/// Result: 1.0010000001 × 2^2 = (fp #b0 #b10001 #b0010000001)
#[test]
#[timeout(60_000)]
fn test_fp_mul_inexact_round_up() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.mul RNE
                (fp #b0 #b01111 #b1000000001)
                (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b10001 #b0010000001))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "(1.5+2^(-10)) × 3.0 should round up (round=1, sticky=1)"
    );
}

/// fp.mul: RTZ truncation gives different result from RNE.
/// Same inputs as above, but RTZ truncates → no round-up.
/// Result: 1.0010000000 × 2^2 = (fp #b0 #b10001 #b0010000000)
#[test]
#[timeout(60_000)]
fn test_fp_mul_rtz_truncates() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.mul RTZ
                (fp #b0 #b01111 #b1000000001)
                (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b10001 #b0010000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "(1.5+2^(-10)) × 3.0 RTZ should truncate (no round-up)"
    );
}

// =========================================================================
// fp.roundToIntegral — Round to nearest integer
// =========================================================================

/// fp.roundToIntegral: roundToIntegral(RNE, 1.5) should be 2.0 (round to even).
#[test]
#[timeout(60_000)]
fn test_fp_round_to_integral_1_5() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b01111 #b1000000000)))
        (assert (= z (fp.roundToIntegral RNE x)))
        (assert (fp.eq z (fp #b0 #b10000 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "roundToIntegral(RNE, 1.5) should equal 2.0"
    );
}

/// fp.roundToIntegral: roundToIntegral(RNE, 2.0) should be 2.0 (already integral).
#[test]
#[timeout(60_000)]
fn test_fp_round_to_integral_already_integer() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (fp #b0 #b10000 #b0000000000)))
        (assert (= z (fp.roundToIntegral RNE x)))
        (assert (fp.eq z (fp #b0 #b10000 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "roundToIntegral(RNE, 2.0) should equal 2.0"
    );
}

/// fp.roundToIntegral: roundToIntegral(RNE, +0) should be +0.
#[test]
#[timeout(60_000)]
fn test_fp_round_to_integral_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= z (fp.roundToIntegral RNE x)))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "roundToIntegral(RNE, +0) should be zero"
    );
}

/// fp.roundToIntegral: roundToIntegral(RNE, NaN) should be NaN.
#[test]
#[timeout(60_000)]
fn test_fp_round_to_integral_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (fp.isNaN x))
        (assert (= z (fp.roundToIntegral RNE x)))
        (assert (fp.isNaN z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "roundToIntegral(RNE, NaN) should be NaN"
    );
}
