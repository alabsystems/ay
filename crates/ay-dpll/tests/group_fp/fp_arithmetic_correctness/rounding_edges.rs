// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp_arithmetic_correctness` to preserve test FQNs.

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
