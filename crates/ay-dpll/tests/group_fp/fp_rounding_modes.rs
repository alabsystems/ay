// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Non-RNE rounding mode tests for fp.div, fp.sqrt, and fp.fma (#3586, #3226).
//!
//! Each test uses discriminating inputs where the rounding mode affects the result.
//! Uses Float16 (5,11) to keep CNF size small.
//!
//! Float16 bit patterns (bias=15):
//!   1.0  = (fp #b0 #b01111 #b0000000000)
//!   3.0  = (fp #b0 #b10000 #b1000000000)
//!   5.0  = (fp #b0 #b10001 #b0100000000)
//!   +0   = (fp #b0 #b00000 #b0000000000)
//!   1+eps = (fp #b0 #b01111 #b0000000001) where eps = 2^-10

use ntest::timeout;

// =========================================================================
// fp.div — Non-RNE Rounding Modes
// =========================================================================
// 5/3 = 1.10101010101... binary. Guard=1, Round=0, Sticky=1 → above halfway.
// RNE/RNA/RTP round up (mantissa 1010101011), RTZ/RTN truncate (1010101010).

/// fp.div: 5.0 / 3.0 with RTZ truncates (differs from RNE).
#[test]
#[timeout(120_000)]
fn test_fp_div_five_over_three_rtz() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RTZ (fp #b0 #b10001 #b0100000000) (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b01111 #b1010101010))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "5/3 with RTZ should truncate to 1.666015625"
    );
}

/// fp.div: 5.0 / 3.0 with RTN truncates (toward -inf = truncate for positive).
#[test]
#[timeout(120_000)]
fn test_fp_div_five_over_three_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RTN (fp #b0 #b10001 #b0100000000) (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b01111 #b1010101010))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "5/3 with RTN should truncate for positive"
    );
}

/// fp.div: 5.0 / 3.0 with RTP rounds up (above halfway, positive).
#[test]
#[timeout(120_000)]
fn test_fp_div_five_over_three_rtp() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RTP (fp #b0 #b10001 #b0100000000) (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b01111 #b1010101011))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "5/3 with RTP should round up for positive"
    );
}

/// fp.div: 5.0 / 3.0 with RNA rounds away from zero (above halfway).
#[test]
#[timeout(120_000)]
fn test_fp_div_five_over_three_rna() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.div RNA (fp #b0 #b10001 #b0100000000) (fp #b0 #b10000 #b1000000000))
            (fp #b0 #b01111 #b1010101011))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "5/3 with RNA should round away from zero"
    );
}

// =========================================================================
// fp.sqrt — Non-RNE Rounding Modes
// =========================================================================
// sqrt(5) = 2.2360679... = 1.000111100011... × 2^1 in binary.
// Guard=1, Round=1 → above halfway.
// RNE/RNA/RTP round up (mantissa 0001111001), RTZ/RTN truncate (0001111000).

/// fp.sqrt: sqrt(5.0) with RTZ truncates (differs from RNE).
#[test]
#[timeout(120_000)]
fn test_fp_sqrt_five_rtz() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.sqrt RTZ (fp #b0 #b10001 #b0100000000))
            (fp #b0 #b10000 #b0001111000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "sqrt(5) with RTZ should truncate");
}

/// fp.sqrt: sqrt(5.0) with RTN truncates (toward -inf = truncate for positive).
#[test]
#[timeout(120_000)]
fn test_fp_sqrt_five_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.sqrt RTN (fp #b0 #b10001 #b0100000000))
            (fp #b0 #b10000 #b0001111000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sqrt(5) with RTN should truncate for positive"
    );
}

/// fp.sqrt: sqrt(5.0) with RTP rounds up (positive, above halfway).
#[test]
#[timeout(120_000)]
fn test_fp_sqrt_five_rtp() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.sqrt RTP (fp #b0 #b10001 #b0100000000))
            (fp #b0 #b10000 #b0001111001))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sqrt(5) with RTP should round up for positive"
    );
}

/// fp.sqrt: sqrt(5.0) with RNA rounds away from zero (above halfway).
#[test]
#[timeout(120_000)]
fn test_fp_sqrt_five_rna() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.sqrt RNA (fp #b0 #b10001 #b0100000000))
            (fp #b0 #b10000 #b0001111001))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sqrt(5) with RNA should round away from zero"
    );
}

// =========================================================================
// fp.fma — Non-RNE Rounding Modes
// =========================================================================
// fma(1+2^-10, 1+2^-10, 0) = (1+2^-10)^2 = 1 + 2^-9 + 2^-20.
// The 2^-20 residual is below Float16 ULP (2^-10) at magnitude ~1.
// Residual is below halfway → truncate for RNE/RNA/RTZ/RTN.
// RTP rounds up for positive; RTN rounds down for negative.

/// fp.fma: fma(1+eps, 1+eps, 0) with RTP rounds up (positive residual).
/// RNE truncates to 1+2^-9; RTP rounds up to 1+2^-9+2^-10.
#[test]
#[timeout(120_000)]
fn test_fp_fma_square_rtp() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTP
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b00000 #b0000000000))
            (fp #b0 #b01111 #b0000000011))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma((1+eps)^2, +0) with RTP should round up"
    );
}

/// fp.fma: fma(1+eps, 1+eps, 0) with RTZ truncates (same as RNE here).
#[test]
#[timeout(120_000)]
fn test_fp_fma_square_rtz() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTZ
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b00000 #b0000000000))
            (fp #b0 #b01111 #b0000000010))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma((1+eps)^2, +0) with RTZ should truncate"
    );
}

/// fp.fma: fma(-(1+eps), 1+eps, 0) with RTN rounds toward -inf (up in magnitude).
/// Result: -(1 + 2^-9 + 2^-20). RTN → -(1+2^-9+2^-10), not -(1+2^-9).
#[test]
#[timeout(120_000)]
fn test_fp_fma_neg_square_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTN
                (fp #b1 #b01111 #b0000000001)
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b00000 #b0000000000))
            (fp #b1 #b01111 #b0000000011))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(-(1+eps)*(1+eps), +0) with RTN should round toward -inf"
    );
}

/// fp.fma: fma(-(1+eps), 1+eps, 0) with RNA truncates (below halfway, same as RNE).
/// RNA only differs from RNE at tie (exactly halfway). Here residual is 2^-20 << 2^-11 halfway.
#[test]
#[timeout(120_000)]
fn test_fp_fma_neg_square_rna() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNA
                (fp #b1 #b01111 #b0000000001)
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b00000 #b0000000000))
            (fp #b1 #b01111 #b0000000010))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(-(1+eps)*(1+eps), +0) with RNA should truncate (below halfway)"
    );
}
