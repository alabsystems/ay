// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp_round_integral` to preserve test FQNs.

// ========== RTN (Round Toward Negative infinity) for values > 1 ==========

/// roundToIntegral(RTN, 2.5) = 2.0 (floor)
#[test]
#[timeout(60_000)]
fn test_round_integral_rtn_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTN (fp #b0 #b10000 #b0100000000))
            (fp #b0 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTN, 2.5) should be 2.0"
    );
}

/// roundToIntegral(RTN, -2.5) = -3.0 (toward -inf)
#[test]
#[timeout(60_000)]
fn test_round_integral_rtn_neg_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTN (fp #b1 #b10000 #b0100000000))
            (fp #b1 #b10000 #b1000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTN, -2.5) should be -3.0"
    );
}

// ========== RTZ (Round Toward Zero) for values > 1 ==========

/// roundToIntegral(RTZ, 2.5) = 2.0 (truncate toward zero)
#[test]
#[timeout(60_000)]
fn test_round_integral_rtz_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTZ (fp #b0 #b10000 #b0100000000))
            (fp #b0 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTZ, 2.5) should be 2.0"
    );
}

/// roundToIntegral(RTZ, -2.5) = -2.0 (truncate toward zero)
#[test]
#[timeout(60_000)]
fn test_round_integral_rtz_neg_2_5() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RTZ (fp #b1 #b10000 #b0100000000))
            (fp #b1 #b10000 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RTZ, -2.5) should be -2.0"
    );
}

// ========== Already-integral boundary ==========

/// roundToIntegral(RNE, 1024.0) = 1024.0 (already integral, exp=10 ≥ sb-1=10)
/// Float16: 1024.0 = 1.0 × 2^10 → exp=25=11001, sig=0000000000
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_already_integral_1024() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b11001 #b0000000000))
            (fp #b0 #b11001 #b0000000000))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 1024.0) should be 1024.0"
    );
}

/// roundToIntegral(RNE, 1025.0) = 1025.0 (already integral)
/// Float16: 1025.0 = 1.0000000001 × 2^10 → exp=25=11001, sig=0000000001
#[test]
#[timeout(60_000)]
fn test_round_integral_rne_already_integral_1025() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.roundToIntegral RNE (fp #b0 #b11001 #b0000000001))
            (fp #b0 #b11001 #b0000000001))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "roundToIntegral(RNE, 1025.0) should be 1025.0"
    );
}
