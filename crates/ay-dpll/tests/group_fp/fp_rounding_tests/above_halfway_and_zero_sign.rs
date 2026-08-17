// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp_rounding_tests` to preserve test FQNs.

/// RNE: above halfway → round up
#[test]
#[timeout(120_000)]
fn test_fp16_rne_above_halfway_rounds_up() {
    let smt = make_add_above_halfway("RNE", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE: 1.0 + 3*2^-12 (above halfway) should round up to 1.0+eps"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rne_above_halfway_not_one() {
    let smt = make_add_above_halfway_neq("RNE", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE: 1.0 + 3*2^-12 (above halfway) should NOT equal 1.0"
    );
}

/// RNA: above halfway → round up
#[test]
#[timeout(120_000)]
fn test_fp16_rna_above_halfway_rounds_up() {
    let smt = make_add_above_halfway("RNA", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA: 1.0 + 3*2^-12 (above halfway) should round up to 1.0+eps"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rna_above_halfway_not_one() {
    let smt = make_add_above_halfway_neq("RNA", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA: 1.0 + 3*2^-12 (above halfway) should NOT equal 1.0"
    );
}

/// RTP: above halfway, positive → round up
#[test]
#[timeout(120_000)]
fn test_fp16_rtp_above_halfway_rounds_up() {
    let smt = make_add_above_halfway("RTP", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP: 1.0 + 3*2^-12 (positive, above halfway) should round up to 1.0+eps"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtp_above_halfway_not_one() {
    let smt = make_add_above_halfway_neq("RTP", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP: 1.0 + 3*2^-12 (positive, above halfway) should NOT equal 1.0"
    );
}

/// RTN: above halfway, positive → truncate (round toward -inf)
#[test]
#[timeout(120_000)]
fn test_fp16_rtn_above_halfway_truncates() {
    let smt = make_add_above_halfway("RTN", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN: 1.0 + 3*2^-12 (positive) should truncate to 1.0 (round toward -inf)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtn_above_halfway_not_one_plus_eps() {
    let smt = make_add_above_halfway_neq("RTN", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN: 1.0 + 3*2^-12 (positive) should NOT equal 1.0+eps"
    );
}

/// RTZ: above halfway, positive → truncate (round toward zero)
#[test]
#[timeout(120_000)]
fn test_fp16_rtz_above_halfway_truncates() {
    let smt = make_add_above_halfway("RTZ", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ: 1.0 + 3*2^-12 (positive) should truncate to 1.0 (round toward zero)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtz_above_halfway_not_one_plus_eps() {
    let smt = make_add_above_halfway_neq("RTZ", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ: 1.0 + 3*2^-12 (positive) should NOT equal 1.0+eps"
    );
}

// =========================================================================
// Zero sign tests: (+0) + (-0) sign depends on rounding mode
//
// IEEE 754-2008 Section 6.3: (+0) + (-0) = +0 in all modes except RTN.
// RTN: (+0) + (-0) = -0.
// =========================================================================

/// RNE: (+0) + (-0) = +0
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rne_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.isPositive z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE: (+0) + (-0) should be positive zero"
    );
}

/// RTN: (+0) + (-0) = -0
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rtn_negative() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RTN x y)))
        (assert (fp.isNegative z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN: (+0) + (-0) should be negative zero"
    );
}

/// RNA: (+0) + (-0) = +0
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rna_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RNA x y)))
        (assert (fp.isPositive z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA: (+0) + (-0) should be positive zero"
    );
}

/// RTP: (+0) + (-0) = +0
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rtp_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RTP x y)))
        (assert (fp.isPositive z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP: (+0) + (-0) should be positive zero"
    );
}

/// RTZ: (+0) + (-0) = +0
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rtz_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RTZ x y)))
        (assert (fp.isPositive z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ: (+0) + (-0) should be positive zero"
    );
}

// ---- Zero sign exclusion tests: verify wrong sign is impossible ----

/// RNE: (+0) + (-0) is NOT negative zero
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rne_not_negative() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RNE x y)))
        (assert (fp.isNegative z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "RNE: (+0) + (-0) must NOT be negative zero"
    );
}

/// RTN: (+0) + (-0) is NOT positive zero
#[test]
#[timeout(120_000)]
fn test_fp16_zero_sign_rtn_not_positive() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x (_ +zero 5 11)))
        (assert (= y (_ -zero 5 11)))
        (assert (= z (fp.add RTN x y)))
        (assert (fp.isPositive z))
        (assert (fp.isZero z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "RTN: (+0) + (-0) must NOT be positive zero"
    );
}
