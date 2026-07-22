// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! IEEE 754 rounding mode correctness tests for all 5 modes (#3575).
//!
//! Tests fp.add with concrete Float16 values through the full executor pipeline
//! (parse → Tseitin → FP bit-blasting → SAT → result). Each test constrains
//! inputs to known bit patterns and verifies the rounding mode produces the
//! IEEE 754-specified result.
//!
//! Float16 (5 exponent bits, 11 significand bits, bias=15):
//!   1.0    = (fp #b0 #b01111 #b0000000000)  exp=15 → real_exp=0
//!   2^{-11} = (fp #b0 #b00100 #b0000000000)  exp=4  → real_exp=-11
//!
//! The sum 1.0 + 2^{-11} = 1.00048828125, which is exactly halfway between
//! the two adjacent Float16 values:
//!   1.0         = (fp #b0 #b01111 #b0000000000)
//!   1.0 + eps   = (fp #b0 #b01111 #b0000000001)   where eps = 2^{-10}
//!
//! Rounding mode behavior for positive 1.0 + 2^{-11} (exact tie):
//!   RNE → 1.0       (tie, last bit = 0 → even → round down)
//!   RNA → 1.0 + eps  (tie → round away from zero)
//!   RTP → 1.0 + eps  (positive → round toward +inf = round up)
//!   RTN → 1.0       (positive → round toward -inf = truncate)
//!   RTZ → 1.0       (positive → round toward zero = truncate)
//!
//! For negative (-1.0) + (-2^{-11}):
//!   RNE → -1.0      (tie, last bit = 0 → even → round down magnitude)
//!   RNA → -(1.0+eps) (tie → round away from zero)
//!   RTP → -1.0      (negative → round toward +inf = toward zero)
//!   RTN → -(1.0+eps) (negative → round toward -inf = away from zero)
//!   RTZ → -1.0      (negative → round toward zero = truncate magnitude)

use ntest::timeout;

// Float16 bit patterns for constants used in tests.
const ONE: &str = "(fp #b0 #b01111 #b0000000000)"; // 1.0
const NEG_ONE: &str = "(fp #b1 #b01111 #b0000000000)"; // -1.0
const TWO_NEG11: &str = "(fp #b0 #b00100 #b0000000000)"; // 2^{-11}
const NEG_TWO_NEG11: &str = "(fp #b1 #b00100 #b0000000000)"; // -2^{-11}
const ONE_PLUS_EPS: &str = "(fp #b0 #b01111 #b0000000001)"; // 1.0 + 2^{-10}
const NEG_ONE_PLUS_EPS: &str = "(fp #b1 #b01111 #b0000000001)"; // -(1.0 + 2^{-10})
                                                                // Above-halfway addend: 3*2^{-12} = 1.5 * 2^{-11}
                                                                // Normalized: 1.1_2 * 2^{-11}, biased exp = 4, stored sig MSB = 1 → 1000000000
const THREE_TWO_NEG12: &str = "(fp #b0 #b00100 #b1000000000)"; // 3 * 2^{-12}

// =========================================================================
// Positive tie: 1.0 + 2^{-11} (exactly halfway)
// =========================================================================

/// Generate SMT-LIB for: fp.add(rm, 1.0, 2^{-11}) == expected
fn make_add_tie_positive(rm: &str, expected: &str) -> String {
    format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x {ONE}))
        (assert (= y {TWO_NEG11}))
        (assert (= z (fp.add {rm} x y)))
        (assert (fp.eq z {expected}))
        (check-sat)
    "#
    )
}

/// Generate SMT-LIB for: fp.add(rm, 1.0, 2^{-11}) != excluded
fn make_add_tie_positive_neq(rm: &str, excluded: &str) -> String {
    format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x {ONE}))
        (assert (= y {TWO_NEG11}))
        (assert (= z (fp.add {rm} x y)))
        (assert (not (fp.eq z {excluded})))
        (check-sat)
    "#
    )
}

// ---- RNE: tie with even last bit → round down ----

#[test]
#[timeout(120_000)]
fn test_fp16_rne_positive_tie_equals_one() {
    let smt = make_add_tie_positive("RNE", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE: 1.0 + 2^-11 should equal 1.0 (tie, round to even)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rne_positive_tie_not_one_plus_eps() {
    let smt = make_add_tie_positive_neq("RNE", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE: 1.0 + 2^-11 should NOT equal 1.0+eps"
    );
}

// ---- RNA: tie → round away from zero ----

#[test]
#[timeout(120_000)]
fn test_fp16_rna_positive_tie_equals_one_plus_eps() {
    let smt = make_add_tie_positive("RNA", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA: 1.0 + 2^-11 should equal 1.0+eps (tie, round away from zero)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rna_positive_tie_not_one() {
    let smt = make_add_tie_positive_neq("RNA", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA: 1.0 + 2^-11 should NOT equal 1.0"
    );
}

// ---- RTP: positive → round toward +inf ----

#[test]
#[timeout(120_000)]
fn test_fp16_rtp_positive_tie_equals_one_plus_eps() {
    let smt = make_add_tie_positive("RTP", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP: 1.0 + 2^-11 should equal 1.0+eps (positive, round toward +inf)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtp_positive_tie_not_one() {
    let smt = make_add_tie_positive_neq("RTP", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP: 1.0 + 2^-11 should NOT equal 1.0"
    );
}

// ---- RTN: positive → round toward -inf = truncate ----

#[test]
#[timeout(120_000)]
fn test_fp16_rtn_positive_tie_equals_one() {
    let smt = make_add_tie_positive("RTN", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN: 1.0 + 2^-11 should equal 1.0 (positive, round toward -inf = truncate)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtn_positive_tie_not_one_plus_eps() {
    let smt = make_add_tie_positive_neq("RTN", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN: 1.0 + 2^-11 should NOT equal 1.0+eps"
    );
}

// ---- RTZ: positive → round toward zero = truncate ----

#[test]
#[timeout(120_000)]
fn test_fp16_rtz_positive_tie_equals_one() {
    let smt = make_add_tie_positive("RTZ", ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ: 1.0 + 2^-11 should equal 1.0 (positive, round toward zero = truncate)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtz_positive_tie_not_one_plus_eps() {
    let smt = make_add_tie_positive_neq("RTZ", ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ: 1.0 + 2^-11 should NOT equal 1.0+eps"
    );
}

// =========================================================================
// Negative tie: (-1.0) + (-2^{-11}) (exactly halfway, negative)
// =========================================================================

fn make_add_tie_negative(rm: &str, expected: &str) -> String {
    format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x {NEG_ONE}))
        (assert (= y {NEG_TWO_NEG11}))
        (assert (= z (fp.add {rm} x y)))
        (assert (fp.eq z {expected}))
        (check-sat)
    "#
    )
}

fn make_add_tie_negative_neq(rm: &str, excluded: &str) -> String {
    format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x {NEG_ONE}))
        (assert (= y {NEG_TWO_NEG11}))
        (assert (= z (fp.add {rm} x y)))
        (assert (not (fp.eq z {excluded})))
        (check-sat)
    "#
    )
}

// ---- RNE (negative): tie with even last bit → round down magnitude ----

#[test]
#[timeout(120_000)]
fn test_fp16_rne_negative_tie_equals_neg_one() {
    let smt = make_add_tie_negative("RNE", NEG_ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE neg: (-1.0) + (-2^-11) should equal -1.0 (tie, round to even)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rne_negative_tie_not_neg_one_plus_eps() {
    let smt = make_add_tie_negative_neq("RNE", NEG_ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNE neg: (-1.0) + (-2^-11) should NOT equal -(1.0+eps)"
    );
}

// ---- RNA (negative): tie → round away from zero ----

#[test]
#[timeout(120_000)]
fn test_fp16_rna_negative_tie_equals_neg_one_plus_eps() {
    let smt = make_add_tie_negative("RNA", NEG_ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA neg: (-1.0) + (-2^-11) should equal -(1.0+eps) (tie, round away from zero)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rna_negative_tie_not_neg_one() {
    let smt = make_add_tie_negative_neq("RNA", NEG_ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RNA neg: (-1.0) + (-2^-11) should NOT equal -1.0"
    );
}

// ---- RTP (negative): round toward +inf = toward zero for negative ----

#[test]
#[timeout(120_000)]
fn test_fp16_rtp_negative_tie_equals_neg_one() {
    let smt = make_add_tie_negative("RTP", NEG_ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP neg: (-1.0) + (-2^-11) should equal -1.0 (negative, round toward +inf = toward zero)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtp_negative_tie_not_neg_one_plus_eps() {
    let smt = make_add_tie_negative_neq("RTP", NEG_ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTP neg: (-1.0) + (-2^-11) should NOT equal -(1.0+eps)"
    );
}

// ---- RTN (negative): round toward -inf = away from zero for negative ----

#[test]
#[timeout(120_000)]
fn test_fp16_rtn_negative_tie_equals_neg_one_plus_eps() {
    let smt = make_add_tie_negative("RTN", NEG_ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN neg: (-1.0) + (-2^-11) should equal -(1.0+eps) (negative, round toward -inf = away from zero)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtn_negative_tie_not_neg_one() {
    let smt = make_add_tie_negative_neq("RTN", NEG_ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTN neg: (-1.0) + (-2^-11) should NOT equal -1.0"
    );
}

// ---- RTZ (negative): round toward zero = truncate magnitude ----

#[test]
#[timeout(120_000)]
fn test_fp16_rtz_negative_tie_equals_neg_one() {
    let smt = make_add_tie_negative("RTZ", NEG_ONE);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ neg: (-1.0) + (-2^-11) should equal -1.0 (negative, round toward zero = truncate)"
    );
}

#[test]
#[timeout(120_000)]
fn test_fp16_rtz_negative_tie_not_neg_one_plus_eps() {
    let smt = make_add_tie_negative_neq("RTZ", NEG_ONE_PLUS_EPS);
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "RTZ neg: (-1.0) + (-2^-11) should NOT equal -(1.0+eps)"
    );
}

// =========================================================================
// Above halfway: 1.0 + 3*2^{-12} (above halfway, positive)
//
// 3*2^{-12} = 1.5 * 2^{-11}, which is above the halfway point (2^{-11}).
// All modes that round up for positive above-halfway should give 1.0+eps.
// RTZ and RTN (which truncate for positive) should give 1.0.
// =========================================================================

fn make_add_above_halfway(rm: &str, expected: &str) -> String {
    format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x {ONE}))
        (assert (= y {THREE_TWO_NEG12}))
        (assert (= z (fp.add {rm} x y)))
        (assert (fp.eq z {expected}))
        (check-sat)
    "#
    )
}

fn make_add_above_halfway_neq(rm: &str, excluded: &str) -> String {
    format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const y (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= x {ONE}))
        (assert (= y {THREE_TWO_NEG12}))
        (assert (= z (fp.add {rm} x y)))
        (assert (not (fp.eq z {excluded})))
        (check-sat)
    "#
    )
}

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
