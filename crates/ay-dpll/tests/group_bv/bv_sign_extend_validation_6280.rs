// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for BV sign_extend model validation (#6280).
//!
//! AY produced a wrong `sat` answer on `bin_eventlogadm_vc331086.smt2`
//! (a QF_BV benchmark with sign_extend) when run at the competition
//! timeout (1200s), but not at 60s. The root cause: after a long
//! search, the model evaluator returned `Unknown` for a pure-BV
//! assertion containing sign_extend, and the validator accepted the
//! SAT assignment through a fallback path.
//!
//! The validation gate (#6280) now degrades pure-BV Unknown to
//! SolveResult::Unknown instead of trusting SAT-truth.
//!
//! These tests verify sign_extend correctness end-to-end through the
//! full BV pipeline: parsing → bit-blasting → SAT → model extraction
//! → model validation.

use ntest::timeout;

/// Basic sign_extend by 0 is identity.
#[test]
#[timeout(60_000)]
fn test_sign_extend_zero_identity_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (not (= ((_ sign_extend 0) x) x)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend by 0 should be identity"
    );
}

/// sign_extend of a positive constant: high bits should be 0.
#[test]
#[timeout(60_000)]
fn test_sign_extend_positive_constant_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= x #x7F))
        ; sign_extend 8 of 0x7F should be 0x007F (sign bit is 0)
        (assert (not (= ((_ sign_extend 8) x) #x007F)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend of positive should zero-extend"
    );
}

/// sign_extend of a negative constant: high bits should be 1.
#[test]
#[timeout(60_000)]
fn test_sign_extend_negative_constant_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= x #x80))
        ; sign_extend 8 of 0x80 should be 0xFF80 (sign bit is 1)
        (assert (not (= ((_ sign_extend 8) x) #xFF80)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend of negative should sign-extend"
    );
}

/// sign_extend preserves bvslt ordering: if x <s 0, then sign_extend(x) <s 0.
#[test]
#[timeout(60_000)]
fn test_sign_extend_preserves_signed_order_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        ; If x is negative (sign bit = 1)
        (assert (bvslt x #x00))
        ; Then sign_extend(x) should also be negative
        (assert (not (bvslt ((_ sign_extend 8) x) #x0000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend should preserve signed negativity"
    );
}

/// sign_extend combined with arithmetic: the sign-extended value should
/// equal the original value when both are treated as signed integers.
#[test]
#[timeout(60_000)]
fn test_sign_extend_signed_value_equality_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 16))
        (assert (= y ((_ sign_extend 8) x)))
        ; If x = -1 (0xFF), then y should be -1 (0xFFFF)
        (assert (= x #xFF))
        (assert (not (= y #xFFFF)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend of -1 (8-bit) should be -1 (16-bit)"
    );
}

/// SAT case: sign_extend with satisfiable constraints.
#[test]
#[timeout(60_000)]
fn test_sign_extend_sat_with_constraints_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 16))
        (assert (= y ((_ sign_extend 8) x)))
        ; x is positive and > 10
        (assert (bvsgt x #x0A))
        (assert (bvslt x #x7F))
        ; y should also be positive (same value, zero-extended high bits)
        (assert (bvsgt y #x000A))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Nested sign_extend: sign_extend(sign_extend(x)) should equal
/// a single sign_extend of the total width.
#[test]
#[timeout(60_000)]
fn test_sign_extend_nested_equivalence_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        ; sign_extend 4 then sign_extend 8 = sign_extend 12
        (assert (not (= ((_ sign_extend 8) ((_ sign_extend 4) x))
                        ((_ sign_extend 12) x))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "nested sign_extend should compose");
}

/// sign_extend with extract: extracting the original bits from a
/// sign-extended value should yield the original value.
#[test]
#[timeout(60_000)]
fn test_sign_extend_extract_roundtrip_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        ; Extract low 8 bits of sign_extend should give back x
        (assert (not (= ((_ extract 7 0) ((_ sign_extend 8) x)) x)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "extract low bits of sign_extend should round-trip"
    );
}

/// Model validation contract: ay must never return `sat` when the
/// answer should be `unsat`. For sign_extend, this tests the full
/// pipeline from bit-blasting through model validation.
#[test]
#[timeout(60_000)]
fn test_sign_extend_never_false_sat_6280() {
    // This benchmark is crafted to be UNSAT but requires correct
    // sign_extend semantics. If the bit-blaster or model validator
    // has a sign_extend bug, this could incorrectly return sat.
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        ; a is positive, b is negative
        (assert (bvsgt a #x00))
        (assert (bvslt b #x00))
        ; After sign extension, a and b should differ
        ; (a is positive → high byte 0x00, b is negative → high byte 0xFF)
        (assert (= ((_ sign_extend 8) a) ((_ sign_extend 8) b)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend of positive and negative must differ"
    );
}

/// Wide sign_extend test: 32→64 bit, matching the kind of widths
/// seen in the original bin_eventlogadm_vc331086.smt2 benchmark.
#[test]
#[timeout(60_000)]
fn test_sign_extend_wide_32_to_64_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 32))
        (declare-fun y () (_ BitVec 64))
        (assert (= y ((_ sign_extend 32) x)))
        ; x = 0xFFFFFFFF (-1 as signed 32-bit)
        (assert (= x #xFFFFFFFF))
        ; y should be 0xFFFFFFFFFFFFFFFF (-1 as signed 64-bit)
        (assert (not (= y #xFFFFFFFFFFFFFFFF)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "32→64 sign_extend of -1 should be -1"
    );
}

/// sign_extend combined with bvadd: the extended value should support
/// correct signed arithmetic at the wider width.
#[test]
#[timeout(60_000)]
fn test_sign_extend_with_arithmetic_6280() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        ; x = 5, y = -3
        (assert (= x #x05))
        (assert (= y #xFD))
        ; sign_extend both to 16 bits, add them: should be 2 (0x0002)
        (assert (not (= (bvadd ((_ sign_extend 8) x) ((_ sign_extend 8) y))
                        #x0002)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "sign_extend + bvadd should compute correctly"
    );
}
