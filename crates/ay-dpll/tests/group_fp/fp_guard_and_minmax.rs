// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! FP guard regression tests and fp.min/fp.max integration tests (#3586).
//!
//! Split from fp_integration.rs when it exceeded 1000-line limit.
//! - Guard tests: verify unsupported ops return Unknown (not false SAT/UNSAT)
//! - Min/max tests: verify the only unguarded arithmetic ops are correct

use ntest::timeout;

// =========================================================================
// FP Conversion Guard Tests
// =========================================================================
//
// Regression tests for the to_fp guard gap (#3586). Previously,
// has_unsupported_fp_arithmetic only checked Symbol::Named, but to_fp and
// to_fp_unsigned are Symbol::Indexed. This caused them to bypass the guard,
// producing false SAT/UNSAT from unconstrained variables.

/// to_fp from a constant real is folded to its IEEE bit pattern, so this is
/// decided correctly: x = 1.0f, y = 2.0f, and `fp.eq 1.0 2.0` is false → UNSAT.
/// Regression: must NOT be a false SAT (it previously bypassed the guard); it is
/// now also no longer `unknown`.
#[test]
#[timeout(30_000)]
fn test_fp_to_fp_real_constants_distinct_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x ((_ to_fp 8 24) RNE 1.0)))
        (assert (= y ((_ to_fp 8 24) RNE 2.0)))
        (assert (fp.eq x y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "1.0f != 2.0f, so fp.eq must be unsat (not a false SAT, not unknown)"
    );
}

/// to_fp_unsigned from variable BV: unsigned 1 converts to 1.0f, not NaN.
#[test]
#[timeout(30_000)]
fn test_fp_to_fp_unsigned_variable_bv_not_nan() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const bv (_ BitVec 32))
        (declare-const x (_ FloatingPoint 8 24))
        (assert (= bv #x00000001))
        (assert (= x ((_ to_fp_unsigned 8 24) RNE bv)))
        (assert (fp.isNaN x))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "unsigned BV 1 → 1.0f which is not NaN — must be unsat"
    );
}

/// fp.to_ubv: 1.0f → ubv32 = 1, asserting = 2 is unsat.
#[test]
#[timeout(30_000)]
fn test_fp_to_ubv_unsat() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const bv (_ BitVec 32))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= bv ((_ fp.to_ubv 32) RNE x)))
        (assert (= bv #x00000002))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fp.to_ubv(1.0f) = 1, asserting = 2 is unsat"
    );
}

/// fp.to_sbv: 1.0f → sbv32 = 1, asserting = 2 is unsat.
#[test]
#[timeout(30_000)]
fn test_fp_to_sbv_unsat() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const bv (_ BitVec 32))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= bv ((_ fp.to_sbv 32) RNE x)))
        (assert (= bv #x00000002))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fp.to_sbv(1.0f) = 1, asserting = 2 is unsat"
    );
}

/// fp.div basic: 2.0 / 1.0 = 2.0, so asserting result == 1.0 is UNSAT.
#[test]
#[timeout(30_000)]
fn test_fp_div_basic() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.div RNE x y)))
        (assert (fp.eq z (fp #b0 #b01111111 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "2.0 / 1.0 != 1.0, so fp.eq to 1.0 should be unsat"
    );
}

/// fp.div correctness: 2.0 / 1.0 = 2.0 (SAT case — verifies correct answer).
/// Division bit-blasting creates large CNF (3*sb+2 = 74 bits for Float32).
/// Release-only: debug SAT solver takes >120s on this CNF, blocking the entire
/// ay-dpll test suite (#6244). Release handles it in ~8s.
#[test]
#[cfg(not(debug_assertions))]
#[timeout(120_000)]
fn test_fp_div_two_over_one_sat() {
    // x = 2.0, y = 1.0, z = x/y. Assert z == 2.0. Should be SAT.
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.div RNE x y)))
        (assert (fp.eq z (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "2.0 / 1.0 = 2.0, so fp.eq to 2.0 should be sat"
    );
}

// ========== fp.min / fp.max tests ==========
// These pass the unsupported-operation guard and are bit-blasted.
// fp.min and fp.max are the ONLY arithmetic FP operations not blocked
// by has_unsupported_fp_arithmetic.

/// fp.min of two positive values: min(1.0, 2.0) = 1.0, so min != 2.0 is UNSAT.
#[test]
#[timeout(30_000)]
fn test_fp_min_positive_values() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.min x y)))
        (assert (fp.eq z y))
        (check-sat)
    "#;
    // min(1.0, 2.0) = 1.0, so z = 1.0, and fp.eq z 2.0 should be false.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// fp.min returns the smaller value (SAT case).
#[test]
#[timeout(30_000)]
fn test_fp_min_positive_values_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.min x y)))
        (assert (fp.eq z x))
        (check-sat)
    "#;
    // min(1.0, 2.0) = 1.0, so z = 1.0 = x, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.max of two positive values: max(1.0, 2.0) = 2.0.
#[test]
#[timeout(30_000)]
fn test_fp_max_positive_values() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.max x y)))
        (assert (fp.eq z x))
        (check-sat)
    "#;
    // max(1.0, 2.0) = 2.0, so z = 2.0, and fp.eq z 1.0 should be false.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// fp.max returns the larger value (SAT case).
#[test]
#[timeout(30_000)]
fn test_fp_max_positive_values_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.max x y)))
        (assert (fp.eq z y))
        (check-sat)
    "#;
    // max(1.0, 2.0) = 2.0 = y, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.min with NaN: min(NaN, y) = y per IEEE 754.
#[test]
#[timeout(30_000)]
fn test_fp_min_nan_returns_other() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.min x y)))
        (assert (fp.eq z y))
        (check-sat)
    "#;
    // min(NaN, 2.0) = 2.0, so z = y, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.max with NaN: max(NaN, y) = y per IEEE 754.
#[test]
#[timeout(30_000)]
fn test_fp_max_nan_returns_other() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (fp.isNaN x))
        (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (= z (fp.max x y)))
        (assert (fp.eq z y))
        (check-sat)
    "#;
    // max(NaN, 2.0) = 2.0, so z = y, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.min with negative numbers: min(-2.0, -1.0) = -2.0.
#[test]
#[timeout(30_000)]
fn test_fp_min_negative_values() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b10000000 #b00000000000000000000000)))
        (assert (= y (fp #b1 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.min x y)))
        (assert (fp.eq z x))
        (check-sat)
    "#;
    // -2.0 < -1.0, so min(-2.0, -1.0) = -2.0 = x, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.max with cross-sign: max(-1.0, 1.0) = 1.0.
#[test]
#[timeout(30_000)]
fn test_fp_max_cross_sign() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b1 #b01111111 #b00000000000000000000000)))
        (assert (= y (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= z (fp.max x y)))
        (assert (fp.eq z y))
        (check-sat)
    "#;
    // max(-1.0, 1.0) = 1.0 = y, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.min with NaN as SECOND argument: min(x, NaN) = x per IEEE 754.
/// This tests a different code path than test_fp_min_nan_returns_other (NaN first).
/// Here, make_lt_result(NaN, x) must return false so use_y stays false.
#[test]
#[timeout(30_000)]
fn test_fp_min_second_arg_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.isNaN y))
        (assert (= z (fp.min x y)))
        (assert (fp.eq z x))
        (check-sat)
    "#;
    // min(2.0, NaN) = 2.0 = x, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// fp.max with NaN as SECOND argument: max(x, NaN) = x per IEEE 754.
/// Tests that make_lt_result(x, NaN) returns false so use_y stays false.
#[test]
#[timeout(30_000)]
fn test_fp_max_second_arg_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const z (_ FloatingPoint 8 24))
        (assert (= x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.isNaN y))
        (assert (= z (fp.max x y)))
        (assert (fp.eq z x))
        (check-sat)
    "#;
    // max(2.0, NaN) = 2.0 = x, SAT.
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

// =========================================================================
// Encoding Gap Guard Tests (#3586)
// =========================================================================
//
// When an FP-sorted ITE has a non-FP condition (e.g., a BV comparison) that
// is not in the Tseitin map, the FP solver cannot link the condition to the
// SAT solver's variable. Previously this created a fresh unconstrained
// variable (false-SAT risk). Now it sets an encoding gap flag and returns
// Unknown.

/// FP-sorted ITE with non-FP condition: BV comparison as ITE condition.
/// The BV comparison (bvugt) is not an FP predicate and not in the Tseitin
/// map (only appears inside the FP-sorted ITE, not at the Bool level).
/// The solver cannot link the BV condition to the FP SAT encoding, so it
/// must return Unknown rather than producing a potentially unsound result.
#[test]
#[timeout(30_000)]
fn test_fp_ite_non_fp_condition_returns_unknown() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ BitVec 8))
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (assert (fp.lt (ite (bvugt x #x05) a b) a))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unknown"],
        "non-FP ITE condition not in Tseitin map — must return unknown"
    );
}

// =========================================================================
// FP ITE Encoding Gap Adversarial Tests (P1:127)
// =========================================================================
//
// Verify W1:2014 has_encoding_gap guard with adversarial formulas that
// mix FP ITEs with non-FP conditions (arithmetic, UF, nested).

/// FP ITE with Int arithmetic condition: (> x 0) is not an FP predicate
/// and won't be in the Tseitin map when appearing only inside FP-sorted ITE.
#[test]
#[timeout(30_000)]
fn test_fp_ite_int_condition_returns_unknown() {
    let smt = r#"
        (set-logic QF_FPLRA)
        (declare-const x Int)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (assert (fp.lt (ite (> x 0) a b) a))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unknown"],
        "Int comparison as FP ITE condition — must return unknown"
    );
}

/// FP ITE with Real arithmetic condition.
#[test]
#[timeout(30_000)]
fn test_fp_ite_real_condition_returns_unknown() {
    let smt = r#"
        (set-logic QF_FPLRA)
        (declare-const r Real)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (assert (fp.eq (ite (> r 0.5) a b) b))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unknown"],
        "Real comparison as FP ITE condition — must return unknown"
    );
}

/// FP ITE where the condition IS an FP predicate — this should NOT trigger
/// the encoding gap. FP predicates are handled natively by the FP encoder.
#[test]
#[timeout(30_000)]
fn test_fp_ite_fp_condition_resolves_normally() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (declare-const c (_ FloatingPoint 8 24))
        (assert (fp.eq (ite (fp.lt a b) a c) a))
        (assert (fp.lt a b))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // FP predicate conditions are handled natively — should get sat or unknown
    // but NOT trigger the encoding gap. The key check is no false-unsat.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "FP ITE with FP predicate condition should resolve normally, got: {outputs:?}"
    );
}

/// Two FP ITEs: one with resolvable FP condition, one with non-FP BV condition.
/// The non-FP condition should trigger the encoding gap for the entire formula.
#[test]
#[timeout(30_000)]
fn test_fp_ite_mixed_conditions_one_gap_returns_unknown() {
    let smt = r#"
        (set-logic QF_BVFP)
        (declare-const x (_ BitVec 8))
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (declare-const c (_ FloatingPoint 8 24))
        (assert (fp.lt (ite (fp.lt a b) a c) b))
        (assert (fp.eq (ite (bvugt x #x05) a b) c))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unknown"],
        "Mixed FP/non-FP ITE conditions: any non-FP gap forces unknown"
    );
}

include!("fp_guard_and_minmax/bv_ite_lowering.rs");
