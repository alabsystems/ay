// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for FP/BV bridge operations (#8332).
//!
//! Covers: try_fp_to_bv, try_bv_to_fp_reinterpret, try_fp_classify,
//! roundtrip fp->bv->fp, NaN detection, infinity detection, classification.

use crate::api::*;
use num_bigint::BigInt;

// --- try_fp_to_bv ---

#[test]
fn test_fp_to_bv_float32_produces_bv32() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let bv = solver.try_fp_to_bv(x).unwrap();
    assert_eq!(
        solver.term_sort(bv),
        Sort::bitvec(32),
        "fp_to_bv(Float32) should produce BV32"
    );
}

#[test]
fn test_fp_to_bv_float64_produces_bv64() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));
    let bv = solver.try_fp_to_bv(x).unwrap();
    assert_eq!(
        solver.term_sort(bv),
        Sort::bitvec(64),
        "fp_to_bv(Float64) should produce BV64"
    );
}

#[test]
fn test_fp_to_bv_rejects_non_fp() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(32));
    let result = solver.try_fp_to_bv(bv);
    assert!(
        matches!(result, Err(SolverError::SortMismatch { .. })),
        "fp_to_bv should reject non-FP sort"
    );
}

// --- try_bv_to_fp_reinterpret ---

#[test]
fn test_bv_to_fp_reinterpret_bv32_to_float32() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(32));
    let fp = solver.try_bv_to_fp_reinterpret(bv, 8, 24).unwrap();
    assert_eq!(
        solver.term_sort(fp),
        Sort::FloatingPoint(8, 24),
        "bv_to_fp_reinterpret(BV32, 8, 24) should produce Float32"
    );
}

#[test]
fn test_bv_to_fp_reinterpret_bv64_to_float64() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(64));
    let fp = solver.try_bv_to_fp_reinterpret(bv, 11, 53).unwrap();
    assert_eq!(
        solver.term_sort(fp),
        Sort::FloatingPoint(11, 53),
        "bv_to_fp_reinterpret(BV64, 11, 53) should produce Float64"
    );
}

#[test]
fn test_bv_to_fp_reinterpret_rejects_width_mismatch() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(16));
    let result = solver.try_bv_to_fp_reinterpret(bv, 8, 24);
    assert!(
        matches!(result, Err(SolverError::InvalidArgument { .. })),
        "bv_to_fp_reinterpret should reject width mismatch: got {result:?}"
    );
}

#[test]
fn test_bv_to_fp_reinterpret_rejects_zero_precision() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(32));
    let result = solver.try_bv_to_fp_reinterpret(bv, 0, 32);
    assert!(
        matches!(result, Err(SolverError::InvalidArgument { .. })),
        "bv_to_fp_reinterpret should reject zero exponent width: {result:?}"
    );
}

#[test]
fn test_bv_to_fp_reinterpret_rejects_precision_width_overflow() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(1));
    let result = solver.try_bv_to_fp_reinterpret(bv, u32::MAX, 1);
    assert!(
        matches!(result, Err(SolverError::InvalidArgument { .. })),
        "bv_to_fp_reinterpret should reject overflowing eb+sb: {result:?}"
    );
}

#[test]
fn test_bv_to_fp_reinterpret_rejects_non_bv() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let fp = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let result = solver.try_bv_to_fp_reinterpret(fp, 8, 24);
    assert!(
        matches!(result, Err(SolverError::SortMismatch { .. })),
        "bv_to_fp_reinterpret should reject non-BV sort"
    );
}

#[test]
fn test_fp_to_ieee_bv_rejects_malformed_declared_precision() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let fp = solver.declare_const("x", Sort::FloatingPoint(u32::MAX, 1));
    let result = solver.try_fp_to_ieee_bv(fp);
    assert!(
        matches!(result, Err(SolverError::InvalidArgument { .. })),
        "fp.to_ieee_bv should reject overflowing eb+sb: {result:?}"
    );
}

#[test]
fn test_fp_from_bvs_rejects_mismatched_component_widths() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let sign = solver.declare_const("sign", Sort::bitvec(2));
    let exp = solver.declare_const("exp", Sort::bitvec(8));
    let sig = solver.declare_const("sig", Sort::bitvec(23));
    let result = solver.try_fp_from_bvs(sign, exp, sig, 8, 24);
    assert!(
        matches!(result, Err(SolverError::InvalidArgument { .. })),
        "fp sign/exponent/significand constructor should reject component width mismatch: {result:?}"
    );
}

#[test]
fn test_fp_special_constants_reject_zero_precision() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    for result in [
        solver.try_fp_plus_infinity(0, 24),
        solver.try_fp_minus_infinity(8, 0),
        solver.try_fp_nan(0, 24),
        solver.try_fp_plus_zero(8, 0),
        solver.try_fp_minus_zero(0, 24),
    ] {
        assert!(
            matches!(result, Err(SolverError::InvalidArgument { .. })),
            "FP special constants should reject zero precision: {result:?}"
        );
    }
}

#[test]
fn test_fp_builders_reject_unrepresentable_or_unbounded_precision() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    for result in [
        solver.try_fp_plus_infinity(32, 24),
        solver.try_fp_nan(8, (1 << 20) + 1),
    ] {
        assert!(matches!(result, Err(SolverError::InvalidArgument { .. })));
    }

    let malformed = solver.declare_const("bad", Sort::FloatingPoint(32, 24));
    assert!(matches!(
        solver.try_fp_to_ieee_bv(malformed),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert!(matches!(
        solver.try_fp_const_from_bits_bigint(&BigInt::from(0u8), u32::MAX - 1, 1),
        Err(SolverError::InvalidArgument { .. })
    ));
}

// --- try_fp_classify ---

#[test]
fn test_fp_classify_returns_bv3() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let cls = solver.try_fp_classify(x).unwrap();
    assert_eq!(
        solver.term_sort(cls),
        Sort::bitvec(3),
        "fp_classify should return BV3"
    );
}

#[test]
fn test_fp_classify_rejects_non_fp() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let bv = solver.declare_const("x", Sort::bitvec(32));
    let result = solver.try_fp_classify(bv);
    assert!(
        matches!(result, Err(SolverError::SortMismatch { .. })),
        "fp_classify should reject non-FP sort"
    );
}

#[test]
fn test_fp_classify_nan_returns_4() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let nan = solver.fp_nan(8, 24);
    let cls = solver.try_fp_classify(nan).unwrap();
    let nan_bv = solver.try_bv_const(fp_class::NAN, 3).unwrap();
    let eq = solver.try_eq(cls, nan_bv).unwrap();
    solver.try_assert_term(eq).unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "NaN should be classified as NAN (4)"
    );
}

#[test]
fn test_fp_classify_infinity_returns_3() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let pinf = solver.fp_plus_infinity(8, 24);
    let cls = solver.try_fp_classify(pinf).unwrap();
    let inf_bv = solver.try_bv_const(fp_class::INFINITY, 3).unwrap();
    let eq = solver.try_eq(cls, inf_bv).unwrap();
    solver.try_assert_term(eq).unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "+infinity should be classified as INFINITY (3)"
    );
}

#[test]
fn test_fp_classify_zero_returns_2() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let pzero = solver.fp_plus_zero(8, 24);
    let cls = solver.try_fp_classify(pzero).unwrap();
    let zero_bv = solver.try_bv_const(fp_class::ZERO, 3).unwrap();
    let eq = solver.try_eq(cls, zero_bv).unwrap();
    solver.try_assert_term(eq).unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "+zero should be classified as ZERO (2)"
    );
}

// --- Roundtrip: fp -> bv -> fp ---

#[test]
fn test_roundtrip_fp_to_bv_to_fp_nan_stays_nan() {
    // NaN -> BV -> FP should produce a NaN (NaN != NaN per IEEE 754)
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let nan = solver.fp_nan(8, 24);
    let bv = solver.try_fp_to_bv(nan).unwrap();
    let fp_back = solver.try_bv_to_fp_reinterpret(bv, 8, 24).unwrap();
    let is_nan_back = solver.try_fp_is_nan(fp_back).unwrap();
    solver.try_assert_term(is_nan_back).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "NaN roundtripped through BV should be SAT or Unknown, got {result:?}"
    );
}

#[test]
fn test_roundtrip_fp_to_bv_to_fp_infinity_stays_infinite() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let pinf = solver.fp_plus_infinity(8, 24);
    let bv = solver.try_fp_to_bv(pinf).unwrap();
    let fp_back = solver.try_bv_to_fp_reinterpret(bv, 8, 24).unwrap();
    let is_inf_back = solver.try_fp_is_infinite(fp_back).unwrap();
    solver.try_assert_term(is_inf_back).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "+infinity roundtripped through BV should be SAT or Unknown, got {result:?}"
    );
}

#[test]
fn test_roundtrip_fp_to_bv_to_fp_zero_stays_zero() {
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let pzero = solver.fp_plus_zero(8, 24);
    let bv = solver.try_fp_to_bv(pzero).unwrap();
    let fp_back = solver.try_bv_to_fp_reinterpret(bv, 8, 24).unwrap();
    let is_zero_back = solver.try_fp_is_zero(fp_back).unwrap();
    solver.try_assert_term(is_zero_back).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "+zero roundtripped through BV should be SAT or Unknown, got {result:?}"
    );
}

// --- NaN and Infinity detection via BV patterns ---

#[test]
fn test_bv_nan_pattern_detected_as_nan() {
    // Float32 NaN: exponent all 1s (0xFF), significand non-zero
    // Canonical NaN: 0x7FC00000 = sign=0, exp=0xFF, sig=0x400000
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let nan_bits = solver.try_bv_const(0x7FC0_0000, 32).unwrap();
    let fp = solver.try_bv_to_fp_reinterpret(nan_bits, 8, 24).unwrap();
    let is_nan = solver.try_fp_is_nan(fp).unwrap();
    solver.try_assert_term(is_nan).unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "BV pattern 0x7FC00000 should be NaN"
    );
}

#[test]
fn test_bv_infinity_pattern_detected_as_infinite() {
    // Float32 +inf: 0x7F800000 = sign=0, exp=0xFF, sig=0x000000
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let inf_bits = solver.try_bv_const(0x7F80_0000, 32).unwrap();
    let fp = solver.try_bv_to_fp_reinterpret(inf_bits, 8, 24).unwrap();
    let is_inf = solver.try_fp_is_infinite(fp).unwrap();
    solver.try_assert_term(is_inf).unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "BV pattern 0x7F800000 should be +infinity"
    );
}

#[test]
fn test_bv_negative_zero_pattern_detected() {
    // Float32 -0: 0x80000000 = sign=1, exp=0x00, sig=0x000000
    let mut solver = Solver::try_new(Logic::QfBvfp).unwrap();
    let nzero_bits = solver
        .try_bv_const(i64::from(0x8000_0000u32 as i32), 32)
        .unwrap();
    let fp = solver.try_bv_to_fp_reinterpret(nzero_bits, 8, 24).unwrap();
    let is_zero = solver.try_fp_is_zero(fp).unwrap();
    let is_neg = solver.try_fp_is_negative(fp).unwrap();
    let both = solver.and(is_zero, is_neg);
    solver.try_assert_term(both).unwrap();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "BV pattern 0x80000000 should be negative zero"
    );
}
