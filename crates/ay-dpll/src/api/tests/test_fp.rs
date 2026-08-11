// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for FP (floating-point) API term construction and sort checking.
//!
//! Covers: fp_add/try_fp_add, fp_sub/try_fp_sub, fp_mul/try_fp_mul,
//! fp_div/try_fp_div, fp_sqrt/try_fp_sqrt, fp_fma/try_fp_fma,
//! fp_rem/try_fp_rem, fp_round_to_integral/try_fp_round_to_integral,
//! fp_abs/try_fp_abs, fp_neg/try_fp_neg, plus error paths.

use crate::api::types::SolverError;
use crate::api::*;
use num_bigint::BigInt;

// --- Positive: term construction produces correct sort ---

#[test]
fn test_fp_add_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let sum = solver.try_fp_add(rm, x, y).unwrap();
    let sort = solver.terms().sort(sum.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_sub_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let diff = solver.try_fp_sub(rm, x, y).unwrap();
    let sort = solver.terms().sort(diff.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_mul_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RTZ").unwrap();
    let prod = solver.try_fp_mul(rm, x, y).unwrap();
    let sort = solver.terms().sort(prod.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_div_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let quot = solver.try_fp_div(rm, x, y).unwrap();
    let sort = solver.terms().sort(quot.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_sqrt_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let root = solver.try_fp_sqrt(rm, x).unwrap();
    let sort = solver.terms().sort(root.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_rem_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let rem = solver.try_fp_rem(x, y).unwrap();
    let sort = solver.terms().sort(rem.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_fma_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let a = solver.declare_const("a", Sort::FloatingPoint(8, 24));
    let b = solver.declare_const("b", Sort::FloatingPoint(8, 24));
    let c = solver.declare_const("c", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let fma = solver.try_fp_fma(rm, a, b, c).unwrap();
    let sort = solver.terms().sort(fma.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_round_to_integral_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RTN").unwrap();
    let rounded = solver.try_fp_round_to_integral(rm, x).unwrap();
    let sort = solver.terms().sort(rounded.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_abs_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let abs = solver.try_fp_abs(x).unwrap();
    let sort = solver.terms().sort(abs.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

#[test]
fn test_fp_neg_produces_fp_term() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let neg = solver.try_fp_neg(x).unwrap();
    let sort = solver.terms().sort(neg.id()).clone();
    assert_eq!(sort, Sort::FloatingPoint(8, 24));
}

// --- Error paths: sort mismatch on wrong argument types ---

#[test]
fn test_try_fp_add_rejects_int_operands() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let err = solver.try_fp_add(rm, x, y).unwrap_err();
    assert!(
        matches!(
            err,
            SolverError::SortMismatch {
                operation: "fp.add",
                ..
            }
        ),
        "expected SortMismatch for fp.add with Int operand, got: {err}"
    );
}

#[test]
fn test_try_fp_add_rejects_mismatched_fp_precisions() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(11, 53));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let err = solver.try_fp_add(rm, x, y).unwrap_err();
    assert!(
        matches!(
            err,
            SolverError::SortMismatch {
                operation: "fp.add",
                ..
            }
        ),
        "expected SortMismatch for fp.add with different FP precisions, got: {err}"
    );
}

#[test]
fn test_try_fp_abs_rejects_bool() {
    let mut solver = Solver::new(Logic::QfFp);
    let b = solver.declare_const("b", Sort::Bool);
    let err = solver.try_fp_abs(b).unwrap_err();
    assert!(
        matches!(
            err,
            SolverError::SortMismatch {
                operation: "fp.abs",
                ..
            }
        ),
        "expected SortMismatch for fp.abs with Bool, got: {err}"
    );
}

#[test]
fn test_try_fp_rem_rejects_bv_operands() {
    let mut solver = Solver::new(Logic::QfFp);
    let bv_sort = Sort::BitVec(BitVecSort { width: 32 });
    let x = solver.declare_const("x", bv_sort.clone());
    let y = solver.declare_const("y", bv_sort);
    let err = solver.try_fp_rem(x, y).unwrap_err();
    assert!(
        matches!(
            err,
            SolverError::SortMismatch {
                operation: "fp.rem",
                ..
            }
        ),
        "expected SortMismatch for fp.rem with BitVec operands, got: {err}"
    );
}

#[test]
fn test_try_fp_fma_rejects_third_operand_mismatch() {
    let mut solver = Solver::new(Logic::QfFp);
    let a = solver.declare_const("a", Sort::FloatingPoint(8, 24));
    let b = solver.declare_const("b", Sort::FloatingPoint(8, 24));
    let c = solver.declare_const("c", Sort::FloatingPoint(11, 53));
    let rm = solver.try_fp_rounding_mode("RNE").unwrap();
    let err = solver.try_fp_fma(rm, a, b, c).unwrap_err();
    assert!(
        matches!(
            err,
            SolverError::SortMismatch {
                operation: "fp.fma",
                ..
            }
        ),
        "expected SortMismatch for fp.fma with mixed precision, got: {err}"
    );
}

// --- Rounding mode validation ---

#[test]
fn test_try_fp_rounding_mode_accepts_all_valid_modes() {
    let mut solver = Solver::new(Logic::QfFp);
    for mode in &["RNE", "RNA", "RTP", "RTN", "RTZ"] {
        assert!(
            solver.try_fp_rounding_mode(mode).is_ok(),
            "valid rounding mode '{mode}' should be accepted"
        );
    }
}

#[test]
fn test_try_fp_rounding_mode_rejects_invalid() {
    let mut solver = Solver::new(Logic::QfFp);
    let err = solver.try_fp_rounding_mode("INVALID").unwrap_err();
    assert!(
        matches!(
            err,
            SolverError::InvalidArgument {
                operation: "fp_rounding_mode",
                ..
            }
        ),
        "expected InvalidArgument for invalid rounding mode, got: {err}"
    );
}

// --- Classification predicates ---

#[test]
fn test_fp_is_nan_returns_bool_sort() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let is_nan = solver.try_fp_is_nan(x).unwrap();
    let sort = solver.terms().sort(is_nan.id()).clone();
    assert_eq!(sort, Sort::Bool);
}

#[test]
fn test_fp_eq_returns_bool_sort() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));
    let eq = solver.try_fp_eq(x, y).unwrap();
    let sort = solver.terms().sort(eq.id()).clone();
    assert_eq!(sort, Sort::Bool);
}

// --- Constants ---

#[test]
fn test_fp_constants_produce_correct_sort() {
    let mut solver = Solver::new(Logic::QfFp);
    let pinf = solver.fp_plus_infinity(8, 24);
    let ninf = solver.fp_minus_infinity(8, 24);
    let nan = solver.fp_nan(8, 24);
    let pzero = solver.fp_plus_zero(8, 24);
    let nzero = solver.fp_minus_zero(8, 24);

    for (term, name) in [
        (pinf, "+oo"),
        (ninf, "-oo"),
        (nan, "NaN"),
        (pzero, "+zero"),
        (nzero, "-zero"),
    ] {
        let sort = solver.terms().sort(term.id()).clone();
        assert_eq!(
            sort,
            Sort::FloatingPoint(8, 24),
            "FP constant {name} should have FloatingPoint(8,24) sort"
        );
    }
}

// --- Integration: basic FP satisfiability ---

/// Regression for #6328 / updated for #8456: the merged FP+Real model path
/// now runs full model validation instead of skipping it. The merged model IS
/// validated against the original assertions — `sat_model_validated`
/// is now true.
#[test]
fn test_fp_to_real_merged_model_sat_validated() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(5, 11));
    let r = solver.declare_const("r", Sort::Real);
    let fp_to_real = solver.try_fp_to_real(x).unwrap();
    let eq = solver.eq(r, fp_to_real);
    solver.assert_term(eq);
    let one = solver.real_const(1.0);
    let gt = solver.gt(r, one);
    solver.assert_term(gt);

    let details = solver.check_sat_with_details();
    // Must still be SAT (not degraded to Unknown by validation).
    assert_eq!(details.result, SolveResult::Sat);
    // #8456: FP model validation is now active — the merged model
    // passes validation against the original assertions.
    assert!(
        details.verification.sat_model_validated,
        "merged FP+Real model should now be validated (#8456)"
    );
}

#[test]
fn test_fp_nan_is_not_equal_to_itself() {
    // IEEE 754: NaN != NaN. Assert fp.eq(nan, nan) is false and check sat.
    let mut solver = Solver::new(Logic::QfFp);
    let nan = solver.fp_nan(8, 24);
    let eq = solver.try_fp_eq(nan, nan).unwrap();
    let not_eq = solver.not(eq);
    solver.assert_term(not_eq);
    // NaN != NaN is always true per IEEE 754, so this should be SAT.
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

/// Regression for #6009: API-level push/pop must not leak scoped FP
/// constraints across solves, even though the internal eager FP encoder does
/// not maintain its own push/pop trail.
#[test]
fn test_fp_incremental_push_pop_restores_base_assertions() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));

    let is_zero = solver.try_fp_is_zero(x).unwrap();
    solver.assert_term(is_zero);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    solver.push();
    let is_nan = solver.try_fp_is_nan(x).unwrap();
    solver.assert_term(is_nan);
    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "zero and NaN cannot hold in the same pushed scope"
    );
    solver.pop();

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "after pop(), only the base FP assertion should remain"
    );
}

/// Regression for #6009: repeated FP push/pop cycles must not accumulate stale
/// contradictory predicates from prior scopes.
#[test]
fn test_fp_incremental_push_pop_sequential_conflicts_do_not_leak() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));

    let is_zero = solver.try_fp_is_zero(x).unwrap();
    solver.assert_term(is_zero);

    for (name, scoped_constraint) in [
        ("normal", solver.try_fp_is_normal(x).unwrap()),
        ("NaN", solver.try_fp_is_nan(x).unwrap()),
        ("infinite", solver.try_fp_is_infinite(x).unwrap()),
    ] {
        solver.push();
        solver.assert_term(scoped_constraint);
        assert_eq!(
            solver.check_sat(),
            SolveResult::unsat(),
            "zero and {name} should be contradictory only inside the pushed scope"
        );
        solver.pop();
        assert_eq!(
            solver.check_sat(),
            SolveResult::Sat,
            "after popping the {name} scope, the base FP assertions should still be satisfiable"
        );
    }
}

/// Regression for #6009: FP `check_sat_assuming()` is currently unsupported
/// and must fail closed with `unknown` instead of mutating the scoped
/// assertion stack or silently dropping the assumption.
#[test]
fn test_fp_check_sat_assuming_returns_unknown_without_leaking_state() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));

    let is_zero = solver.try_fp_is_zero(x).unwrap();
    solver.assert_term(is_zero);

    solver.push();
    let is_positive = solver.try_fp_is_positive(x).unwrap();
    solver.assert_term(is_positive);
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "base pushed FP scope should stay satisfiable"
    );

    let is_nan = solver.try_fp_is_nan(x).unwrap();
    let assuming_result = solver.check_sat_assuming(&[is_nan]);
    assert!(
        assuming_result.is_unknown() || assuming_result.is_unsat(),
        "FP assumptions must fail closed until assumption-based FP solving exists, got {assuming_result:?}"
    );
    if assuming_result.is_unknown() {
        assert_eq!(solver.get_reason_unknown().as_deref(), Some("incomplete"));
    }

    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "temporary FP assumptions must not pollute the pushed scope"
    );
    solver.pop();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "popping after an FP assumption solve must restore the base assertions"
    );
}

#[test]
fn test_fp_rem_float64_supported_sat() {
    // fp.rem on Float64 is now supported (exact bounded modular reduction,
    // commit 143b360e4d) — no longer reports Unsupported. (= (fp.rem x y) z)
    // is trivially SAT (z binds to the remainder).
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));
    let y = solver.declare_const("y", Sort::FloatingPoint(11, 53));
    let z = solver.declare_const("z", Sort::FloatingPoint(11, 53));

    let rem = solver.try_fp_rem(x, y).unwrap();
    let rem_eq_z = solver.eq(rem, z);
    solver.assert_term(rem_eq_z);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

// --- fp.to_ieee_bv API tests ---

#[test]
fn test_fp_to_ieee_bv_sort_float32() {
    let mut solver = Solver::new(Logic::QfBvfp);
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let bv = solver
        .try_fp_to_ieee_bv(x)
        .expect("fp.to_ieee_bv should accept FP sort");
    assert_eq!(
        solver.term_sort(bv),
        Sort::bitvec(32),
        "fp.to_ieee_bv(Float32) should produce BV32"
    );
}

#[test]
fn test_fp_to_ieee_bv_sort_float64() {
    let mut solver = Solver::new(Logic::QfBvfp);
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));
    let bv = solver
        .try_fp_to_ieee_bv(x)
        .expect("fp.to_ieee_bv should accept FP sort");
    assert_eq!(
        solver.term_sort(bv),
        Sort::bitvec(64),
        "fp.to_ieee_bv(Float64) should produce BV64"
    );
}

#[test]
fn test_fp_to_ieee_bv_wrong_sort() {
    let mut solver = Solver::new(Logic::QfBvfp);
    let bv = solver.declare_const("x", Sort::bitvec(32));
    let result = solver.try_fp_to_ieee_bv(bv);
    assert!(
        matches!(result, Err(SolverError::SortMismatch { .. })),
        "fp.to_ieee_bv should reject non-FP sort"
    );
}

// ---------------------------------------------------------------------------
// Concrete FP-model representation boundary.
// ---------------------------------------------------------------------------

#[test]
fn float128_high_fraction_bit_fails_closed_before_model_extraction() {
    // Float128 has 112 explicitly stored fraction bits, while the current
    // concrete model stores that field in u64. Exercise a bit above 63 so a
    // missing preflight would shift/truncate in `extract_fp_model_from_bits`.
    let mut solver = Solver::new(Logic::QfBvfp);
    let x = solver.declare_const("wide_x", Sort::FloatingPoint(15, 113));
    let high_fraction = BigInt::from(1u8) << 100usize;
    let value = solver
        .try_fp_const_from_bits_bigint(&high_fraction, 15, 113)
        .expect("Float128 term construction remains supported");
    let equality = solver.eq(x, value);
    solver.assert_term(equality);

    assert_eq!(solver.check_sat(), SolveResult::Unknown);
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Incomplete));
}

#[test]
fn wide_fp_model_boundary_scans_unused_nested_declaration_sort() {
    // Model completion enumerates unused declarations too. Keep the FP sort
    // below no asserted term and nest it so a root-only scan cannot pass.
    let mut solver = Solver::new(Logic::All);
    let nested = Sort::array(Sort::Int, Sort::seq(Sort::FloatingPoint(15, 113)));
    let _array = solver.declare_const("wide_fp_array", nested);

    assert_eq!(solver.check_sat(), SolveResult::Unknown);
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Incomplete));
}
