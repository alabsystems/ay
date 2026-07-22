// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible floating-point (FPA) C API (`fpa.rs`).
//!
//! Coverage:
//! - FP sorts (`Z3_mk_fpa_sort` + convenience half/single/double/quadruple) and
//!   the rounding-mode sort.
//! - Rounding-mode constants build non-null terms.
//! - FP constants: NaN, +/-inf, +/-zero, numeral double/int.
//! - Build `(fp.add RNE a b)` and solve a small FP query: SAT + a model.
//! - A predicate (`fp.isNaN`) decides correctly (NaN-and-Infinite is UNSAT;
//!   the same constraints witness that the solver knows real FP semantics).
//! - SOUNDNESS / FP IS NOT REAL ARITHMETIC: `x + 0.0 == x` is NOT valid for FP
//!   (it fails when x is NaN). We assert the solver finds a counterexample
//!   (the negation is SAT), matching z3 — the FFI never fakes algebraic
//!   identities that FP does not obey.
//! - HONEST ERRORS: a non-FP sort handed to an FP constructor returns the null
//!   AST and sets `Z3_SORT_ERROR`; an unsupported numeral precision sets
//!   `Z3_INVALID_ARG`. No fabricated terms.

use super::super::*;
use std::ptr::null_mut;

/// Float32 sort helper.
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn f32_sort(ctx: Z3_context) -> Z3_sort {
    // SAFETY: forwarded under the caller's contract.
    unsafe { Z3_mk_fpa_sort_single(ctx) }
}

/// Declare a Float32 constant named `name`.
///
/// # Safety
/// `ctx`/`sort` must be valid handles.
unsafe fn fp32_const(ctx: Z3_context, sort: Z3_sort, name: &std::ffi::CStr) -> Z3_ast {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
        Z3_mk_const(ctx, sym, sort)
    }
}

/// FP sorts are constructed and reported with the FloatingPoint kind; the
/// convenience precisions map to the standard IEEE formats.
#[test]
fn test_fpa_sorts() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = Z3_mk_fpa_sort(ctx, 8, 24);
        assert!(!s.is_null(), "Z3_mk_fpa_sort(8,24) should be non-null");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let half = Z3_mk_fpa_sort_half(ctx);
        let single = Z3_mk_fpa_sort_single(ctx);
        let double = Z3_mk_fpa_sort_double(ctx);
        let quad = Z3_mk_fpa_sort_quadruple(ctx);
        assert!(!half.is_null() && !single.is_null() && !double.is_null() && !quad.is_null());

        // single == (8,24): same stable semantic sort id as the explicit sort.
        assert_eq!(Z3_get_sort_id(ctx, s), Z3_get_sort_id(ctx, single));
        // half != double.
        assert_ne!(Z3_get_sort_id(ctx, half), Z3_get_sort_id(ctx, double));

        let rm_sort = Z3_mk_fpa_rounding_mode_sort(ctx);
        assert!(!rm_sort.is_null());

        // Degenerate widths are rejected honestly.
        let bad = Z3_mk_fpa_sort(ctx, 1, 1);
        assert!(bad.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        let too_wide = Z3_mk_fpa_sort(ctx, 32, 24);
        assert!(too_wide.is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        Z3_del_context(ctx);
    }
}

/// All five rounding-mode constants (and their short aliases) build terms.
#[test]
fn test_fpa_rounding_modes() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let modes = [
            Z3_mk_fpa_round_nearest_ties_to_even(ctx),
            Z3_mk_fpa_rne(ctx),
            Z3_mk_fpa_round_nearest_ties_to_away(ctx),
            Z3_mk_fpa_rna(ctx),
            Z3_mk_fpa_round_toward_positive(ctx),
            Z3_mk_fpa_rtp(ctx),
            Z3_mk_fpa_round_toward_negative(ctx),
            Z3_mk_fpa_rtn(ctx),
            Z3_mk_fpa_round_toward_zero(ctx),
            Z3_mk_fpa_rtz(ctx),
        ];
        for (i, m) in modes.iter().enumerate() {
            assert!(*m != 0, "rounding mode #{i} should be non-null");
        }
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// FP special constants (NaN, +/-inf, +/-zero) and numerals build terms.
#[test]
fn test_fpa_constants() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = f32_sort(ctx);

        let nan = Z3_mk_fpa_nan(ctx, s);
        let pinf = Z3_mk_fpa_inf(ctx, s, false);
        let ninf = Z3_mk_fpa_inf(ctx, s, true);
        let pzero = Z3_mk_fpa_zero(ctx, s, false);
        let nzero = Z3_mk_fpa_zero(ctx, s, true);
        assert!(nan != 0 && pinf != 0 && ninf != 0 && pzero != 0 && nzero != 0);

        let one = Z3_mk_fpa_numeral_double(ctx, 1.0, s);
        let half = Z3_mk_fpa_numeral_double(ctx, 0.5, s);
        let three = Z3_mk_fpa_numeral_int(ctx, 3, s);
        assert!(one != 0 && half != 0 && three != 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// Build `(fp.add RNE a b)` and solve `a == 1.0 /\ b == 2.0 /\ (a+b) == 3.0`:
/// the query is SAT and a model is available.
#[test]
fn test_fpa_add_solve_sat_with_model() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = f32_sort(ctx);
        let a = fp32_const(ctx, s, c"a");
        let b = fp32_const(ctx, s, c"b");
        let rne = Z3_mk_fpa_rne(ctx);

        let one = Z3_mk_fpa_numeral_double(ctx, 1.0, s);
        let two = Z3_mk_fpa_numeral_double(ctx, 2.0, s);
        let three = Z3_mk_fpa_numeral_double(ctx, 3.0, s);

        let sum = Z3_mk_fpa_add(ctx, rne, a, b);
        assert!(sum != 0, "fp.add should build a term");
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_OK,
            "building fp.add should not set an error"
        );

        // a == 1.0, b == 2.0, (a+b) == 3.0  (fp.eq is the IEEE equality)
        let a_eq = Z3_mk_fpa_eq(ctx, a, one);
        let b_eq = Z3_mk_fpa_eq(ctx, b, two);
        let sum_eq = Z3_mk_fpa_eq(ctx, sum, three);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, a_eq);
        Z3_solver_assert(ctx, solver, b_eq);
        Z3_solver_assert(ctx, solver, sum_eq);

        let r = Z3_solver_check(ctx, solver);
        assert_eq!(r, Z3_L_TRUE, "1.0 + 2.0 == 3.0 in Float32 should be SAT");

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null(), "a SAT FP query should yield a model");
        let model_str = Z3_model_to_string(ctx, model);
        assert!(!model_str.is_null(), "model should render to a string");

        Z3_del_context(ctx);
    }
}

/// `(fp.add RNE a b) == 4.0` while `a == 1.0 /\ b == 2.0` is UNSAT: the FP
/// addition is interpreted (1+2 != 4), so the solver refutes it. This proves the
/// term routes through the real FP theory, not a free uninterpreted function.
#[test]
fn test_fpa_add_is_interpreted_unsat() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = f32_sort(ctx);
        let a = fp32_const(ctx, s, c"a");
        let b = fp32_const(ctx, s, c"b");
        let rne = Z3_mk_fpa_rne(ctx);

        let one = Z3_mk_fpa_numeral_double(ctx, 1.0, s);
        let two = Z3_mk_fpa_numeral_double(ctx, 2.0, s);
        let four = Z3_mk_fpa_numeral_double(ctx, 4.0, s);

        let sum = Z3_mk_fpa_add(ctx, rne, a, b);
        let a_eq = Z3_mk_fpa_eq(ctx, a, one);
        let b_eq = Z3_mk_fpa_eq(ctx, b, two);
        let sum_eq = Z3_mk_fpa_eq(ctx, sum, four);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, a_eq);
        Z3_solver_assert(ctx, solver, b_eq);
        Z3_solver_assert(ctx, solver, sum_eq);

        let r = Z3_solver_check(ctx, solver);
        assert_eq!(r, Z3_L_FALSE, "1.0 + 2.0 == 4.0 must be UNSAT");

        Z3_del_context(ctx);
    }
}

/// Predicate test: `(fp.isNaN x) /\ (fp.isInfinite x)` is UNSAT (a value cannot
/// be both NaN and infinite), while `(fp.isNaN x)` alone is SAT.
#[test]
fn test_fpa_is_nan_predicate() {
    // SAFETY: see above.
    unsafe {
        // isNaN alone: SAT.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let s = f32_sort(ctx);
        let x = fp32_const(ctx, s, c"x");
        let is_nan = Z3_mk_fpa_is_nan(ctx, x);
        assert!(is_nan != 0);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_nan);
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_TRUE,
            "isNaN should be SAT"
        );
        Z3_del_context(ctx);

        // isNaN AND isInfinite: UNSAT.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let s = f32_sort(ctx);
        let x = fp32_const(ctx, s, c"x");
        let is_nan = Z3_mk_fpa_is_nan(ctx, x);
        let is_inf = Z3_mk_fpa_is_infinite(ctx, x);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, is_nan);
        Z3_solver_assert(ctx, solver, is_inf);
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_FALSE,
            "NaN AND Infinite should be UNSAT"
        );
        Z3_del_context(ctx);
    }
}

/// SOUNDNESS: `x + 0.0 == x` is NOT a valid FP identity (it fails for x = NaN,
/// since NaN != NaN under fp.eq). We assert `(not (fp.eq (fp.add RNE x +0) x))`
/// is SAT — i.e. the solver finds a counterexample, exactly as z3 does. If the
/// FFI fabricated real-arithmetic semantics, this would wrongly be UNSAT.
#[test]
fn test_fpa_add_zero_not_identity_soundness() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s = f32_sort(ctx);
        let x = fp32_const(ctx, s, c"x");
        let rne = Z3_mk_fpa_rne(ctx);
        let pzero = Z3_mk_fpa_zero(ctx, s, false);

        let sum = Z3_mk_fpa_add(ctx, rne, x, pzero);
        let eq = Z3_mk_fpa_eq(ctx, sum, x);
        let neq = Z3_mk_not(ctx, eq);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, neq);

        let r = Z3_solver_check(ctx, solver);
        assert_eq!(
            r, Z3_L_TRUE,
            "x + 0.0 == x is NOT FP-valid (fails at NaN); the negation must be SAT"
        );

        Z3_del_context(ctx);
    }
}

/// HONEST ERRORS: FP constructors reject non-FP sorts / operands and unsupported
/// numeral precisions rather than fabricating a term.
#[test]
fn test_fpa_honest_errors() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // A NaN constructor on a non-FP (Int) sort => null + Z3_SORT_ERROR.
        let int_sort = Z3_mk_int_sort(ctx);
        let bad_nan = Z3_mk_fpa_nan(ctx, int_sort);
        assert_eq!(bad_nan, 0, "NaN on a non-FP sort must return null");
        assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);

        // fp.add on Int operands => null + Z3_SORT_ERROR.
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"i".as_ptr()), int_sort);
        let rne = Z3_mk_fpa_rne(ctx);
        let bad_add = Z3_mk_fpa_add(ctx, rne, x, x);
        assert_eq!(bad_add, 0, "fp.add on Int operands must return null");
        assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);

        // numeral_double on an unsupported (3,5) precision => null + Z3_INVALID_ARG.
        let weird = Z3_mk_fpa_sort(ctx, 3, 5);
        assert!(!weird.is_null());
        let bad_num = Z3_mk_fpa_numeral_double(ctx, 1.0, weird);
        assert_eq!(
            bad_num, 0,
            "numeral on unsupported precision must return null"
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        // A null sort is likewise rejected.
        let bad_null = Z3_mk_fpa_nan(ctx, null_mut());
        assert_eq!(bad_null, 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);

        Z3_del_context(ctx);
    }
}

/// Every rounded FPA constructor rejects a non-RoundingMode `rm` operand at
/// the C API boundary. The core builders intentionally accept an internal RM
/// term, so this regression test covers each distinct FFI forwarding path.
#[test]
fn test_fpa_rounding_operations_reject_wrong_rm_sort() {
    // SAFETY: all handles are created in and remain owned by this context.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let fp_sort = f32_sort(ctx);
        let fp = Z3_mk_fpa_zero(ctx, fp_sort, false);
        let bv_sort = Z3_mk_bv_sort(ctx, 8);
        let bv = Z3_mk_unsigned_int64(ctx, 1, bv_sort);
        let int_sort = Z3_mk_int_sort(ctx);
        let exponent = Z3_mk_int(ctx, 0, int_sort);
        let real_sort = Z3_mk_real_sort(ctx);
        let real = Z3_mk_numeral(ctx, c"1".as_ptr(), real_sort);
        let bad_rm = Z3_mk_true(ctx);

        macro_rules! assert_bad_rm {
            ($call:expr) => {{
                let result = $call;
                assert_eq!(result, 0, "non-RoundingMode operand must be rejected");
                assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);
            }};
        }

        assert_bad_rm!(Z3_mk_fpa_add(ctx, bad_rm, fp, fp));
        assert_bad_rm!(Z3_mk_fpa_fma(ctx, bad_rm, fp, fp, fp));
        assert_bad_rm!(Z3_mk_fpa_sqrt(ctx, bad_rm, fp));
        assert_bad_rm!(Z3_mk_fpa_round_to_integral(ctx, bad_rm, fp));
        assert_bad_rm!(Z3_mk_fpa_to_fp_float(ctx, bad_rm, fp, fp_sort));
        assert_bad_rm!(Z3_mk_fpa_to_fp_signed(ctx, bad_rm, bv, fp_sort));
        assert_bad_rm!(Z3_mk_fpa_to_fp_unsigned(ctx, bad_rm, bv, fp_sort));
        assert_bad_rm!(Z3_mk_fpa_to_sbv(ctx, bad_rm, fp, 8));
        assert_bad_rm!(Z3_mk_fpa_to_ubv(ctx, bad_rm, fp, 8));
        assert_bad_rm!(Z3_mk_fpa_to_fp_real(ctx, bad_rm, real, fp_sort));
        assert_bad_rm!(Z3_mk_fpa_to_fp_int_real(
            ctx, bad_rm, exponent, real, fp_sort
        ));

        Z3_del_context(ctx);
    }
}

/// FP comparison + conversion smoke: `fp.lt`, `fp.to_fp_float` (Float32->Float64)
/// build terms and a `fp.lt` query solves SAT.
#[test]
fn test_fpa_compare_and_convert() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let s32 = Z3_mk_fpa_sort_single(ctx);
        let s64 = Z3_mk_fpa_sort_double(ctx);
        let a = fp32_const(ctx, s32, c"a");
        let b = fp32_const(ctx, s32, c"b");

        let lt = Z3_mk_fpa_lt(ctx, a, b);
        assert!(lt != 0);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, lt);
        assert_eq!(
            Z3_solver_check(ctx, solver),
            Z3_L_TRUE,
            "a < b should be SAT"
        );

        // Convert a (Float32) up to Float64 with RNE.
        let rne = Z3_mk_fpa_rne(ctx);
        let a64 = Z3_mk_fpa_to_fp_float(ctx, rne, a, s64);
        assert!(a64 != 0, "Float32->Float64 conversion should build a term");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}
