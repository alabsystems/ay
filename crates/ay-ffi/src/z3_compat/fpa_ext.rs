// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible floating-point (FPA) real constructors/conversions, part 2.
//!
//! This module extends the FPA family in [`super::fpa`] with the numeric-named
//! sort aliases (`_16/_32/_64/_128`), the `(eb, sb)` accessors
//! ([`Z3_fpa_get_ebits`] / [`Z3_fpa_get_sbits`]), the `fp` bit-vector
//! constructor and its conversions (`to_fp_bv`, `to_fp_unsigned`, `to_ieee_bv`,
//! `to_real`, `to_sbv`, `to_ubv`), and the integer/float numeral constructors.
//!
//! Like [`super::fpa`], every operation delegates to a PROVEN-CORRECT
//! `ay_dpll::api::Solver` FP builder (`try_fp_from_bvs`,
//! `try_bv_to_fp_reinterpret`, `try_bv_to_fp_unsigned`, `try_fp_to_ieee_bv`,
//! `try_fp_to_real`, `try_fp_to_sbv`, `try_fp_to_ubv`,
//! `try_fp_const_from_bits_bigint`) — the exact constructors AY's SMT-LIB
//! elaborator and model reconstruction use (see
//! `crates/ay-dpll/src/api/floating_point.rs` and
//! `crates/ay-dpll/src/api/floating_point_conv.rs`).
//!
//! # Soundness
//!
//! NO FP semantics are invented in this FFI layer: an FFI function only builds
//! the operand terms (or, for the integer numeral constructors, packs the exact
//! IEEE-754 bit pattern verified byte-for-byte against Z3 4.16) and forwards to
//! the core builder. When an operation is requested with operands the core
//! rejects (sort mismatch, wrong width, unsupported precision), the function
//! returns the null sentinel and records `Z3_SORT_ERROR`/`Z3_INVALID_ARG`
//! rather than fabricating an ill-typed or wrong term.
//!
//! DIVERGENCE: `Z3_mk_fpa_numeral_int_uint` / `Z3_mk_fpa_numeral_int64_uint64`
//! reproduce Z3's `mpf_manager::set` semantics ONLY for values that land in the
//! IEEE-754 *normal* range of the target format (see those functions for the
//! exact guard). Z3's `mpf` carries an unbounded internal exponent, so its
//! `fp.to_ieee_bv` rendering of subnormal / zero / infinity / overflowing
//! operands is a lossy wrap-around artifact of the internal representation, not
//! a clean interchange encoding; AY declines those inputs (`Z3_INVALID_ARG`)
//! rather than fabricate a possibly-wrong term. Callers needing zero/inf should
//! use [`super::Z3_mk_fpa_zero`] / [`super::Z3_mk_fpa_inf`], and
//! [`super::Z3_mk_fpa_numeral_double`] for arbitrary rounded values.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via the
//! `ffi_guard_*` helpers to prevent undefined behavior from panics unwinding
//! across the `extern "C"` boundary.

use std::ffi::{c_float, c_int, c_uint};

use num_bigint::BigInt;

use ay_dpll::api::Sort;

use super::{
    ast_to_term, ffi_guard_ast, ffi_guard_uint, record_ast_sort, require_fpa_rounding_mode,
    term_to_ast, Z3Context, Z3_ast, Z3_context, Z3_mk_fpa_numeral_double, Z3_mk_fpa_sort, Z3_sort,
    MAX_FFI_BITVECTOR_WIDTH, MAX_FFI_FP_EXPONENT_BITS, Z3_INVALID_ARG, Z3_SORT_ERROR,
};

/// Record an error code + message on the context and return the null AST sentinel.
fn ast_error(ctx: &mut Z3Context, code: c_uint, msg: impl Into<String>) -> Z3_ast {
    ctx.last_error = code;
    ctx.error_msg = Some(msg.into());
    0
}

/// Read the `(eb, sb)` of an FP sort handle, or `None` if it is not an FP sort.
///
/// # Safety
/// `s` must be null or a valid `Z3_sort` produced by this context.
unsafe fn fp_sort_params(s: Z3_sort) -> Option<(u32, u32)> {
    if s.is_null() {
        return None;
    }
    // SAFETY: `s` was null-checked and originates from a prior AY FFI allocation
    // whose handle is kept alive by the owning `Z3Context`. Reading `.sort` is a
    // shared-read with no concurrent mutation (single-threaded per context).
    match unsafe { &(*s).sort } {
        Sort::FloatingPoint(eb, sb) => Some((*eb, *sb)),
        _ => None,
    }
}

// ============================================================================
// Numeric-named FP sort aliases
// ============================================================================

/// Create the half-precision (16-bit) FP sort: `(_ FloatingPoint 5 11)`.
///
/// Identical to [`super::Z3_mk_fpa_sort_half`]; the numeric name is the Z3 alias.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_16(c: Z3_context) -> Z3_sort {
    // SAFETY: forwards to the shared FP-sort constructor under the caller's contract.
    unsafe { Z3_mk_fpa_sort(c, 5, 11) }
}

/// Create the single-precision (32-bit) FP sort: `(_ FloatingPoint 8 24)`.
///
/// Identical to [`super::Z3_mk_fpa_sort_single`]; the numeric name is the Z3 alias.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_32(c: Z3_context) -> Z3_sort {
    // SAFETY: forwards to the shared FP-sort constructor under the caller's contract.
    unsafe { Z3_mk_fpa_sort(c, 8, 24) }
}

/// Create the double-precision (64-bit) FP sort: `(_ FloatingPoint 11 53)`.
///
/// Identical to [`super::Z3_mk_fpa_sort_double`]; the numeric name is the Z3 alias.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_64(c: Z3_context) -> Z3_sort {
    // SAFETY: forwards to the shared FP-sort constructor under the caller's contract.
    unsafe { Z3_mk_fpa_sort(c, 11, 53) }
}

/// Create the quadruple-precision (128-bit) FP sort: `(_ FloatingPoint 15 113)`.
///
/// Identical to [`super::Z3_mk_fpa_sort_quadruple`]; the numeric name is the Z3
/// alias.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_128(c: Z3_context) -> Z3_sort {
    // SAFETY: forwards to the shared FP-sort constructor under the caller's contract.
    unsafe { Z3_mk_fpa_sort(c, 15, 113) }
}

// ============================================================================
// FP sort accessors
// ============================================================================

/// Retrieve the number of exponent bits of an FP sort.
///
/// Pure-FFI read of the sort handle's [`Sort::FloatingPoint`] `eb` field — no
/// solver call. Returns `0` + `Z3_SORT_ERROR` when `s` is null or not an FP sort.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid sort handle (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_ebits(c: Z3_context, s: Z3_sort) -> c_uint {
    // SAFETY: `s` read under the single-threaded-per-context contract.
    let params = unsafe { fp_sort_params(s) };
    // SAFETY: `c` forwarded under the caller's contract; `ffi_guard_uint`
    // null-checks it and catches panics at the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match params {
            Some((eb, _)) => eb,
            None => {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_fpa_get_ebits: s must be a FloatingPoint sort".to_string());
                0
            }
        })
    }
}

/// Retrieve the number of significand bits of an FP sort (INCLUDING the hidden
/// bit, matching Z3 and AY's [`Sort::FloatingPoint`] `sb` field).
///
/// Pure-FFI read of the sort handle — no solver call. Returns `0` +
/// `Z3_SORT_ERROR` when `s` is null or not an FP sort.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid sort handle (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_sbits(c: Z3_context, s: Z3_sort) -> c_uint {
    // SAFETY: `s` read under the single-threaded-per-context contract.
    let params = unsafe { fp_sort_params(s) };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match params {
            Some((_, sb)) => sb,
            None => {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_fpa_get_sbits: s must be a FloatingPoint sort".to_string());
                0
            }
        })
    }
}

// ============================================================================
// FP constructor from sign / exponent / significand bit-vectors
// ============================================================================

/// Create an FP value from three bit-vectors: `(fp sgn exp sig)`.
///
/// The resulting FP sort is derived from the operand widths exactly as Z3 does:
/// `sgn` must be a 1-bit BV, `eb = width(exp)`, and `sb = width(sig) + 1`. The
/// exponent is the IEEE-754 *biased* field. Backed by
/// [`ay_dpll::api::Solver::try_fp_from_bvs`], which re-validates all three
/// widths. Returns NULL + `Z3_SORT_ERROR` if any operand is not a BitVec, or
/// NULL + `Z3_INVALID_ARG` if the widths are inconsistent.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_fp(
    c: Z3_context,
    sgn: Z3_ast,
    exp: Z3_ast,
    sig: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let (sgnt, expt, sigt) = (ast_to_term(sgn), ast_to_term(exp), ast_to_term(sig));
            let Sort::BitVec(sign_bv) = ctx.solver.sort_of(sgnt) else {
                return ast_error(ctx, Z3_SORT_ERROR, "Z3_mk_fpa_fp: sign must be a BitVec");
            };
            let Sort::BitVec(exp_bv) = ctx.solver.sort_of(expt) else {
                return ast_error(ctx, Z3_SORT_ERROR, "Z3_mk_fpa_fp: exp must be a BitVec");
            };
            let Sort::BitVec(sig_bv) = ctx.solver.sort_of(sigt) else {
                return ast_error(ctx, Z3_SORT_ERROR, "Z3_mk_fpa_fp: sig must be a BitVec");
            };
            let eb = exp_bv.width;
            let Some(sb) = sig_bv.width.checked_add(1) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_mk_fpa_fp: significand width + 1 overflows u32",
                );
            };
            if sign_bv.width != 1 {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!("Z3_mk_fpa_fp: sign width must be 1, got {}", sign_bv.width),
                );
            }
            if !(2..=MAX_FFI_FP_EXPONENT_BITS).contains(&eb)
                || !(2..=MAX_FFI_BITVECTOR_WIDTH).contains(&sb)
            {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!(
                        "Z3_mk_fpa_fp: widths outside supported ranges: eb={eb} (2..={MAX_FFI_FP_EXPONENT_BITS}), sb={sb} (2..={MAX_FFI_BITVECTOR_WIDTH})"
                    ),
                );
            }
            match ctx.solver.try_fp_from_bvs(sgnt, expt, sigt, eb, sb) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

// ============================================================================
// BV -> FP conversions
// ============================================================================

/// Reinterpret an IEEE-754 bit-vector as an FP value: `((_ to_fp eb sb) bv)`.
///
/// One-argument (no rounding mode) raw bit-pattern reinterpretation. `bv` must
/// be a BitVec of width `eb + sb`, where `(eb, sb)` come from the target sort
/// `s`. Backed by [`ay_dpll::api::Solver::try_bv_to_fp_reinterpret`]. Returns
/// NULL + `Z3_SORT_ERROR` if `s` is not FP or `bv` is not a BitVec, or NULL +
/// `Z3_INVALID_ARG` if the BV width is not `eb + sb`.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_fp_bv(c: Z3_context, bv: Z3_ast, s: Z3_sort) -> Z3_ast {
    // SAFETY: `s` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(s) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_bv: target sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let bvt = ast_to_term(bv);
            if !matches!(ctx.solver.sort_of(bvt), Sort::BitVec(_)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_bv: value must be a BitVec",
                );
            }
            match ctx.solver.try_bv_to_fp_reinterpret(bvt, eb, sb) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Convert an *unsigned* bit-vector to an FP value: `((_ to_fp_unsigned eb sb) rm t)`.
///
/// `t` must be a BitVec value and `s` a FloatingPoint sort. Backed by
/// [`ay_dpll::api::Solver::try_bv_to_fp_unsigned`]. Mirrors
/// [`super::Z3_mk_fpa_to_fp_signed`], swapping the signed builder for the
/// unsigned one.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_fp_unsigned(
    c: Z3_context,
    rm: Z3_ast,
    t: Z3_ast,
    s: Z3_sort,
) -> Z3_ast {
    // SAFETY: `s` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(s) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_unsigned: target sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_unsigned", rm) else {
                return 0;
            };
            let bvt = ast_to_term(t);
            if !matches!(ctx.solver.sort_of(bvt), Sort::BitVec(_)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_unsigned: value must be a BitVec",
                );
            }
            match ctx.solver.try_bv_to_fp_unsigned(rmt, bvt, eb, sb) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

// ============================================================================
// FP -> BV / Real conversions
// ============================================================================

/// Reinterpret an FP value as its IEEE-754 bit-vector: `(fp.to_ieee_bv t)`.
///
/// `t` must be a FloatingPoint value; the result is a BitVec of width `eb + sb`.
/// Backed by [`ay_dpll::api::Solver::try_fp_to_ieee_bv`]. The recorded result
/// sort is the exact BitVec sort the core builder assigned. Returns NULL +
/// `Z3_SORT_ERROR` if `t` is not FP.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_ieee_bv(c: Z3_context, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let xt = ast_to_term(t);
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(xt) else {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_ieee_bv: operand must be FloatingPoint",
                );
            };
            let Some(width) = eb.checked_add(sb) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_mk_fpa_to_ieee_bv: result width overflows u32",
                );
            };
            if width > MAX_FFI_BITVECTOR_WIDTH {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!(
                        "Z3_mk_fpa_to_ieee_bv: result width {width} exceeds the supported maximum {MAX_FFI_BITVECTOR_WIDTH}"
                    ),
                );
            }
            match ctx.solver.try_fp_to_ieee_bv(xt) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    // Record the BitVec(eb+sb) sort the core builder computed.
                    let sort = ctx.solver.sort_of(t);
                    record_ast_sort(ctx, a, sort);
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Convert an FP value to a Real: `(fp.to_real t)`.
///
/// `t` must be a FloatingPoint value; the result has sort Real. Backed by
/// [`ay_dpll::api::Solver::try_fp_to_real`]. Returns NULL + `Z3_SORT_ERROR` if
/// `t` is not FP.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_real(c: Z3_context, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let xt = ast_to_term(t);
            if !matches!(ctx.solver.sort_of(xt), Sort::FloatingPoint(_, _)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_real: operand must be FloatingPoint",
                );
            }
            match ctx.solver.try_fp_to_real(xt) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::Real);
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Convert an FP value to a signed bit-vector: `((_ fp.to_sbv sz) rm t)`.
///
/// `t` must be a FloatingPoint value; the result is a BitVec of width `sz`.
/// Backed by [`ay_dpll::api::Solver::try_fp_to_sbv`]. Returns NULL +
/// `Z3_SORT_ERROR` if `t` is not FP.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_sbv(
    c: Z3_context,
    rm: Z3_ast,
    t: Z3_ast,
    sz: c_uint,
) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if sz == 0 || sz > MAX_FFI_BITVECTOR_WIDTH {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!(
                        "Z3_mk_fpa_to_sbv: result width {sz} is outside the supported range 1..={MAX_FFI_BITVECTOR_WIDTH}"
                    ),
                );
            }
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_sbv", rm) else {
                return 0;
            };
            let xt = ast_to_term(t);
            if !matches!(ctx.solver.sort_of(xt), Sort::FloatingPoint(_, _)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_sbv: operand must be FloatingPoint",
                );
            }
            match ctx.solver.try_fp_to_sbv(rmt, xt, sz) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::bitvec(sz));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Convert an FP value to an unsigned bit-vector: `((_ fp.to_ubv sz) rm t)`.
///
/// `t` must be a FloatingPoint value; the result is a BitVec of width `sz`.
/// Backed by [`ay_dpll::api::Solver::try_fp_to_ubv`]. Returns NULL +
/// `Z3_SORT_ERROR` if `t` is not FP.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_ubv(
    c: Z3_context,
    rm: Z3_ast,
    t: Z3_ast,
    sz: c_uint,
) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if sz == 0 || sz > MAX_FFI_BITVECTOR_WIDTH {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!(
                        "Z3_mk_fpa_to_ubv: result width {sz} is outside the supported range 1..={MAX_FFI_BITVECTOR_WIDTH}"
                    ),
                );
            }
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_ubv", rm) else {
                return 0;
            };
            let xt = ast_to_term(t);
            if !matches!(ctx.solver.sort_of(xt), Sort::FloatingPoint(_, _)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_ubv: operand must be FloatingPoint",
                );
            }
            match ctx.solver.try_fp_to_ubv(rmt, xt, sz) {
                Ok(t) => {
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::bitvec(sz));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

// ============================================================================
// Numeral constructors
// ============================================================================

/// Create an FP numeral from a C `float`, rounded to the given FP sort.
///
/// The `float` is widened to `double` (exact — `f64` is a superset of `f32`)
/// and routed through [`super::Z3_mk_fpa_numeral_double`], which uses the
/// hardware's correctly-rounded conversion. Supports the standard half/single/
/// double precisions (5/11, 8/24, 11/53); other `(eb, sb)` return NULL +
/// `Z3_INVALID_ARG`, matching `Z3_mk_fpa_numeral_double`'s honest limitation.
///
/// # Safety
/// `c` must be a valid context pointer; `ty` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_numeral_float(c: Z3_context, v: c_float, ty: Z3_sort) -> Z3_ast {
    // SAFETY: forwards to Z3_mk_fpa_numeral_double under the same caller contract;
    // widening f32 -> f64 is exact so no precision is lost before rounding.
    unsafe { Z3_mk_fpa_numeral_double(c, f64::from(v), ty) }
}

/// Assemble the IEEE-754 bit pattern for a normal-range FP value and build the
/// numeral, or record `Z3_INVALID_ARG` if the value is not a normal float.
///
/// Reproduces Z3's `mpf_manager::set(o, ebits, sbits, sign, exponent, sig)`
/// semantics, verified against Z3 4.16: the mathematical value is
/// `(-1)^sgn * (1 + sig / 2^(sb-1)) * 2^exp`, i.e. `exp` is the *unbiased*
/// exponent and `sig` is the trailing-significand field. This encodes cleanly to
/// IEEE-754 exactly when the value is *normal*:
/// `1 <= exp + bias <= 2^eb - 2` (with `bias = 2^(eb-1) - 1`) and
/// `0 <= sig < 2^(sb-1)`. Any other input (subnormal, zero, infinity, or a
/// significand wider than the field) is declined — see the module-level
/// DIVERGENCE note.
fn build_fp_numeral_fields(
    ctx: &mut Z3Context,
    op: &'static str,
    sgn: bool,
    exp: i128,
    sig: u128,
    eb: u32,
    sb: u32,
) -> Z3_ast {
    // Defensive: every real IEEE format has eb, sb >= 2 (Z3_mk_fpa_sort enforces
    // this). Reject a malformed sort before the `eb - 1` / `sb - 1` shifts below
    // could underflow `usize` and attempt an enormous allocation.
    if eb < 2 || sb < 2 {
        return ast_error(
            ctx,
            Z3_INVALID_ARG,
            format!("{op}: FloatingPoint({eb}, {sb}) has degenerate width (eb, sb must be >= 2)"),
        );
    }

    // 2^n as a BigInt (n < eb+sb, always small for real formats).
    let pow2 = |n: usize| BigInt::from(1u8) << n;
    let one = BigInt::from(1u8);

    // bias = 2^(eb-1) - 1 ; the biased exponent field is exp + bias.
    let bias = pow2(eb as usize - 1) - &one;
    let biased = BigInt::from(exp) + bias;
    let max_biased = pow2(eb as usize) - &one - &one; // 2^eb - 2 (largest normal field)
    if biased < one || biased > max_biased {
        return ast_error(
            ctx,
            Z3_INVALID_ARG,
            format!(
                "{op}: biased exponent out of normal range for FloatingPoint({eb}, {sb}); \
                 only normal values (1 <= exp + bias <= 2^eb - 2) are supported by this raw \
                 integer constructor — use Z3_mk_fpa_zero / Z3_mk_fpa_inf / \
                 Z3_mk_fpa_numeral_double for other values"
            ),
        );
    }
    let sig_big = BigInt::from(sig);
    let sig_field_limit = pow2(sb as usize - 1); // 2^(sb-1)
    if sig_big >= sig_field_limit {
        return ast_error(
            ctx,
            Z3_INVALID_ARG,
            format!(
                "{op}: significand {sig} does not fit in the {} trailing-significand bits",
                sb - 1
            ),
        );
    }
    // IEEE-754 layout: sign(1) | exponent(eb) | trailing-significand(sb-1).
    let sign_shift = (eb + sb - 1) as usize;
    let bits =
        (BigInt::from(u8::from(sgn)) << sign_shift) | (biased << (sb as usize - 1)) | sig_big;
    match ctx.solver.try_fp_const_from_bits_bigint(&bits, eb, sb) {
        Ok(t) => {
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
            a
        }
        Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
    }
}

/// Create an FP numeral from a sign bit and two integers (32-bit).
///
/// `sgn` is the sign (true = negative), `exp` the *unbiased* exponent, and `sig`
/// the trailing-significand field: the value is
/// `(-1)^sgn * (1 + sig / 2^(sb-1)) * 2^exp`, matching Z3's `mpf_manager::set`.
/// Only normal-range values are supported (see [`build_fp_numeral_fields`]);
/// out-of-range inputs return NULL + `Z3_INVALID_ARG`. `ty` must be an FP sort,
/// else NULL + `Z3_SORT_ERROR`.
///
/// # Safety
/// `c` must be a valid context pointer; `ty` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_numeral_int_uint(
    c: Z3_context,
    sgn: bool,
    exp: c_int,
    sig: c_uint,
    ty: Z3_sort,
) -> Z3_ast {
    // SAFETY: `ty` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(ty) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_numeral_int_uint: ty must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            build_fp_numeral_fields(
                ctx,
                "Z3_mk_fpa_numeral_int_uint",
                sgn,
                i128::from(exp),
                u128::from(sig),
                eb,
                sb,
            )
        })
    }
}

/// Create an FP numeral from a sign bit and two 64-bit integers.
///
/// Same `mpf_manager::set` semantics as [`Z3_mk_fpa_numeral_int_uint`] with
/// 64-bit `exp`/`sig`, enabling the wider significand fields of FP128. Only
/// normal-range values are supported (see [`build_fp_numeral_fields`]);
/// out-of-range inputs return NULL + `Z3_INVALID_ARG`. `ty` must be an FP sort,
/// else NULL + `Z3_SORT_ERROR`.
///
/// # Safety
/// `c` must be a valid context pointer; `ty` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_numeral_int64_uint64(
    c: Z3_context,
    sgn: bool,
    exp: i64,
    sig: u64,
    ty: Z3_sort,
) -> Z3_ast {
    // SAFETY: `ty` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(ty) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_numeral_int64_uint64: ty must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            build_fp_numeral_fields(
                ctx,
                "Z3_mk_fpa_numeral_int64_uint64",
                sgn,
                i128::from(exp),
                u128::from(sig),
                eb,
                sb,
            )
        })
    }
}
