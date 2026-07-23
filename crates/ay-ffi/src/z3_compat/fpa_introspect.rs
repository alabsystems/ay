// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible floating-point numeral introspection + Real/Int -> FP (#phase3-fpa).
//!
//! Wires Z3's `Z3_fpa_is_numeral*` / `Z3_fpa_get_numeral_*` accessors and the
//! `Z3_mk_fpa_to_fp_real` / `Z3_mk_fpa_to_fp_int_real` constructors onto AY's
//! native FP theory. Every value read delegates to the PROVEN-CORRECT decoder
//! [`ay_dpll::api::Solver::fp_numeral_decode`], which pattern-matches AY's three
//! canonical FP-numeral term shapes (special-value app, 1-arg `to_fp` over a BV
//! const, 3-arg `fp` over BV consts) — the exact terms AY's FP builders and the
//! `Z3_mk_fpa_*` numeral constructors (see `fpa.rs` / `fpa_ext.rs`) produce.
//!
//! # Soundness
//!
//! NO FP semantics are invented in this FFI layer. A non-numeral (symbolic FP
//! term, or a non-FP AST) decodes to `None`: the accessors then set
//! `Z3_INVALID_ARG` and return the null/false/0 sentinel rather than fabricate a
//! value. Matching Z3's split behavior exactly: `Z3_fpa_is_numeral` is a total
//! query that simply answers `false` for a non-numeral (no error), whereas the
//! category predicates (`is_numeral_nan/inf/zero/normal/subnormal/positive/
//! negative`) reject a non-numeral argument with `Z3_INVALID_ARG` (they still
//! answer plain `true`/`false` for a valid numeral of any category).
//!
//! NaN carries no meaningful sign, significand, or exponent, so — matching Z3,
//! which raises an error for NaN on every one of these accessors — the value
//! accessors (`get_numeral_sign(_bv)`, `get_numeral_significand_*`,
//! `get_numeral_exponent_*`) decline a NaN numeral with `Z3_INVALID_ARG`. The
//! `is_numeral_nan` predicate still reports `true`.
//!
//! # Z3 4.16 fidelity
//!
//! The decode ([`Solver::fp_numeral_decode`](ay_dpll::api::Solver::fp_numeral_decode))
//! extracts the raw IEEE-754 sign / biased-exponent / trailing-significand
//! fields and the IEEE value category; the accessors then render those fields
//! exactly as Z3 4.16's `mpf` accessors do. Rendering is category-aware so that
//! the special values match Z3 bit-for-bit (verified against Z3 4.16 for
//! Float16/32/64 over every category, reached both via the special-value
//! constructors and via `Z3_mk_fpa_numeral_double`):
//!   * significand string — normal `1 + sig/2^(sb-1)`, subnormal `sig/2^(sb-1)`,
//!     zero `"1"`, infinity `"0"` (Z3 keeps zero's `mpf` significand normalized
//!     to `1.0` and infinity's to `0`);
//!   * biased exponent — `exp_field` for finite values, `2^(eb-1)` for infinity
//!     (Z3's internal top-exponent);
//!   * unbiased exponent — normal `exp_field - bias`, subnormal `1 - bias` (the
//!     IEEE effective exponent `emin`), zero `0`, infinity `2^(eb-1)`;
//!   * sign / sign-bv / significand-bv / significand-uint64 read straight off the
//!     fields (`0` for the significand of zero and infinity, matching Z3).
//! No IEEE semantics are invented: the numbers are the number's own encoding.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via the
//! `ffi_guard_*` helpers so a panic cannot cross the `extern "C"` boundary.

use std::ffi::{c_char, c_uint};
use std::ptr;

use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};

use ay_dpll::api::Sort;

use super::{
    cache_string, ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_int, record_ast_sort,
    require_fpa_rounding_mode, require_term_ast, require_term_ast_or_return, term_to_ast,
    Z3Context, Z3_ast, Z3_context, Z3_sort, Z3_string, Z3_INVALID_ARG, Z3_SORT_ERROR,
};

/// Record an error code + message on the context and return the null AST sentinel.
fn ast_error(ctx: &mut Z3Context, code: c_uint, msg: impl Into<String>) -> Z3_ast {
    ctx.last_error = code;
    ctx.error_msg = Some(msg.into());
    0
}

/// Record an error code + message and return the null string sentinel.
fn str_error(ctx: &mut Z3Context, code: c_uint, msg: impl Into<String>) -> *const c_char {
    ctx.last_error = code;
    ctx.error_msg = Some(msg.into());
    ptr::null()
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
// Real / Int-Real -> FP constructors
// ============================================================================

/// Convert a Real value to an FP value: `((_ to_fp eb sb) rm t)`.
///
/// `rm` is a rounding mode, `t` a Real value, and `s` the target FloatingPoint
/// sort. Backed by [`ay_dpll::api::Solver::try_real_to_fp`]. The construction is
/// sound (well-typed symbolic term); because AY's FP solver bit-blasts, a solve
/// over a symbolic real may return `Z3_L_UNDEF` — orthogonal to construction.
/// Returns NULL + `Z3_SORT_ERROR` if `s` is not FP or `t` is not Real.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_fp_real(
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
                    "Z3_mk_fpa_to_fp_real: target sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_real", rm) else {
                return 0;
            };
            let Some(rt) = require_term_ast(ctx, t, "Z3_mk_fpa_to_fp_real", "real value") else {
                return 0;
            };
            if !matches!(ctx.solver.sort_of(rt), Sort::Real) {
                return ast_error(ctx, Z3_SORT_ERROR, "Z3_mk_fpa_to_fp_real: t must be a Real");
            }
            match ctx.solver.try_real_to_fp(rmt, rt, eb, sb) {
                Ok(x) => {
                    let a = term_to_ast(ctx, x);
                    record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
                    a
                }
                Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
            }
        })
    }
}

/// Convert an `(Int exponent, Real significand)` pair to FP:
/// `((_ to_fp eb sb) rm exp sig)` — Z3's real+int `to_fp` form; the value is
/// `round(sig * 2^exp)`.
///
/// `exp` must be Int-sorted and `sig` Real-sorted; `s` the target FloatingPoint
/// sort. Backed by [`ay_dpll::api::Solver::try_int_real_to_fp`]. Same
/// construction-soundness / solve-completeness characterization as
/// [`Z3_mk_fpa_to_fp_real`]. Returns NULL + `Z3_SORT_ERROR` on any sort
/// mismatch.
///
/// # Safety
/// `c` must be a valid context pointer; `s` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_fp_int_real(
    c: Z3_context,
    rm: Z3_ast,
    exp: Z3_ast,
    sig: Z3_ast,
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
                    "Z3_mk_fpa_to_fp_int_real: target sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_int_real", rm) else {
                return 0;
            };
            let Some(et) = require_term_ast(ctx, exp, "Z3_mk_fpa_to_fp_int_real", "exponent")
            else {
                return 0;
            };
            let Some(st) = require_term_ast(ctx, sig, "Z3_mk_fpa_to_fp_int_real", "significand")
            else {
                return 0;
            };
            if !matches!(ctx.solver.sort_of(et), Sort::Int) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_int_real: exp must be an Int",
                );
            }
            if !matches!(ctx.solver.sort_of(st), Sort::Real) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_int_real: sig must be a Real",
                );
            }
            match ctx.solver.try_int_real_to_fp(rmt, et, st, eb, sb) {
                Ok(x) => {
                    let a = term_to_ast(ctx, x);
                    record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
                    a
                }
                Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
            }
        })
    }
}

// ============================================================================
// is_numeral* predicates (total queries: false, no error, for non-numerals)
// ============================================================================

/// `true` iff `t` is a floating-point numeral (any of AY's three canonical FP
/// numeral shapes). Backed by `Solver::fp_numeral_decode(t).is_some()`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_is_numeral(c: Z3_context, t: Z3_ast) -> bool {
    if t == 0 {
        return false;
    }
    // SAFETY: `c` forwarded under the caller's contract; `ffi_guard_int`
    // null-checks it and catches panics at the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, t, "Z3_fpa_is_numeral", "term", 0);
            i32::from(ctx.solver.fp_numeral_decode(term).is_some())
        }) != 0
    }
}

/// Build a `is_numeral_<category>` predicate. For a valid FP numeral it applies
/// `pred` to the decoded value and returns the boolean (no error, even when
/// `false`). For a non-numeral it sets `Z3_INVALID_ARG` and returns `false` —
/// matching Z3, whose category predicates reject a non-numeral argument (unlike
/// the total `Z3_fpa_is_numeral`, which just answers `false`).
macro_rules! fpa_is_category {
    ($name:ident, $doc:literal, |$d:ident| $pred:expr) => {
        #[doc = $doc]
        ///
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t: Z3_ast) -> bool {
            if t == 0 {
                return false;
            }
            // SAFETY: `c` forwarded under the caller's contract.
            unsafe {
                ffi_guard_int(c, 0, |ctx| {
                    let Some(term) = require_term_ast(ctx, t, stringify!($name), "term") else {
                        return 0;
                    };
                    match ctx.solver.fp_numeral_decode(term) {
                        Some($d) => i32::from($pred),
                        None => {
                            ctx.last_error = Z3_INVALID_ARG;
                            ctx.error_msg = Some(
                                concat!(stringify!($name), ": t is not an FP numeral").to_string(),
                            );
                            0
                        }
                    }
                }) != 0
            }
        }
    };
}

fpa_is_category!(
    Z3_fpa_is_numeral_nan,
    "`true` iff `t` is a NaN FP numeral (exp all-ones, significand != 0).",
    |d| d.is_nan()
);
fpa_is_category!(
    Z3_fpa_is_numeral_inf,
    "`true` iff `t` is a +/-infinity FP numeral (exp all-ones, significand == 0).",
    |d| d.is_inf()
);
fpa_is_category!(
    Z3_fpa_is_numeral_zero,
    "`true` iff `t` is a +/-zero FP numeral (exp == 0, significand == 0).",
    |d| d.is_zero()
);
fpa_is_category!(
    Z3_fpa_is_numeral_normal,
    "`true` iff `t` is a normal FP numeral (0 < exp < all-ones).",
    |d| d.is_normal()
);
fpa_is_category!(
    Z3_fpa_is_numeral_subnormal,
    "`true` iff `t` is a subnormal FP numeral (exp == 0, significand != 0).",
    |d| d.is_subnormal()
);
fpa_is_category!(
    Z3_fpa_is_numeral_positive,
    "`true` iff `t` is a non-NaN FP numeral with the sign bit clear (Z3: NaN is \
     neither positive nor negative).",
    |d| !d.sign && !d.is_nan()
);
fpa_is_category!(
    Z3_fpa_is_numeral_negative,
    "`true` iff `t` is a non-NaN FP numeral with the sign bit set (-0 and -oo \
     count as negative, matching Z3).",
    |d| d.sign && !d.is_nan()
);

// ============================================================================
// Sign accessors
// ============================================================================

/// Write the sign bit of FP numeral `t` to `*sgn` (`false` = positive).
///
/// Returns `true` and writes for a non-NaN FP numeral. For a NaN numeral (no
/// meaningful sign) or a non-numeral, sets `Z3_INVALID_ARG`, returns `false`,
/// and does NOT write `*sgn` (no fabricated sign) — matching Z3, which errors on
/// NaN here.
///
/// # Safety
/// `c` must be a valid context pointer; `sgn` a valid `bool` out-pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_sign(c: Z3_context, t: Z3_ast, sgn: *mut bool) -> bool {
    if t == 0 || sgn.is_null() {
        return false;
    }
    // SAFETY: `c` forwarded under the caller's contract; `sgn` is null-checked and
    // written only on the success path within the guarded closure.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, t, "Z3_fpa_get_numeral_sign", "term", 0);
            match ctx.solver.fp_numeral_decode(term) {
                Some(d) if !d.is_nan() => {
                    *sgn = d.sign;
                    1
                }
                _ => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg =
                        Some("Z3_fpa_get_numeral_sign: t is not a non-NaN FP numeral".to_string());
                    0
                }
            }
        }) != 0
    }
}

/// Return the sign bit of FP numeral `t` as a 1-bit BitVec numeral.
///
/// Backed by `Solver::try_bv_const`. Returns NULL + `Z3_INVALID_ARG` if `t` is a
/// NaN or non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_sign_bv(c: Z3_context, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = require_term_ast_or_return!(ctx, t, "Z3_fpa_get_numeral_sign_bv", "term", 0);
            let Some(d) = ctx.solver.fp_numeral_decode(term) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_sign_bv: t is not an FP numeral",
                );
            };
            if d.is_nan() {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_sign_bv: sign is undefined for NaN",
                );
            }
            match ctx.solver.try_bv_const(i64::from(d.sign), 1) {
                Ok(bv) => {
                    let a = term_to_ast(ctx, bv);
                    record_ast_sort(ctx, a, Sort::bitvec(1));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

// ============================================================================
// Significand accessors
// ============================================================================

/// Return the `(sb-1)`-bit trailing-significand field of FP numeral `t` as a
/// BitVec numeral. Backed by `Solver::try_bv_const_bigint`. Returns NULL +
/// `Z3_INVALID_ARG` if `t` is a NaN or non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_significand_bv(c: Z3_context, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term =
                require_term_ast_or_return!(ctx, t, "Z3_fpa_get_numeral_significand_bv", "term", 0);
            let Some(d) = ctx.solver.fp_numeral_decode(term) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_significand_bv: t is not an FP numeral",
                );
            };
            if d.is_nan() {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_significand_bv: significand is undefined for NaN",
                );
            }
            let width = d.sb - 1;
            let val = BigInt::from(d.sig_field);
            match ctx.solver.try_bv_const_bigint(&val, width) {
                Ok(bv) => {
                    let a = term_to_ast(ctx, bv);
                    record_ast_sort(ctx, a, Sort::bitvec(width));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Write the `(sb-1)`-bit trailing-significand field of FP numeral `t` to `*n`.
///
/// Returns `true` only if `t` is a non-NaN FP numeral AND the field fits in 64
/// bits (Float128 has a 112-bit field that may not fit — then returns `false`
/// rather than truncate). Sets `Z3_INVALID_ARG` for a NaN/non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer; `n` a valid `uint64` out-pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_significand_uint64(
    c: Z3_context,
    t: Z3_ast,
    n: *mut u64,
) -> bool {
    if t == 0 || n.is_null() {
        return false;
    }
    // SAFETY: `c` forwarded under the caller's contract; `n` null-checked and
    // written only on the success path within the guarded closure.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                t,
                "Z3_fpa_get_numeral_significand_uint64",
                "term",
                0
            );
            match ctx.solver.fp_numeral_decode(term) {
                Some(d) if !d.is_nan() => match d.sig_field.to_u64() {
                    Some(v) => {
                        *n = v;
                        1
                    }
                    // Field wider than 64 bits: legitimate "does not fit" (not an
                    // invalid argument), so return false without truncating.
                    None => 0,
                },
                _ => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(
                        "Z3_fpa_get_numeral_significand_uint64: t is not a non-NaN FP numeral"
                            .to_string(),
                    );
                    0
                }
            }
        }) != 0
    }
}

/// Return the significand of FP numeral `t` as an exact decimal string in
/// `[0.0, 2.0)`.
///
/// For a value with the implicit leading bit present (`exp_field != 0`) the
/// significand is `1 + sig_field / 2^(sb-1)`; otherwise it is
/// `sig_field / 2^(sb-1)`. Both are dyadic rationals with a terminating decimal
/// expansion, computed exactly here. The returned string is owned by the
/// context. Returns NULL + `Z3_INVALID_ARG` if `t` is a NaN or non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_significand_string(
    c: Z3_context,
    t: Z3_ast,
) -> Z3_string {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                t,
                "Z3_fpa_get_numeral_significand_string",
                "term",
                ptr::null()
            );
            let Some(d) = ctx.solver.fp_numeral_decode(term) else {
                return str_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_significand_string: t is not an FP numeral",
                );
            };
            if d.is_nan() {
                return str_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_significand_string: significand is undefined for NaN",
                );
            }
            let s =
                fp_significand_decimal(&d.exp_field, &d.sig_field, d.sb, d.is_inf(), d.is_zero());
            cache_string(ctx, s)
        })
    }
}

// ============================================================================
// Exponent accessors
// ============================================================================

/// Return the exponent of FP numeral `t` as an `eb`-bit BitVec numeral.
///
/// The value (biased or unbiased) is the Z3 4.16 `mpf` exponent — see
/// `fp_exponent_value` for the exact per-category definition — reduced modulo
/// `2^eb` into the `eb`-bit result. Backed by `Solver::try_bv_const_bigint`.
/// Returns NULL + `Z3_INVALID_ARG` if `t` is a NaN or non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_exponent_bv(
    c: Z3_context,
    t: Z3_ast,
    biased: bool,
) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term =
                require_term_ast_or_return!(ctx, t, "Z3_fpa_get_numeral_exponent_bv", "term", 0);
            let Some(d) = ctx.solver.fp_numeral_decode(term) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_exponent_bv: t is not an FP numeral",
                );
            };
            if d.is_nan() {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_exponent_bv: exponent is undefined for NaN",
                );
            }
            let width = d.eb;
            let val = fp_exponent_value(
                &d.exp_field,
                d.eb,
                biased,
                d.is_inf(),
                d.is_zero(),
                d.is_subnormal(),
            );
            match ctx.solver.try_bv_const_bigint(&val, width) {
                Ok(bv) => {
                    let a = term_to_ast(ctx, bv);
                    record_ast_sort(ctx, a, Sort::bitvec(width));
                    a
                }
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Write the exponent of FP numeral `t` to `*n` as a signed 64-bit value.
///
/// The value (biased or unbiased) is the Z3 4.16 `mpf` exponent — see
/// `fp_exponent_value` for the exact per-category definition. Returns `true`
/// only if `t` is a non-NaN FP numeral AND the value fits in `i64`. Sets
/// `Z3_INVALID_ARG` for a NaN/non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer; `n` a valid `int64` out-pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_exponent_int64(
    c: Z3_context,
    t: Z3_ast,
    n: *mut i64,
    biased: bool,
) -> bool {
    if t == 0 || n.is_null() {
        return false;
    }
    // SAFETY: `c` forwarded under the caller's contract; `n` null-checked and
    // written only on the success path within the guarded closure.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term =
                require_term_ast_or_return!(ctx, t, "Z3_fpa_get_numeral_exponent_int64", "term", 0);
            match ctx.solver.fp_numeral_decode(term) {
                Some(d) if !d.is_nan() => {
                    let val = fp_exponent_value(
                        &d.exp_field,
                        d.eb,
                        biased,
                        d.is_inf(),
                        d.is_zero(),
                        d.is_subnormal(),
                    );
                    match val.to_i64() {
                        Some(v) => {
                            *n = v;
                            1
                        }
                        None => 0,
                    }
                }
                _ => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(
                        "Z3_fpa_get_numeral_exponent_int64: t is not a non-NaN FP numeral"
                            .to_string(),
                    );
                    0
                }
            }
        }) != 0
    }
}

/// Return the exponent of FP numeral `t` as a signed decimal string.
///
/// Same biased/unbiased value as [`Z3_fpa_get_numeral_exponent_int64`], but via
/// arbitrary-precision arithmetic so every width is exact. The returned string is
/// owned by the context. Returns NULL + `Z3_INVALID_ARG` if `t` is a NaN or
/// non-numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_fpa_get_numeral_exponent_string(
    c: Z3_context,
    t: Z3_ast,
    biased: bool,
) -> Z3_string {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                t,
                "Z3_fpa_get_numeral_exponent_string",
                "term",
                ptr::null()
            );
            let Some(d) = ctx.solver.fp_numeral_decode(term) else {
                return str_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_exponent_string: t is not an FP numeral",
                );
            };
            if d.is_nan() {
                return str_error(
                    ctx,
                    Z3_INVALID_ARG,
                    "Z3_fpa_get_numeral_exponent_string: exponent is undefined for NaN",
                );
            }
            let val = fp_exponent_value(
                &d.exp_field,
                d.eb,
                biased,
                d.is_inf(),
                d.is_zero(),
                d.is_subnormal(),
            );
            cache_string(ctx, val.to_str_radix(10))
        })
    }
}

// ============================================================================
// Pure field -> decimal helpers (Z3 4.16-faithful, category-aware)
// ============================================================================

/// Significand value as a decimal string in `[0.0, 2.0)`, matching Z3 4.16.
///
/// * infinity -> `"0"` and zero -> `"1"` reproduce Z3's `mpf` renderings of
///   those special values exactly (Z3 keeps zero's significand normalized to
///   `1.0` and infinity's to `0`);
/// * a normal value (implicit leading bit present) is `1 + sig_field/2^(sb-1)`;
/// * a subnormal value (no leading bit) is `sig_field/2^(sb-1)`.
///
/// NaN is handled by the caller (declined), so it never reaches here.
fn fp_significand_decimal(
    exp_field: &BigUint,
    sig_field: &BigUint,
    sb: u32,
    is_inf: bool,
    is_zero: bool,
) -> String {
    if is_inf {
        return "0".to_string();
    }
    if is_zero {
        return "1".to_string();
    }
    let sb1 = (sb - 1) as usize;
    // Remaining categories are normal / subnormal: the implicit leading bit is
    // present iff the biased exponent field is nonzero.
    let numer = if exp_field.is_zero() {
        sig_field.clone()
    } else {
        (BigUint::from(1u8) << sb1) + sig_field
    };
    dyadic_to_decimal(&numer, sb1)
}

/// Exact decimal expansion of the dyadic rational `numer / 2^k`.
///
/// `numer / 2^k == numer * 5^k / 10^k`, so the fractional part is exact and
/// terminating. Trailing zeros are stripped; an integral value returns just the
/// integer part.
fn dyadic_to_decimal(numer: &BigUint, k: usize) -> String {
    if k == 0 {
        return numer.to_str_radix(10);
    }
    let k32 = k as u32;
    let five_k = BigUint::from(5u8).pow(k32);
    let ten_k = BigUint::from(10u8).pow(k32);
    let scaled = numer * &five_k;
    let int_part = (&scaled / &ten_k).to_str_radix(10);
    let frac = &scaled % &ten_k;
    if frac.is_zero() {
        return int_part;
    }
    // Zero-pad the fractional digits to width `k`, then strip trailing zeros.
    let frac_digits = frac.to_str_radix(10);
    let pad = k.saturating_sub(frac_digits.len());
    let mut frac_str = String::with_capacity(k);
    for _ in 0..pad {
        frac_str.push('0');
    }
    frac_str.push_str(&frac_digits);
    let trimmed = frac_str.trim_end_matches('0');
    format!("{int_part}.{trimmed}")
}

/// The exponent value, matching Z3 4.16's `mpf` accessor exactly.
///
/// * infinity -> `2^(eb-1)` for BOTH biased and unbiased (Z3's internal
///   top-exponent);
/// * zero -> `0` for both;
/// * subnormal -> biased `0`, unbiased `1 - bias` (the IEEE effective exponent
///   `emin`);
/// * normal -> biased `exp_field`, unbiased `exp_field - bias`;
///
/// with `bias = 2^(eb-1) - 1`. NaN is declined by the caller and never reaches
/// here.
fn fp_exponent_value(
    exp_field: &BigUint,
    eb: u32,
    biased: bool,
    is_inf: bool,
    is_zero: bool,
    is_subnormal: bool,
) -> BigInt {
    let top = BigInt::from(1) << ((eb - 1) as usize); // 2^(eb-1)
    if is_inf {
        return top;
    }
    if is_zero {
        return BigInt::from(0);
    }
    if biased {
        // normal -> exp_field; subnormal -> 0 (its exp_field is already 0).
        BigInt::from(exp_field.clone())
    } else {
        let bias = &top - BigInt::from(1);
        if is_subnormal {
            BigInt::from(1) - bias
        } else {
            BigInt::from(exp_field.clone()) - bias
        }
    }
}
