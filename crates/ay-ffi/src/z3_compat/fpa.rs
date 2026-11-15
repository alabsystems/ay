// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible floating-point (IEEE-754 / FPA) C API (#phase3-fpa).
//!
//! These wire Z3's `Z3_mk_fpa_*` constructors onto AY's native floating-point
//! theory. Every function delegates to a PROVEN-CORRECT `ay_dpll::api::Solver`
//! FP builder (`try_fp_*`, `try_bv_to_fp*`, `try_fp_to_fp`, ...) — the exact
//! same constructors AY's SMT-LIB elaborator and model reconstruction use (see
//! `crates/ay-dpll/src/api/floating_point.rs`,
//! `crates/ay-dpll/src/api/floating_point_conv.rs`, and
//! `crates/ay-ffi/src/z3_compat/model_params.rs`).
//!
//! # Soundness
//!
//! NO FP semantics are invented in this FFI layer: an FFI function only builds
//! the operand terms and forwards to the core builder, recording the resulting
//! sort. The IEEE-754 meaning (rounding, NaN/inf/zero, bit-blasting) is entirely
//! the core's. When an operation is requested with operands the core rejects
//! (sort mismatch, mixed precision, unsupported width), the function returns the
//! null sentinel and records `Z3_SORT_ERROR`/`Z3_INVALID_ARG` rather than
//! fabricating an ill-typed or wrong term.
//!
//! # Rounding modes
//!
//! In Z3 a rounding mode is a value of the dedicated `RoundingMode` sort. AY's
//! core models a rounding mode as a named nullary application (`RNE`, `RNA`,
//! `RTP`, `RTN`, `RTZ`) recognized by the FP solver. We expose the five Z3
//! rounding-mode constructors (with both the spelled-out and short aliases) and
//! a `Z3_mk_fpa_rounding_mode_sort` for API completeness.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via the
//! `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_double, c_int, c_uint};

use ay_dpll::api::{Sort, Term};

use super::{
    alloc_sort, ffi_guard_mk, ffi_guard_ptr, mk_ast, require_ast, require_fpa_rounding_mode,
    Z3Context, Z3_ast, Z3_context, Z3_sort, MAX_FFI_BITVECTOR_WIDTH, MAX_FFI_FP_EXPONENT_BITS,
    Z3_INVALID_ARG, Z3_SORT_ERROR,
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
// FP sorts
// ============================================================================

/// Create a floating-point sort `(_ FloatingPoint ebits sbits)`.
///
/// `ebits` is the exponent width and `sbits` is the significand width INCLUDING
/// the hidden bit (exactly as Z3's `Z3_mk_fpa_sort`). Backed by
/// [`Sort::FloatingPoint`]. Returns NULL + `Z3_INVALID_ARG` if either width is
/// outside AY's representable dense-bitblasting envelope.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort(c: Z3_context, ebits: c_uint, sbits: c_uint) -> Z3_sort {
    // SAFETY: `c` is forwarded under the caller's contract; `ffi_guard_ptr`
    // null-checks it and catches panics at the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !(2..=MAX_FFI_FP_EXPONENT_BITS).contains(&ebits)
                || !(2..=MAX_FFI_BITVECTOR_WIDTH).contains(&sbits)
            {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_fpa_sort: widths outside supported ranges: ebits={ebits} (2..={MAX_FFI_FP_EXPONENT_BITS}), sbits={sbits} (2..={MAX_FFI_BITVECTOR_WIDTH})"
                ));
                return std::ptr::null_mut();
            }
            alloc_sort(ctx, Sort::FloatingPoint(ebits, sbits))
        })
    }
}

/// Create the half-precision (16-bit) FP sort: `(_ FloatingPoint 5 11)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_half(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is live by caller contract; `Z3_mk_fpa_sort` null-checks it,
    // and these fixed format widths satisfy its validated bounds.
    unsafe { Z3_mk_fpa_sort(c, 5, 11) }
}

/// Create the single-precision (32-bit) FP sort: `(_ FloatingPoint 8 24)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_single(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is live by caller contract; `Z3_mk_fpa_sort` null-checks it,
    // and these fixed format widths satisfy its validated bounds.
    unsafe { Z3_mk_fpa_sort(c, 8, 24) }
}

/// Create the double-precision (64-bit) FP sort: `(_ FloatingPoint 11 53)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_double(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is live by caller contract; `Z3_mk_fpa_sort` null-checks it,
    // and these fixed format widths satisfy its validated bounds.
    unsafe { Z3_mk_fpa_sort(c, 11, 53) }
}

/// Create the quadruple-precision (128-bit) FP sort: `(_ FloatingPoint 15 113)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_quadruple(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is live by caller contract; `Z3_mk_fpa_sort` null-checks it,
    // and these fixed format widths satisfy its validated bounds.
    unsafe { Z3_mk_fpa_sort(c, 15, 113) }
}

/// Create the `RoundingMode` sort.
///
/// AY does not have a dedicated `RoundingMode` sort kind — rounding-mode values
/// are named nullary terms recognized by the FP solver (see
/// [`Z3_mk_fpa_round_nearest_ties_to_even`] etc.). For API compatibility this
/// returns a sentinel uninterpreted sort named `RoundingMode`; it is only useful
/// as a sort handle (e.g. declaring a rounding-mode constant), and the rounding
/// modes consumed by FP operations are built by the dedicated constructors.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_rounding_mode_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is live by caller contract; `ffi_guard_ptr` handles a null
    // pointer defensively before allocating the context-owned sentinel sort.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            alloc_sort(ctx, Sort::Uninterpreted("RoundingMode".to_string()))
        })
    }
}

// ============================================================================
// Rounding-mode constants
// ============================================================================

/// Build a rounding-mode term from its SMT-LIB short name, recording the sort.
///
/// Backed by [`ay_dpll::api::Solver::try_fp_rounding_mode`].
fn mk_rm(ctx: &mut Z3Context, name: &str) -> Z3_ast {
    match ctx.solver.try_fp_rounding_mode(name) {
        // The rounding-mode term is reported as the RoundingMode sort so a
        // consumer that queries its sort sees a coherent answer.
        Ok(t) => mk_ast(ctx, t, Sort::Uninterpreted("RoundingMode".to_string())),
        Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
    }
}

macro_rules! fpa_rounding_mode {
    ($name:ident, $rm:literal, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context) -> Z3_ast {
            // SAFETY: `c` forwarded under the caller's contract; `ffi_guard_ast`
            // null-checks it and catches panics at the FFI boundary.
            unsafe { ffi_guard_mk(c, stringify!($name), |ctx| mk_rm(ctx, $rm)) }
        }
    };
}

fpa_rounding_mode!(
    Z3_mk_fpa_round_nearest_ties_to_even,
    "RNE",
    "Rounding mode: round to nearest, ties to even (`roundNearestTiesToEven`)."
);
fpa_rounding_mode!(
    Z3_mk_fpa_rne,
    "RNE",
    "Alias for `Z3_mk_fpa_round_nearest_ties_to_even`."
);
fpa_rounding_mode!(
    Z3_mk_fpa_round_nearest_ties_to_away,
    "RNA",
    "Rounding mode: round to nearest, ties away from zero (`roundNearestTiesToAway`)."
);
fpa_rounding_mode!(
    Z3_mk_fpa_rna,
    "RNA",
    "Alias for `Z3_mk_fpa_round_nearest_ties_to_away`."
);
fpa_rounding_mode!(
    Z3_mk_fpa_round_toward_positive,
    "RTP",
    "Rounding mode: round toward positive infinity (`roundTowardPositive`)."
);
fpa_rounding_mode!(
    Z3_mk_fpa_rtp,
    "RTP",
    "Alias for `Z3_mk_fpa_round_toward_positive`."
);
fpa_rounding_mode!(
    Z3_mk_fpa_round_toward_negative,
    "RTN",
    "Rounding mode: round toward negative infinity (`roundTowardNegative`)."
);
fpa_rounding_mode!(
    Z3_mk_fpa_rtn,
    "RTN",
    "Alias for `Z3_mk_fpa_round_toward_negative`."
);
fpa_rounding_mode!(
    Z3_mk_fpa_round_toward_zero,
    "RTZ",
    "Rounding mode: round toward zero (`roundTowardZero`)."
);
fpa_rounding_mode!(
    Z3_mk_fpa_rtz,
    "RTZ",
    "Alias for `Z3_mk_fpa_round_toward_zero`."
);

// ============================================================================
// FP constants / literals
// ============================================================================

/// Create the NaN constant of the given FP sort.
///
/// Backed by [`ay_dpll::api::Solver::try_fp_nan`].
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_nan(c: Z3_context, sort: Z3_sort) -> Z3_ast {
    // SAFETY: `sort` is read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(sort) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_mk(c, "Z3_mk_fpa_nan", |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_nan: sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract; `ffi_guard_ast`
    // null-checks it and catches panics at the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_nan", |ctx| {
            match ctx.solver.try_fp_nan(eb, sb) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Create a +/-infinity constant of the given FP sort.
///
/// `negative != 0` selects -oo, otherwise +oo. Backed by
/// [`ay_dpll::api::Solver::try_fp_plus_infinity`] /
/// [`ay_dpll::api::Solver::try_fp_minus_infinity`].
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_inf(c: Z3_context, sort: Z3_sort, negative: bool) -> Z3_ast {
    // SAFETY: `sort` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(sort) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_mk(c, "Z3_mk_fpa_inf", |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_inf: sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_inf", |ctx| {
            let result = if negative {
                ctx.solver.try_fp_minus_infinity(eb, sb)
            } else {
                ctx.solver.try_fp_plus_infinity(eb, sb)
            };
            match result {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Create a +/-zero constant of the given FP sort.
///
/// `negative != 0` selects -zero, otherwise +zero. Backed by
/// [`ay_dpll::api::Solver::try_fp_plus_zero`] /
/// [`ay_dpll::api::Solver::try_fp_minus_zero`].
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_zero(c: Z3_context, sort: Z3_sort, negative: bool) -> Z3_ast {
    // SAFETY: `sort` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(sort) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_mk(c, "Z3_mk_fpa_zero", |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_zero: sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_zero", |ctx| {
            let result = if negative {
                ctx.solver.try_fp_minus_zero(eb, sb)
            } else {
                ctx.solver.try_fp_plus_zero(eb, sb)
            };
            match result {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Round a C `double` once into any admitted FP format, using exact arithmetic.
///
/// IEEE 754 round-to-nearest, ties-to-even is delegated to the FP theory's
/// rational converter. Decode the double exactly rather than rounding through
/// an intermediate float, which would double-round narrow/custom formats.
/// Signed zero and non-finite values are assembled directly because rationals
/// cannot represent them. The format bounds are the same as `Z3_mk_fpa_sort`.
pub(crate) fn f64_to_fp_bits(value: f64, eb: u32, sb: u32) -> Option<num_bigint::BigInt> {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    if !(2..=MAX_FFI_FP_EXPONENT_BITS).contains(&eb) || !(2..=MAX_FFI_BITVECTOR_WIDTH).contains(&sb)
    {
        return None;
    }
    match (eb, sb) {
        (8, 24) => return Some(BigInt::from((value as f32).to_bits())),
        (11, 53) => return Some(BigInt::from(value.to_bits())),
        _ => {}
    }
    let sign = BigInt::from(u8::from(value.is_sign_negative())) << (eb + sb - 1);
    if value.is_nan() || value.is_infinite() {
        let exponent = ((BigInt::from(1) << eb) - 1) << (sb - 1);
        return Some(sign + exponent + BigInt::from(u8::from(value.is_nan())));
    }
    if value == 0.0 {
        return Some(sign);
    }
    let rational = BigRational::from_float(value)?;
    Some(ay_fp::round_rational_to_ieee_bits(
        &rational,
        eb,
        sb,
        ay_fp::RoundingMode::RNE,
    ))
}

/// Create an FP numeral from a C `double`, rounded to the given FP sort.
///
/// Supports custom precisions and binary128 within the native FP construction
/// envelope. Finite doubles are converted to an exact rational
/// and rounded once; signed zero, NaN and infinities retain their FP meaning.
/// The resulting `(fp ...)` term uses the native FP bit-pattern constructor.
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_numeral_double(
    c: Z3_context,
    value: c_double,
    sort: Z3_sort,
) -> Z3_ast {
    // SAFETY: `sort` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(sort) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_mk(c, "Z3_mk_fpa_numeral_double", |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_numeral_double: sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_numeral_double", |ctx| {
            let Some(bits) = f64_to_fp_bits(value, eb, sb) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!("Z3_mk_fpa_numeral_double: invalid FP format ({eb}, {sb})"),
                );
            };
            match ctx.solver.try_fp_const_from_bits_bigint(&bits, eb, sb) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Create an FP numeral from a C `int`, rounded to the given FP sort.
///
/// Convenience wrapper over [`Z3_mk_fpa_numeral_double`]: the integer is widened
/// to `double` (exact for the magnitudes representable in `f64`) and rounded into
/// the FP format. Same supported precisions and error behavior.
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_numeral_int(
    c: Z3_context,
    value: c_int,
    sort: Z3_sort,
) -> Z3_ast {
    // SAFETY: forwards to Z3_mk_fpa_numeral_double under the same caller contract.
    unsafe { Z3_mk_fpa_numeral_double(c, f64::from(value), sort) }
}

// ============================================================================
// FP unary operations (abs, neg)
// ============================================================================

/// Build a unary FP op, validating the operand sort and recording the result sort.
fn fpa_unary(
    ctx: &mut Z3Context,
    op: &'static str,
    a: Z3_ast,
    build: impl FnOnce(&mut Z3Context, Term) -> Result<Term, ay_dpll::api::SolverError>,
) -> Z3_ast {
    let Some(at) = require_ast(ctx, a, op, "operand").map(|decoded| decoded.term) else {
        return 0;
    };
    let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operand must be FloatingPoint"),
        );
    };
    match build(ctx, at) {
        Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
        Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
    }
}

/// Create FP absolute value `(fp.abs t)`. Backed by `Solver::try_fp_abs`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_abs(c: Z3_context, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_abs", |ctx| {
            fpa_unary(ctx, "fp.abs", t, |ctx, a| ctx.solver.try_fp_abs(a))
        })
    }
}

/// Create FP negation `(fp.neg t)`. Backed by `Solver::try_fp_neg`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_neg(c: Z3_context, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_neg", |ctx| {
            fpa_unary(ctx, "fp.neg", t, |ctx, a| ctx.solver.try_fp_neg(a))
        })
    }
}

// ============================================================================
// FP rounded binary arithmetic (add, sub, mul, div) — take a rounding mode
// ============================================================================

/// Build a rounded binary FP op `(op rm a b)`, recording the FP result sort.
fn fpa_rm_binary(
    ctx: &mut Z3Context,
    op: &'static str,
    rm: Z3_ast,
    a: Z3_ast,
    b: Z3_ast,
    build: impl FnOnce(&mut Z3Context, Term, Term, Term) -> Result<Term, ay_dpll::api::SolverError>,
) -> Z3_ast {
    let Some(rmt) = require_fpa_rounding_mode(ctx, op, rm) else {
        return 0;
    };
    let Some(at) = require_ast(ctx, a, op, "left operand").map(|decoded| decoded.term) else {
        return 0;
    };
    let Some(bt) = require_ast(ctx, b, op, "right operand").map(|decoded| decoded.term) else {
        return 0;
    };
    let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operands must be FloatingPoint"),
        );
    };
    match build(ctx, rmt, at, bt) {
        Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
        Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
    }
}

macro_rules! fpa_rm_binary_op {
    ($name:ident, $op:literal, $method:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(
            c: Z3_context,
            rm: Z3_ast,
            t1: Z3_ast,
            t2: Z3_ast,
        ) -> Z3_ast {
            // SAFETY: `c` forwarded under the caller's contract.
            unsafe {
                ffi_guard_mk(c, stringify!($name), |ctx| {
                    fpa_rm_binary(ctx, $op, rm, t1, t2, |ctx, rm, a, b| {
                        ctx.solver.$method(rm, a, b)
                    })
                })
            }
        }
    };
}

fpa_rm_binary_op!(
    Z3_mk_fpa_add,
    "fp.add",
    try_fp_add,
    "Create FP addition `(fp.add rm a b)`."
);
fpa_rm_binary_op!(
    Z3_mk_fpa_sub,
    "fp.sub",
    try_fp_sub,
    "Create FP subtraction `(fp.sub rm a b)`."
);
fpa_rm_binary_op!(
    Z3_mk_fpa_mul,
    "fp.mul",
    try_fp_mul,
    "Create FP multiplication `(fp.mul rm a b)`."
);
fpa_rm_binary_op!(
    Z3_mk_fpa_div,
    "fp.div",
    try_fp_div,
    "Create FP division `(fp.div rm a b)`."
);

/// Create FP fused multiply-add `(fp.fma rm a b c)` = round(a*b + c).
///
/// Backed by `Solver::try_fp_fma`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_fma(
    c: Z3_context,
    rm: Z3_ast,
    t1: Z3_ast,
    t2: Z3_ast,
    t3: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_fma", |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "fp.fma", rm) else {
                return 0;
            };
            let Some(at) =
                require_ast(ctx, t1, "fp.fma", "first operand").map(|decoded| decoded.term)
            else {
                return 0;
            };
            let Some(bt) =
                require_ast(ctx, t2, "fp.fma", "second operand").map(|decoded| decoded.term)
            else {
                return 0;
            };
            let Some(ct) =
                require_ast(ctx, t3, "fp.fma", "third operand").map(|decoded| decoded.term)
            else {
                return 0;
            };
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
                return ast_error(ctx, Z3_SORT_ERROR, "fp.fma: operands must be FloatingPoint");
            };
            match ctx.solver.try_fp_fma(rmt, at, bt, ct) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
            }
        })
    }
}

/// Create FP square root `(fp.sqrt rm a)`. Backed by `Solver::try_fp_sqrt`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sqrt(c: Z3_context, rm: Z3_ast, t: Z3_ast) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_sqrt", |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "fp.sqrt", rm) else {
                return 0;
            };
            let Some(at) = require_ast(ctx, t, "fp.sqrt", "operand").map(|decoded| decoded.term)
            else {
                return 0;
            };
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
                return ast_error(ctx, Z3_SORT_ERROR, "fp.sqrt: operand must be FloatingPoint");
            };
            match ctx.solver.try_fp_sqrt(rmt, at) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Create FP round-to-integral `(fp.roundToIntegral rm a)`.
///
/// Backed by `Solver::try_fp_round_to_integral`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_round_to_integral(
    c: Z3_context,
    rm: Z3_ast,
    t: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_round_to_integral", |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "fp.roundToIntegral", rm) else {
                return 0;
            };
            let Some(at) =
                require_ast(ctx, t, "fp.roundToIntegral", "operand").map(|decoded| decoded.term)
            else {
                return 0;
            };
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "fp.roundToIntegral: operand must be FloatingPoint",
                );
            };
            match ctx.solver.try_fp_round_to_integral(rmt, at) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

// ============================================================================
// FP binary arithmetic without a rounding mode (rem, min, max)
// ============================================================================

/// Build a non-rounded binary FP op `(op a b)`, recording the FP result sort.
fn fpa_binary(
    ctx: &mut Z3Context,
    op: &'static str,
    a: Z3_ast,
    b: Z3_ast,
    build: impl FnOnce(&mut Z3Context, Term, Term) -> Result<Term, ay_dpll::api::SolverError>,
) -> Z3_ast {
    let Some(at) = require_ast(ctx, a, op, "left operand").map(|decoded| decoded.term) else {
        return 0;
    };
    let Some(bt) = require_ast(ctx, b, op, "right operand").map(|decoded| decoded.term) else {
        return 0;
    };
    let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operands must be FloatingPoint"),
        );
    };
    match build(ctx, at, bt) {
        Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
        Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
    }
}

macro_rules! fpa_binary_op {
    ($name:ident, $op:literal, $method:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
            // SAFETY: `c` forwarded under the caller's contract.
            unsafe {
                ffi_guard_mk(c, stringify!($name), |ctx| {
                    fpa_binary(ctx, $op, t1, t2, |ctx, a, b| ctx.solver.$method(a, b))
                })
            }
        }
    };
}

fpa_binary_op!(
    Z3_mk_fpa_rem,
    "fp.rem",
    try_fp_rem,
    "Create IEEE FP remainder `(fp.rem a b)`."
);
fpa_binary_op!(
    Z3_mk_fpa_min,
    "fp.min",
    try_fp_min,
    "Create FP minimum `(fp.min a b)`."
);
fpa_binary_op!(
    Z3_mk_fpa_max,
    "fp.max",
    try_fp_max,
    "Create FP maximum `(fp.max a b)`."
);

// ============================================================================
// FP comparison predicates (return Bool)
// ============================================================================

/// Build a binary FP predicate `(op a b)` returning a Bool, recording Bool sort.
fn fpa_pred_binary(
    ctx: &mut Z3Context,
    op: &'static str,
    a: Z3_ast,
    b: Z3_ast,
    build: impl FnOnce(&mut Z3Context, Term, Term) -> Result<Term, ay_dpll::api::SolverError>,
) -> Z3_ast {
    let Some(at) = require_ast(ctx, a, op, "left operand").map(|decoded| decoded.term) else {
        return 0;
    };
    let Some(bt) = require_ast(ctx, b, op, "right operand").map(|decoded| decoded.term) else {
        return 0;
    };
    if !matches!(ctx.solver.sort_of(at), Sort::FloatingPoint(_, _)) {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operands must be FloatingPoint"),
        );
    }
    match build(ctx, at, bt) {
        Ok(t) => mk_ast(ctx, t, Sort::Bool),
        Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
    }
}

macro_rules! fpa_pred_op {
    ($name:ident, $op:literal, $method:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
            // SAFETY: `c` forwarded under the caller's contract.
            unsafe {
                ffi_guard_mk(c, stringify!($name), |ctx| {
                    fpa_pred_binary(ctx, $op, t1, t2, |ctx, a, b| ctx.solver.$method(a, b))
                })
            }
        }
    };
}

fpa_pred_op!(
    Z3_mk_fpa_eq,
    "fp.eq",
    try_fp_eq,
    "Create FP IEEE equality `(fp.eq a b)` (Bool)."
);
fpa_pred_op!(
    Z3_mk_fpa_lt,
    "fp.lt",
    try_fp_lt,
    "Create FP less-than `(fp.lt a b)` (Bool)."
);
fpa_pred_op!(
    Z3_mk_fpa_leq,
    "fp.leq",
    try_fp_le,
    "Create FP less-than-or-equal `(fp.leq a b)` (Bool)."
);
fpa_pred_op!(
    Z3_mk_fpa_gt,
    "fp.gt",
    try_fp_gt,
    "Create FP greater-than `(fp.gt a b)` (Bool)."
);
fpa_pred_op!(
    Z3_mk_fpa_geq,
    "fp.geq",
    try_fp_ge,
    "Create FP greater-than-or-equal `(fp.geq a b)` (Bool)."
);

// ============================================================================
// FP classification predicates (return Bool)
// ============================================================================

/// Build a unary FP classification predicate `(op a)` returning a Bool.
fn fpa_pred_unary(
    ctx: &mut Z3Context,
    op: &'static str,
    a: Z3_ast,
    build: impl FnOnce(&mut Z3Context, Term) -> Result<Term, ay_dpll::api::SolverError>,
) -> Z3_ast {
    let Some(at) = require_ast(ctx, a, op, "operand").map(|decoded| decoded.term) else {
        return 0;
    };
    if !matches!(ctx.solver.sort_of(at), Sort::FloatingPoint(_, _)) {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operand must be FloatingPoint"),
        );
    }
    match build(ctx, at) {
        Ok(t) => mk_ast(ctx, t, Sort::Bool),
        Err(e) => ast_error(ctx, Z3_SORT_ERROR, format!("{e}")),
    }
}

macro_rules! fpa_class_op {
    ($name:ident, $op:literal, $method:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t: Z3_ast) -> Z3_ast {
            // SAFETY: `c` forwarded under the caller's contract.
            unsafe {
                ffi_guard_mk(c, stringify!($name), |ctx| {
                    fpa_pred_unary(ctx, $op, t, |ctx, a| ctx.solver.$method(a))
                })
            }
        }
    };
}

fpa_class_op!(
    Z3_mk_fpa_is_nan,
    "fp.isNaN",
    try_fp_is_nan,
    "Create FP `(fp.isNaN a)` (Bool)."
);
fpa_class_op!(
    Z3_mk_fpa_is_infinite,
    "fp.isInfinite",
    try_fp_is_infinite,
    "Create FP `(fp.isInfinite a)` (Bool)."
);
fpa_class_op!(
    Z3_mk_fpa_is_zero,
    "fp.isZero",
    try_fp_is_zero,
    "Create FP `(fp.isZero a)` (Bool)."
);
fpa_class_op!(
    Z3_mk_fpa_is_normal,
    "fp.isNormal",
    try_fp_is_normal,
    "Create FP `(fp.isNormal a)` (Bool)."
);
fpa_class_op!(
    Z3_mk_fpa_is_subnormal,
    "fp.isSubnormal",
    try_fp_is_subnormal,
    "Create FP `(fp.isSubnormal a)` (Bool)."
);
fpa_class_op!(
    Z3_mk_fpa_is_negative,
    "fp.isNegative",
    try_fp_is_negative,
    "Create FP `(fp.isNegative a)` (Bool)."
);
fpa_class_op!(
    Z3_mk_fpa_is_positive,
    "fp.isPositive",
    try_fp_is_positive,
    "Create FP `(fp.isPositive a)` (Bool)."
);

// ============================================================================
// Conversions
// ============================================================================

/// Convert one FP value to another FP precision: `((_ to_fp eb sb) rm t)`.
///
/// `t` must be a FloatingPoint value and `sort` a FloatingPoint sort. Backed by
/// [`ay_dpll::api::Solver::try_fp_to_fp`].
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_fp_float(
    c: Z3_context,
    rm: Z3_ast,
    t: Z3_ast,
    sort: Z3_sort,
) -> Z3_ast {
    // SAFETY: `sort` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(sort) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_mk(c, "Z3_mk_fpa_to_fp_float", |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_float: target sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_to_fp_float", |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_float", rm) else {
                return 0;
            };
            let Some(ft) = require_ast(ctx, t, "Z3_mk_fpa_to_fp_float", "floating-point value")
                .map(|decoded| decoded.term)
            else {
                return 0;
            };
            if !matches!(ctx.solver.sort_of(ft), Sort::FloatingPoint(_, _)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_float: value must be a FloatingPoint",
                );
            }
            match ctx.solver.try_fp_to_fp(rmt, ft, eb, sb) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

/// Convert a signed bitvector to an FP value: `((_ to_fp eb sb) rm bv)`.
///
/// `t` must be a BitVec value and `sort` a FloatingPoint sort. Backed by
/// [`ay_dpll::api::Solver::try_bv_to_fp`].
///
/// # Safety
/// `c` must be a valid context pointer; `sort` a valid FP sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_to_fp_signed(
    c: Z3_context,
    rm: Z3_ast,
    t: Z3_ast,
    sort: Z3_sort,
) -> Z3_ast {
    // SAFETY: `sort` read under the single-threaded-per-context contract.
    let Some((eb, sb)) = (unsafe { fp_sort_params(sort) }) else {
        // SAFETY: `c` forwarded under the caller's contract.
        return unsafe {
            ffi_guard_mk(c, "Z3_mk_fpa_to_fp_signed", |ctx| {
                ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_signed: target sort must be a FloatingPoint sort",
                )
            })
        };
    };
    // SAFETY: `c` forwarded under the caller's contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_fpa_to_fp_signed", |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_signed", rm) else {
                return 0;
            };
            let Some(bvt) = require_ast(ctx, t, "Z3_mk_fpa_to_fp_signed", "bit-vector value")
                .map(|decoded| decoded.term)
            else {
                return 0;
            };
            if !matches!(ctx.solver.sort_of(bvt), Sort::BitVec(_)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_signed: value must be a BitVec",
                );
            }
            match ctx.solver.try_bv_to_fp(rmt, bvt, eb, sb) {
                Ok(t) => mk_ast(ctx, t, Sort::FloatingPoint(eb, sb)),
                Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
            }
        })
    }
}

#[cfg(test)]
#[path = "fpa_tests.rs"]
mod fpa_tests;
