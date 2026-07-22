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
    alloc_sort, ast_to_term, ffi_guard_ast, ffi_guard_ptr, record_ast_sort,
    require_fpa_rounding_mode, term_to_ast, Z3Context, Z3_ast, Z3_context, Z3_sort,
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
    // SAFETY: see Z3_mk_fpa_sort.
    unsafe { Z3_mk_fpa_sort(c, 5, 11) }
}

/// Create the single-precision (32-bit) FP sort: `(_ FloatingPoint 8 24)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_single(c: Z3_context) -> Z3_sort {
    // SAFETY: see Z3_mk_fpa_sort.
    unsafe { Z3_mk_fpa_sort(c, 8, 24) }
}

/// Create the double-precision (64-bit) FP sort: `(_ FloatingPoint 11 53)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_double(c: Z3_context) -> Z3_sort {
    // SAFETY: see Z3_mk_fpa_sort.
    unsafe { Z3_mk_fpa_sort(c, 11, 53) }
}

/// Create the quadruple-precision (128-bit) FP sort: `(_ FloatingPoint 15 113)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fpa_sort_quadruple(c: Z3_context) -> Z3_sort {
    // SAFETY: see Z3_mk_fpa_sort.
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
    // SAFETY: see Z3_mk_fpa_sort.
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
        Ok(t) => {
            let a = term_to_ast(t);
            // The rounding-mode term is reported as the RoundingMode sort so a
            // consumer that queries its sort sees a coherent answer.
            record_ast_sort(ctx, a, Sort::Uninterpreted("RoundingMode".to_string()));
            a
        }
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
            unsafe { ffi_guard_ast(c, |ctx| mk_rm(ctx, $rm)) }
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
            ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| match ctx.solver.try_fp_nan(eb, sb) {
            Ok(t) => {
                let a = term_to_ast(t);
                record_ast_sort(ctx, a, Sort::FloatingPoint(eb, sb));
                a
            }
            Err(e) => ast_error(ctx, Z3_INVALID_ARG, format!("{e}")),
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
            ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
            let result = if negative {
                ctx.solver.try_fp_minus_infinity(eb, sb)
            } else {
                ctx.solver.try_fp_plus_infinity(eb, sb)
            };
            match result {
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
            ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
            let result = if negative {
                ctx.solver.try_fp_minus_zero(eb, sb)
            } else {
                ctx.solver.try_fp_plus_zero(eb, sb)
            };
            match result {
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

/// Encode a C `double` into the raw IEEE-754 bit pattern of `(eb, sb)`.
///
/// Returns `None` for formats this constructor does not support exactly. We
/// support the three standard widths that have a native Rust counterpart so the
/// bit pattern is computed by the hardware's correctly-rounded conversion (the
/// same exact path `fp.py` uses via `struct`):
/// - half  `(5, 11)`  : round the f64 to half precision in-Rust (RNE).
/// - single`(8, 24)`  : `f64 as f32`, then `f32::to_bits`.
/// - double`(11, 53)` : `f64::to_bits`.
///
/// Other formats return `None`; the caller reports `Z3_INVALID_ARG` rather than
/// fabricate an approximate encoding.
fn f64_to_fp_bits(value: f64, eb: u32, sb: u32) -> Option<u128> {
    match (eb, sb) {
        (8, 24) => Some(u128::from((value as f32).to_bits())),
        (11, 53) => Some(u128::from(value.to_bits())),
        (5, 11) => Some(u128::from(f64_to_f16_bits(value))),
        _ => None,
    }
}

/// Round an `f64` to IEEE-754 half precision (5/11), returning the 16-bit pattern.
///
/// Round-to-nearest-ties-to-even, the IEEE/Z3 default. Handles NaN, +/-inf,
/// signed zero, subnormals, and overflow-to-inf.
fn f64_to_f16_bits(value: f64) -> u16 {
    let bits = value.to_bits();
    let sign = ((bits >> 63) & 1) as u16;
    let exp = ((bits >> 52) & 0x7ff) as i64;
    let mant = bits & 0x000f_ffff_ffff_ffff;

    if exp == 0x7ff {
        // NaN or infinity.
        if mant != 0 {
            // Canonical quiet NaN for half: exp all ones, top mantissa bit set.
            return (sign << 15) | 0x7e00;
        }
        return (sign << 15) | 0x7c00; // +/-inf
    }

    if value == 0.0 {
        return sign << 15;
    }

    // Unbiased exponent of the double, and the target half exponent (bias 15).
    let unbiased = exp - 1023;
    let half_exp = unbiased + 15;

    if half_exp >= 0x1f {
        // Overflow -> infinity.
        return (sign << 15) | 0x7c00;
    }

    if half_exp <= 0 {
        // Subnormal half (or underflow to zero). Build the 1.f significand
        // (53 bits) including the implicit leading 1, then shift into the
        // subnormal range with round-to-nearest-ties-to-even.
        let full_sig = (1u64 << 52) | mant; // 1.mant scaled to 2^52
                                            // Number of bits to drop to land a 10-bit subnormal mantissa.
        let shift = (1 - half_exp) as u32 + (52 - 10);
        if shift >= 64 {
            return sign << 15; // underflow to zero
        }
        let rounded = round_shift(full_sig, shift);
        if rounded >= (1 << 10) {
            // Rounded up into the smallest normal.
            return (sign << 15) | (1 << 10);
        }
        return (sign << 15) | (rounded as u16);
    }

    // Normal half. Round the 52-bit trailing significand down to 10 bits.
    let rounded = round_shift(mant, 52 - 10);
    let mut half_exp = half_exp as u16;
    let mut half_mant = rounded as u16;
    if half_mant >= (1 << 10) {
        // Mantissa overflow carries into the exponent.
        half_mant = 0;
        half_exp += 1;
        if half_exp >= 0x1f {
            return (sign << 15) | 0x7c00; // overflow -> inf
        }
    }
    (sign << 15) | (half_exp << 10) | half_mant
}

/// Right-shift `value` by `shift` bits with round-to-nearest-ties-to-even.
fn round_shift(value: u64, shift: u32) -> u64 {
    if shift == 0 {
        return value;
    }
    if shift >= 64 {
        return 0;
    }
    let kept = value >> shift;
    let round_bit = (value >> (shift - 1)) & 1;
    let sticky = (value & ((1u64 << (shift - 1)) - 1)) != 0;
    if round_bit == 1 && (sticky || (kept & 1) == 1) {
        kept + 1
    } else {
        kept
    }
}

/// Create an FP numeral from a C `double`, rounded to the given FP sort.
///
/// Supports the standard half/single/double precisions (5/11, 8/24, 11/53),
/// where the conversion uses the hardware's correctly-rounded path (the same
/// bit-pattern route AY's `fp.py` validated against z3py). The resulting
/// `(fp ...)` term is built by [`ay_dpll::api::Solver::try_fp_const_from_bits_bigint`].
/// For any other `(eb, sb)` it returns NULL + `Z3_INVALID_ARG` (no fabricated
/// approximation). NaN and +/-inf doubles map to the corresponding FP special
/// values for these formats.
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
            ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
            let Some(bits) = f64_to_fp_bits(value, eb, sb) else {
                return ast_error(
                    ctx,
                    Z3_INVALID_ARG,
                    format!(
                        "Z3_mk_fpa_numeral_double: unsupported precision ({eb}, {sb}); \
                         supported: (5,11), (8,24), (11,53). Build the (fp ...) bit pattern \
                         via Z3_parse_smtlib2_string for other formats."
                    ),
                );
            };
            let big = num_bigint::BigInt::from(bits);
            match ctx.solver.try_fp_const_from_bits_bigint(&big, eb, sb) {
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
    let at = ast_to_term(a);
    let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operand must be FloatingPoint"),
        );
    };
    match build(ctx, at) {
        Ok(t) => {
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::FloatingPoint(eb, sb));
            r
        }
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
        ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
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
    let (at, bt) = (ast_to_term(a), ast_to_term(b));
    let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operands must be FloatingPoint"),
        );
    };
    match build(ctx, rmt, at, bt) {
        Ok(t) => {
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::FloatingPoint(eb, sb));
            r
        }
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
                ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "fp.fma", rm) else {
                return 0;
            };
            let (at, bt, ct) = (ast_to_term(t1), ast_to_term(t2), ast_to_term(t3));
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
                return ast_error(ctx, Z3_SORT_ERROR, "fp.fma: operands must be FloatingPoint");
            };
            match ctx.solver.try_fp_fma(rmt, at, bt, ct) {
                Ok(t) => {
                    let r = term_to_ast(t);
                    record_ast_sort(ctx, r, Sort::FloatingPoint(eb, sb));
                    r
                }
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
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "fp.sqrt", rm) else {
                return 0;
            };
            let at = ast_to_term(t);
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
                return ast_error(ctx, Z3_SORT_ERROR, "fp.sqrt: operand must be FloatingPoint");
            };
            match ctx.solver.try_fp_sqrt(rmt, at) {
                Ok(t) => {
                    let r = term_to_ast(t);
                    record_ast_sort(ctx, r, Sort::FloatingPoint(eb, sb));
                    r
                }
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
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "fp.roundToIntegral", rm) else {
                return 0;
            };
            let at = ast_to_term(t);
            let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "fp.roundToIntegral: operand must be FloatingPoint",
                );
            };
            match ctx.solver.try_fp_round_to_integral(rmt, at) {
                Ok(t) => {
                    let r = term_to_ast(t);
                    record_ast_sort(ctx, r, Sort::FloatingPoint(eb, sb));
                    r
                }
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
    let (at, bt) = (ast_to_term(a), ast_to_term(b));
    let Sort::FloatingPoint(eb, sb) = ctx.solver.sort_of(at) else {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operands must be FloatingPoint"),
        );
    };
    match build(ctx, at, bt) {
        Ok(t) => {
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::FloatingPoint(eb, sb));
            r
        }
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
                ffi_guard_ast(c, |ctx| {
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
    let (at, bt) = (ast_to_term(a), ast_to_term(b));
    if !matches!(ctx.solver.sort_of(at), Sort::FloatingPoint(_, _)) {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operands must be FloatingPoint"),
        );
    }
    match build(ctx, at, bt) {
        Ok(t) => {
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::Bool);
            r
        }
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
                ffi_guard_ast(c, |ctx| {
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
    let at = ast_to_term(a);
    if !matches!(ctx.solver.sort_of(at), Sort::FloatingPoint(_, _)) {
        return ast_error(
            ctx,
            Z3_SORT_ERROR,
            format!("{op}: operand must be FloatingPoint"),
        );
    }
    match build(ctx, at) {
        Ok(t) => {
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::Bool);
            r
        }
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
                ffi_guard_ast(c, |ctx| {
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
            ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_float", rm) else {
                return 0;
            };
            let ft = ast_to_term(t);
            if !matches!(ctx.solver.sort_of(ft), Sort::FloatingPoint(_, _)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_float: value must be a FloatingPoint",
                );
            }
            match ctx.solver.try_fp_to_fp(rmt, ft, eb, sb) {
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
            ffi_guard_ast(c, |ctx| {
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
        ffi_guard_ast(c, |ctx| {
            let Some(rmt) = require_fpa_rounding_mode(ctx, "Z3_mk_fpa_to_fp_signed", rm) else {
                return 0;
            };
            let bvt = ast_to_term(t);
            if !matches!(ctx.solver.sort_of(bvt), Sort::BitVec(_)) {
                return ast_error(
                    ctx,
                    Z3_SORT_ERROR,
                    "Z3_mk_fpa_to_fp_signed: value must be a BitVec",
                );
            }
            match ctx.solver.try_bv_to_fp(rmt, bvt, eb, sb) {
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

#[cfg(test)]
#[path = "fpa_tests.rs"]
mod fpa_tests;
