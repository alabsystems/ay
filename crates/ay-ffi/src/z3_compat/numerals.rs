// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible numeral construction functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint};

use ay_dpll::api::Sort;
use num_bigint::BigInt;

use super::{
    ffi_guard_mk, ffi_read_bounded_numeral_text, record_ast_sort, term_to_ast, Z3Context, Z3_ast,
    Z3_context, Z3_sort, Z3_INVALID_ARG, Z3_PARSER_ERROR,
};

// ---- Numerals ----

/// Build a finite-domain numeral: the `Int` literal `v` recorded at the
/// finite-domain sort, after the exact range check Z3 performs
/// (`0 <= v < size`; libz3 4.16 rejects an out-of-range value with "value is
/// out of bounds"). Returns 0 with `Z3_INVALID_ARG` when out of range — never
/// a fabricated wrapped/clamped value.
fn mk_finite_domain_numeral(ctx: &mut Z3Context, v: &BigInt, sort: &Sort) -> Z3_ast {
    let Some(size) = sort.finite_domain_size() else {
        return 0; // caller dispatches only on FiniteDomain
    };
    if v.sign() == num_bigint::Sign::Minus || *v >= BigInt::from(size) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "finite-domain numeral: value {v} is out of bounds for a domain of size {size}"
        ));
        return 0;
    }
    let term = ctx.solver.int_const_bigint(v);
    let ast = term_to_ast(ctx, term);
    record_ast_sort(ctx, ast, sort.clone())
}

/// A FloatingPoint numeral in z3py's `FPVal` spelling: an exact Real
/// numeral optionally followed by `p<exp>` (times `2^exp`). Round the exact
/// rational once into the requested format; an intermediate double would lose
/// precision for non-dyadic values and formats wider than binary64.
fn fp_numeral_term(
    ctx: &mut Z3Context,
    text: &str,
    eb: u32,
    sb: u32,
) -> Option<ay_dpll::api::Term> {
    use num_rational::BigRational;
    use num_traits::Zero;
    let text = text.trim();
    let (mantissa, exponent) = match text.rsplit_once(['p', 'P']) {
        Some((mantissa, exp)) => (mantissa, exp.trim().parse::<i32>().ok()?),
        None => (text, 0),
    };
    // Keep the existing bounded textual exponent envelope; refuse before
    // allocating `2^exp`. This envelope is independent of the target precision.
    if exponent.unsigned_abs() > 4096 {
        return None;
    }
    let mut value = parse_numeral_text(mantissa)?;
    let scale = BigRational::from_integer(BigInt::from(2u32).pow(exponent.unsigned_abs()));
    if exponent >= 0 {
        value *= scale;
    } else {
        value /= scale;
    }
    // Rationals erase the sign of zero, so preserve the textual minus.
    let bits = if value.is_zero() && mantissa.trim_start().starts_with('-') {
        super::fpa::f64_to_fp_bits(-0.0, eb, sb)?
    } else {
        ay_fp::round_rational_to_ieee_bits(&value, eb, sb, ay_fp::RoundingMode::RNE)
    };
    ctx.solver.try_fp_const_from_bits_bigint(&bits, eb, sb).ok()
}

/// Report a numeral text the sort cannot read (z3: a parser error) and return
/// the NULL AST, so the caller sees an error code instead of a silent NULL.
fn invalid_numeral(ctx: &mut Z3Context, text: &str, sort: &Sort) -> Z3_ast {
    ctx.last_error = Z3_PARSER_ERROR;
    ctx.error_msg = Some(format!(
        "Z3_mk_numeral: `{text}` is not a numeral of sort {sort}"
    ));
    0
}

/// Create a numeral from a string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_numeral(
    c: Z3_context,
    numeral: *const c_char,
    ty: Z3_sort,
) -> Z3_ast {
    if numeral.is_null() || ty.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_numeral", |ctx| {
            // SAFETY: `numeral` was null-checked and the caller guarantees a
            // live NUL-terminated string for this call.
            let num_str = match ffi_read_bounded_numeral_text(ctx, "Z3_mk_numeral", numeral) {
                Some(text) => text,
                None => return 0,
            };

            // SAFETY: `ty` was null-checked above and originates from a live AY
            // sort allocation owned by this context.
            let sort = (*ty).sort.clone();
            if let Sort::FloatingPoint(eb, sb) = sort {
                let Some(term) = fp_numeral_term(ctx, &num_str, eb, sb) else {
                    return invalid_numeral(ctx, &num_str, &sort);
                };
                let ast = term_to_ast(ctx, term);
                let ast = record_ast_sort(ctx, ast, sort);
                return ast;
            }
            let Some(value) = parse_numeral_text(&num_str) else {
                ctx.last_error = Z3_PARSER_ERROR;
                ctx.error_msg = Some(format!("Z3_mk_numeral: '{num_str}' is not a numeral"));
                return 0;
            };
            let whole = || value.is_integer().then(|| value.to_integer());
            let not_whole = |ctx: &mut Z3Context| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_numeral: '{num_str}' is not an integer, as sort {sort} requires"
                ));
                0
            };
            let term = match &sort {
                Sort::FiniteField(field) => match whole() {
                    Some(v) => ctx.solver.finite_field_const(&v, *field),
                    None => return not_whole(ctx),
                },
                Sort::Int => match whole() {
                    Some(v) => ctx.solver.int_const_bigint(&v),
                    None => return not_whole(ctx),
                },
                Sort::Real => ctx
                    .solver
                    .rational_const_bigint(value.numer(), value.denom()),
                Sort::BitVec(bvs) => match whole() {
                    Some(v) => ctx.solver.bv_const_bigint(&v, bvs.width),
                    None => return not_whole(ctx),
                },
                Sort::FiniteDomain(_, _) => match whole() {
                    Some(v) => return mk_finite_domain_numeral(ctx, &v, &sort),
                    None => return not_whole(ctx),
                },
                _ => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_numeral: no numerals of sort {sort} through this entry point"
                    ));
                    return 0;
                }
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort.clone())
        })
    }
}

/// Largest decimal exponent `Z3_mk_numeral` expands (`1e<n>` has `n` digits).
const MAX_NUMERAL_EXPONENT: u32 = 100_000;

/// The value of z3's numeral text (`rational(char const*)`, as
/// `Z3_mk_numeral` reads it): surrounding blanks, an optional sign, then
/// `a/b`, or decimal digits with an optional `.` fraction (either side may be
/// empty: `.5`, `2.`) and an optional `e`/`E` exponent (`1e2`, `-1.25e1`).
/// `None` for anything else, which z3 reports as a parser error.
pub(crate) fn parse_numeral_text(text: &str) -> Option<num_rational::BigRational> {
    use num_rational::BigRational;
    use num_traits::Zero;
    let text = text.trim_matches(|c: char| c == ' ' || c == '\n' || c == '\t' || c == '\r');
    let (negative, body) = match text.as_bytes().first()? {
        b'-' => (true, &text[1..]),
        b'+' => (false, &text[1..]),
        _ => (false, text),
    };
    let digits = |s: &str| -> Option<BigInt> {
        (!s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())).then(|| s.parse().ok())?
    };
    let value = if let Some((numer, denom)) = body.split_once('/') {
        let denom = digits(denom.trim())?;
        if denom.is_zero() {
            return None;
        }
        BigRational::new(digits(numer.trim())?, denom)
    } else {
        let (mantissa, exponent) = match body.find(['e', 'E']) {
            Some(at) => (&body[..at], Some(&body[at + 1..])),
            None => (body, None),
        };
        let (int_part, frac_part) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        if int_part.is_empty() && frac_part.is_empty() {
            return None;
        }
        let int_value = if int_part.is_empty() {
            BigInt::zero()
        } else {
            digits(int_part)?
        };
        let mut value = BigRational::from_integer(int_value);
        if !frac_part.is_empty() {
            let scale = BigInt::from(10).pow(u32::try_from(frac_part.len()).ok()?);
            value += BigRational::new(digits(frac_part)?, scale);
        }
        if let Some(exponent) = exponent {
            let (exp_negative, exp_digits) = match exponent.as_bytes().first()? {
                b'-' => (true, &exponent[1..]),
                b'+' => (false, &exponent[1..]),
                _ => (false, exponent),
            };
            let power = u32::try_from(digits(exp_digits)?).ok()?;
            if power > MAX_NUMERAL_EXPONENT {
                return None;
            }
            let factor = BigRational::from_integer(BigInt::from(10).pow(power));
            value = if exp_negative {
                value / factor
            } else {
                value * factor
            };
        }
        value
    };
    Some(if negative { -value } else { value })
}

/// Create an integer numeral.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int(c: Z3_context, v: c_int, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    // SAFETY: `ty` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = unsafe { (*ty).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_int", |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(i64::from(v)),
                Sort::Real => ctx.solver.real_const(f64::from(v)),
                Sort::FiniteField(field) => ctx.solver.finite_field_const(&BigInt::from(v), *field),
                Sort::BitVec(bvs) => ctx.solver.bv_const(i64::from(v), bvs.width),
                Sort::FiniteDomain(_, _) => {
                    return mk_finite_domain_numeral(ctx, &BigInt::from(v), &sort);
                }
                _ => return 0,
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort.clone())
        })
    }
}

/// Create an unsigned integer numeral.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_unsigned_int(c: Z3_context, v: c_uint, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    // SAFETY: `ty` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = unsafe { (*ty).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_unsigned_int", |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(i64::from(v)),
                Sort::Real => ctx.solver.real_const(f64::from(v)),
                Sort::FiniteField(field) => ctx.solver.finite_field_const(&BigInt::from(v), *field),
                Sort::BitVec(bvs) => ctx.solver.bv_const(i64::from(v), bvs.width),
                Sort::FiniteDomain(_, _) => {
                    return mk_finite_domain_numeral(ctx, &BigInt::from(v), &sort);
                }
                _ => return 0,
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort.clone())
        })
    }
}

/// Create a numeral from a 64-bit signed integer.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int64(c: Z3_context, v: i64, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    // SAFETY: `ty` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = unsafe { (*ty).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_int64", |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(v),
                Sort::Real => {
                    let big_v = BigInt::from(v);
                    ctx.solver.rational_const_bigint(&big_v, &BigInt::from(1))
                }
                Sort::FiniteField(field) => ctx.solver.finite_field_const(&BigInt::from(v), *field),
                Sort::BitVec(bvs) => ctx.solver.bv_const(v, bvs.width),
                Sort::FiniteDomain(_, _) => {
                    return mk_finite_domain_numeral(ctx, &BigInt::from(v), &sort);
                }
                _ => return 0,
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort.clone())
        })
    }
}

/// Create a numeral from a 64-bit unsigned integer.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_unsigned_int64(c: Z3_context, v: u64, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    // SAFETY: `ty` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = unsafe { (*ty).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_unsigned_int64", |ctx| {
            let big_v = BigInt::from(v);
            let term = match &sort {
                Sort::Int => ctx.solver.int_const_bigint(&big_v),
                Sort::Real => ctx.solver.rational_const_bigint(&big_v, &BigInt::from(1)),
                Sort::FiniteField(field) => ctx.solver.finite_field_const(&big_v, *field),
                Sort::BitVec(bvs) => ctx.solver.bv_const_bigint(&big_v, bvs.width),
                Sort::FiniteDomain(_, _) => return mk_finite_domain_numeral(ctx, &big_v, &sort),
                _ => return 0,
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort.clone())
        })
    }
}

/// Create a real numeral from numerator/denominator.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real(c: Z3_context, num: c_int, den: c_int) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_real", |ctx| {
            let term = ctx.solver.rational_const(i64::from(num), i64::from(den));
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, Sort::Real)
        })
    }
}
