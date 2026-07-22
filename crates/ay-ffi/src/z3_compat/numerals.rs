// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible numeral construction functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint, CStr};

use ay_dpll::api::Sort;
use num_bigint::BigInt;

use super::{
    ffi_guard_ast, record_ast_sort, term_to_ast, Z3Context, Z3_ast, Z3_context, Z3_sort,
    Z3_INVALID_ARG,
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
    let ast = term_to_ast(term);
    record_ast_sort(ctx, ast, sort.clone());
    ast
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
    // SAFETY: The caller's `# Safety` contract requires the C string pointer to be non-null
    // and to point to a valid, null-terminated sequence of bytes owned by the caller for the
    // duration of this call. The pointer was null-checked before entering this block.
    let num_str = match unsafe { CStr::from_ptr(numeral).to_str() } {
        Ok(s) => s.to_string(),
        Err(_) => return 0,
    };
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
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => match num_str.parse::<BigInt>() {
                    Ok(v) => ctx.solver.int_const_bigint(&v),
                    Err(_) => return 0,
                },
                Sort::Real => {
                    if let Some((n, d)) = num_str.split_once('/') {
                        if let (Ok(numer), Ok(denom)) =
                            (n.trim().parse::<BigInt>(), d.trim().parse::<BigInt>())
                        {
                            ctx.solver.rational_const_bigint(&numer, &denom)
                        } else {
                            return 0;
                        }
                    } else if let Ok(v) = num_str.parse::<BigInt>() {
                        // Integer literal used as Real — construct as n/1
                        ctx.solver.rational_const_bigint(&v, &BigInt::from(1))
                    } else {
                        return 0;
                    }
                }
                Sort::BitVec(bvs) => match num_str.parse::<BigInt>() {
                    Ok(v) => ctx.solver.bv_const_bigint(&v, bvs.width),
                    Err(_) => return 0,
                },
                Sort::FiniteDomain(_, _) => match num_str.parse::<BigInt>() {
                    Ok(v) => return mk_finite_domain_numeral(ctx, &v, &sort),
                    Err(_) => return 0,
                },
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
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
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(i64::from(v)),
                Sort::Real => ctx.solver.real_const(f64::from(v)),
                Sort::BitVec(bvs) => ctx.solver.bv_const(i64::from(v), bvs.width),
                Sort::FiniteDomain(_, _) => {
                    return mk_finite_domain_numeral(ctx, &BigInt::from(v), &sort)
                }
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
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
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(i64::from(v)),
                Sort::Real => ctx.solver.real_const(f64::from(v)),
                Sort::BitVec(bvs) => ctx.solver.bv_const(i64::from(v), bvs.width),
                Sort::FiniteDomain(_, _) => {
                    return mk_finite_domain_numeral(ctx, &BigInt::from(v), &sort)
                }
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
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
        ffi_guard_ast(c, |ctx| {
            let term = match &sort {
                Sort::Int => ctx.solver.int_const(v),
                Sort::Real => {
                    let big_v = BigInt::from(v);
                    ctx.solver.rational_const_bigint(&big_v, &BigInt::from(1))
                }
                Sort::BitVec(bvs) => ctx.solver.bv_const(v, bvs.width),
                Sort::FiniteDomain(_, _) => {
                    return mk_finite_domain_numeral(ctx, &BigInt::from(v), &sort)
                }
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
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
        ffi_guard_ast(c, |ctx| {
            let big_v = BigInt::from(v);
            let term = match &sort {
                Sort::Int => ctx.solver.int_const_bigint(&big_v),
                Sort::Real => ctx.solver.rational_const_bigint(&big_v, &BigInt::from(1)),
                Sort::BitVec(bvs) => ctx.solver.bv_const_bigint(&big_v, bvs.width),
                Sort::FiniteDomain(_, _) => return mk_finite_domain_numeral(ctx, &big_v, &sort),
                _ => return 0,
            };
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
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
        ffi_guard_ast(c, |ctx| {
            let term = ctx.solver.rational_const(i64::from(num), i64::from(den));
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, Sort::Real);
            ast
        })
    }
}
