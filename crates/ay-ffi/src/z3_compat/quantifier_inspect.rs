// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible quantifier introspection functions.
//!
//! Decomposes quantifier terms back into their bound variables, body,
//! patterns, and metadata. Construction functions live in `quantifiers.rs`.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::c_uint;
use std::ptr;

use ay_dpll::api::TermKind;

use super::quantifiers::{PatternHandle, Z3_pattern};
use super::{
    alloc_sort, ast_to_term, cache_symbol, ffi_guard_ast, ffi_guard_int, ffi_guard_ptr,
    ffi_guard_uint, term_to_ast, Z3_ast, Z3_context, Z3_sort, Z3_symbol,
};

/// Return true if the AST is a universal quantifier.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_quantifier_forall(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            i32::from(matches!(
                ctx.solver.term_kind(ast_to_term(a)),
                TermKind::Forall
            ))
        }) != 0
    }
}

/// Return true if the AST is an existential quantifier.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_quantifier_exists(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            i32::from(matches!(
                ctx.solver.term_kind(ast_to_term(a)),
                TermKind::Exists
            ))
        }) != 0
    }
}

/// Get the body of a quantifier.
///
/// Returns 0 (null AST) if `a` is not a quantifier.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_body(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let children = ctx.solver.term_children(ast_to_term(a));
            children.first().map_or(0, |&t| term_to_ast(t))
        })
    }
}

/// Get the number of bound variables in a quantifier.
///
/// Returns 0 if `a` is not a quantifier.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_num_bound(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.solver
                .quantifier_bound_vars(ast_to_term(a))
                .map_or(0, |v| v.len() as c_uint)
        })
    }
}

/// Get the name of the i-th bound variable in a quantifier.
///
/// Returns null if `a` is not a quantifier or `i` is out of bounds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_bound_name(
    c: Z3_context,
    a: Z3_ast,
    i: c_uint,
) -> Z3_symbol {
    if a == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            match ctx.solver.quantifier_bound_vars(ast_to_term(a)) {
                Some(vars) if (i as usize) < vars.len() => {
                    cache_symbol(ctx, vars[i as usize].0.clone())
                }
                _ => ptr::null_mut(),
            }
        })
    }
}

/// Get the sort of the i-th bound variable in a quantifier.
///
/// Returns null if `a` is not a quantifier or `i` is out of bounds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_bound_sort(
    c: Z3_context,
    a: Z3_ast,
    i: c_uint,
) -> Z3_sort {
    if a == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            match ctx.solver.quantifier_bound_vars(ast_to_term(a)) {
                Some(vars) if (i as usize) < vars.len() => {
                    alloc_sort(ctx, vars[i as usize].1.clone())
                }
                _ => ptr::null_mut(),
            }
        })
    }
}

/// Get the number of trigger patterns in a quantifier.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_num_patterns(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.solver
                .quantifier_triggers(ast_to_term(a))
                .map_or(0, |t| t.len() as c_uint)
        })
    }
}

/// Get the i-th trigger pattern of a quantifier.
///
/// Returns null if `a` is not a quantifier or `i` is out of bounds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_pattern_ast(
    c: Z3_context,
    a: Z3_ast,
    i: c_uint,
) -> Z3_pattern {
    if a == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            match ctx.solver.quantifier_triggers(ast_to_term(a)) {
                Some(triggers) if (i as usize) < triggers.len() => {
                    let handle = Box::into_raw(Box::new(PatternHandle {
                        terms: triggers[i as usize].clone(),
                    }));
                    ctx.pattern_cache.push(handle);
                    handle
                }
                _ => ptr::null_mut(),
            }
        })
    }
}

/// Get the weight of a quantifier (priority hint).
///
/// AY does not track weights; always returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_weight(_c: Z3_context, _a: Z3_ast) -> c_uint {
    0
}

/// Get the number of no-patterns in a quantifier.
///
/// AY does not support no-patterns; always returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_num_no_patterns(_c: Z3_context, _a: Z3_ast) -> c_uint {
    0
}

/// Get the i-th no-pattern of a quantifier.
///
/// AY does not support no-patterns; always returns 0 (null AST).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_no_pattern_ast(
    _c: Z3_context,
    _a: Z3_ast,
    _i: c_uint,
) -> Z3_ast {
    0
}
