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
#[path = "quantifier_de_bruijn_body.rs"]
mod de_bruijn_body;

use super::{
    alloc_sort, cache_symbol, cache_symbol_key, ffi_guard_ast, ffi_guard_int, ffi_guard_ptr,
    ffi_guard_uint, lookup_ast_sort, require_term_ast_or_return, term_to_ast, Z3_ast, Z3_context,
    Z3_sort, Z3_symbol,
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
            let term =
                require_term_ast_or_return!(ctx, a, "Z3_is_quantifier_forall", "quantifier", 0);
            i32::from(matches!(ctx.solver.term_kind(term), TermKind::Forall))
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
            let term =
                require_term_ast_or_return!(ctx, a, "Z3_is_quantifier_exists", "quantifier", 0);
            i32::from(matches!(ctx.solver.term_kind(term), TermKind::Exists))
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
            let term =
                require_term_ast_or_return!(ctx, a, "Z3_get_quantifier_body", "quantifier", 0);
            let children = ctx.solver.term_children(term);
            let Some(&body) = children.first() else {
                return 0;
            };
            // z3's body names its binders by de Bruijn index (the last binder
            // is `(:var 0)`), so `substitute_vars` instantiates it (it was a
            // no-op on AY's named-constant body). A body the conversion cannot
            // rebuild is returned as it is stored.
            let body = de_bruijn_body::de_bruijn_body(ctx, term, body).unwrap_or(body);
            term_to_ast(ctx, body)
        })
    }
}

/// The public sort of binder `index` of `quantifier` when the C API or a
/// parsed text recorded one (a FiniteSet binder's engine sort is its
/// characteristic array).
fn quantifier_bound_public_sort(
    ctx: &super::Z3Context,
    quantifier: ay_dpll::api::Term,
    index: usize,
) -> Option<ay_dpll::api::Sort> {
    ctx.quantifier_public_bound_terms
        .get(&quantifier)
        .and_then(|bounds| bounds.get(index))
        .and_then(|&bound| lookup_ast_sort(ctx, term_to_ast(ctx, bound)))
        .cloned()
        .or_else(|| {
            ctx.parsed_quantifier_public_bound_sorts
                .get(&quantifier)
                .and_then(|sorts| sorts.get(index))
                .cloned()
        })
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
            let term =
                require_term_ast_or_return!(ctx, a, "Z3_get_quantifier_num_bound", "quantifier", 0);
            ctx.solver
                .quantifier_bound_vars(term)
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_bound_name",
                "quantifier",
                ptr::null_mut()
            );
            let index = i as usize;
            let public_symbol = ctx
                .quantifier_public_bound_terms
                .get(&term)
                .and_then(|bounds| bounds.get(index))
                .and_then(|bound| ctx.ffi_const_metadata.get(bound))
                .map(|(_, symbol)| symbol.clone());
            if let Some(symbol) = public_symbol {
                return cache_symbol_key(ctx, symbol);
            }
            match ctx.solver.quantifier_bound_vars(term) {
                // A binder named by a private API identity (a quantifier the
                // evaluator or a rewrite rebuilt over the caller's constant)
                // shows the caller's name, never `!ay.z3-const!N`.
                // A de Bruijn binder minted under a private spelling (its name
                // was reused at another sort, or had to avoid capture) shows
                // the caller's symbol too: z3 shows `w`, never
                // `!ay.z3-bound!1!w`.
                Some(vars) if index < vars.len() => {
                    let identity = &vars[index].0;
                    match ctx
                        .ffi_const_terms_by_identity
                        .get(identity)
                        .and_then(|bound| ctx.ffi_const_metadata.get(bound))
                        .map(|(_, symbol)| symbol.clone())
                        .or_else(|| ctx.ffi_decl_symbols.get(identity).cloned())
                    {
                        Some(symbol) => cache_symbol_key(ctx, symbol),
                        None => cache_symbol(ctx, identity.clone()),
                    }
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_bound_sort",
                "quantifier",
                ptr::null_mut()
            );
            let index = i as usize;
            let engine_sort = match ctx.solver.quantifier_bound_vars(term) {
                Some(vars) if index < vars.len() => vars[index].1.clone(),
                _ => return ptr::null_mut(),
            };
            let public_sort = quantifier_bound_public_sort(ctx, term, index).unwrap_or(engine_sort);
            alloc_sort(ctx, public_sort)
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_num_patterns",
                "quantifier",
                0
            );
            ctx.solver
                .quantifier_triggers(term)
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_pattern_ast",
                "quantifier",
                ptr::null_mut()
            );
            match ctx.solver.quantifier_triggers(term) {
                Some(triggers) if (i as usize) < triggers.len() => {
                    let handle = Box::into_raw(Box::new(PatternHandle {
                        terms: triggers[i as usize].clone(),
                        owner_salt: ctx.handle_salt,
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
/// Quantifiers built through the C API retain the exact caller-supplied value.
/// Parsed quantifiers without retained weight metadata use Z3's default weight
/// of 1. A later constructor that would reuse a hash-consed term with different
/// metadata is rejected, so one public AST can never change another AST's
/// introspection result.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_weight(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `ffi_guard_uint` null-checks `c`, authenticates `a` in the
    // closure, and catches panics before they can cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let term =
                require_term_ast_or_return!(ctx, a, "Z3_get_quantifier_weight", "quantifier", 0);
            if !matches!(
                ctx.solver.term_kind(term),
                TermKind::Forall | TermKind::Exists
            ) {
                return 0;
            }
            ctx.quantifier_weights.get(&term).copied().unwrap_or(1)
        })
    }
}

/// Get the number of no-patterns in a quantifier.
///
/// Explicit no-pattern expressions supplied through an extended constructor
/// round-trip exactly. Quantifiers without explicit metadata return 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_num_no_patterns(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: guard/authentication prevents invalid handles and unwinding.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_num_no_patterns",
                "quantifier",
                0
            );
            ctx.quantifier_no_patterns
                .get(&term)
                .map_or(0, |patterns| patterns.len() as c_uint)
        })
    }
}

/// Get the i-th no-pattern of a quantifier.
///
/// Returns the retained expression, or a null AST for an absent/out-of-range
/// entry.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_no_pattern_ast(
    c: Z3_context,
    a: Z3_ast,
    i: c_uint,
) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: guard/authentication prevents invalid handles and unwinding.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_no_pattern_ast",
                "quantifier",
                0
            );
            ctx.quantifier_no_patterns
                .get(&term)
                .and_then(|patterns| patterns.get(i as usize))
                .copied()
                .map_or(0, |expression| term_to_ast(ctx, expression))
        })
    }
}

#[cfg(test)]
#[path = "t5_p0_integration_tests.rs"]
mod t5_p0_integration_tests;
