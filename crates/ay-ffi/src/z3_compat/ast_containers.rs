// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST containers: the `Z3_ast_map_*` family plus the two
//! `Z3_ast_vector` operations that complete that container (`to_string` and
//! `translate`). Mirrors upstream `z3_ast_containers.h`.
//!
//! An [`AstMapHandle`](super::AstMapHandle) is a real `HashMap<Z3_ast, Z3_ast>`
//! (keys and values are ordinary term handles interned in the context's shared
//! term store) with a parallel insertion-order key vector so `keys`/`to_string`
//! render deterministically. The vector helpers reuse the SAME machinery the
//! rest of the FFI uses: `format_term_checked` (identical to `Z3_ast_to_string`)
//! for rendering and `Solver::translate_terms_from` (the goal/solver-translate
//! graft) for cross-context copies — never a fabricated element or handle.
//!
//! # Honesty
//!
//! `Z3_ast_map_find` on an absent key does NOT invent a value: it records
//! `Z3_INVALID_ARG` (Z3's "invoke the error handler if `k` is not in the map")
//! and returns the null AST `0`. `translate` re-interns each element's real term
//! DAG into the destination context; it never returns a handle that is
//! meaningless there.

use std::ptr;

use super::{
    cache_ast_map, cache_ast_vector, cache_string, checked_ast_to_term,
    ensure_cross_context_translation_semantics, ffi_guard_ast, ffi_guard_const_ptr, ffi_guard_int,
    ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, record_ast_sort, require_term_ast,
    require_term_ast_or_return, require_term_asts_or_return, term_to_ast,
    transfer_cross_context_ffi_metadata, Z3Context, Z3_ast, Z3_ast_map, Z3_ast_vector, Z3_context,
    Z3_string, Z3_INVALID_ARG, Z3_OK,
};
use ay_dpll::api::Term;
use std::os::raw::c_uint;

/// Render one `Z3_ast` handle exactly as `Z3_ast_to_string` would, falling back
/// to `?` for the null handle or an unformattable term. Shared by both the map
/// and vector `to_string` renderers so their element text matches libz3's.
fn render_ast(ctx: &mut Z3Context, a: Z3_ast, operation: &str) -> Option<String> {
    if a == 0 {
        return Some("?".to_string());
    }
    let term = require_term_ast(ctx, a, operation, "container element")?;
    let rendered = ctx
        .solver
        .format_term_checked(term)
        .unwrap_or_else(|| "?".to_string());
    Some(super::ffi_surface_text(ctx, &rendered))
}

// ============================================================================
// AST maps (Z3_ast_map_*)
// ============================================================================

/// Create an empty AST-to-AST map (Z3's `Z3_mk_ast_map`).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ast_map(c: Z3_context) -> Z3_ast_map {
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` null-checks
    // it and catches any unwinding panic so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            cache_ast_map(ctx)
        })
    }
}

/// Increment AST-map reference count (arena-owned; bookkeeping no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_inc_ref(_c: Z3_context, _m: Z3_ast_map) {}

/// Decrement AST-map reference count (arena-owned; bookkeeping no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_dec_ref(_c: Z3_context, _m: Z3_ast_map) {}

/// Return `true` iff the map contains key `k` (Z3's `Z3_ast_map_contains`).
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_contains(c: Z3_context, m: Z3_ast_map, k: Z3_ast) -> bool {
    // Pre-extract the membership answer (raw deref of the distinct map allocation).
    // SAFETY: `m`, when non-null, is a live `AstMapHandle`; `as_ref` null-checks.
    let present = unsafe { m.as_ref() }.is_some_and(|h| h.map.contains_key(&k));
    // SAFETY: `ffi_guard_int` handles a null context and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let _term = require_term_ast_or_return!(ctx, k, "Z3_ast_map_contains", "map key", 0);
            ctx.last_error = Z3_OK;
            std::os::raw::c_int::from(present)
        }) != 0
    }
}

/// Return the value associated with key `k` (Z3's `Z3_ast_map_find`).
///
/// If `k` is absent, records `Z3_INVALID_ARG` (Z3 "invokes the error handler")
/// and returns the null AST `0` — never a fabricated value.
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_find(c: Z3_context, m: Z3_ast_map, k: Z3_ast) -> Z3_ast {
    // Pre-extract the value (raw deref of the distinct map allocation).
    // SAFETY: `m`, when non-null, is a live `AstMapHandle`; `as_ref` null-checks.
    let value = unsafe { m.as_ref() }.and_then(|h| h.map.get(&k).copied());
    // SAFETY: `ffi_guard_ast` handles a null context and catches panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let _key_term = require_term_ast_or_return!(ctx, k, "Z3_ast_map_find", "map key", 0);
            match value {
                Some(v) => {
                    let _value_term = require_term_ast_or_return!(
                        ctx,
                        v,
                        "Z3_ast_map_find",
                        "stored map value",
                        0
                    );
                    ctx.last_error = Z3_OK;
                    v
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_ast_map_find: key not present in map".to_string());
                    0
                }
            }
        })
    }
}

/// Store or replace `k -> v` in the map (Z3's `Z3_ast_map_insert`).
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_insert(c: Z3_context, m: Z3_ast_map, k: Z3_ast, v: Z3_ast) {
    if m.is_null() {
        return;
    }
    // SAFETY: `ffi_guard_void` handles a null context and catches panics. `m` is a
    // valid, non-null `AstMapHandle` pointer distinct from the context allocation,
    // so mutating `(*m)` does not alias the `&mut Z3Context` borrow.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let _key_term = require_term_ast_or_return!(ctx, k, "Z3_ast_map_insert", "map key");
            let _value_term = require_term_ast_or_return!(ctx, v, "Z3_ast_map_insert", "map value");
            ctx.last_error = Z3_OK;
            (*m).insert(k, v);
        });
    }
}

/// Erase key `k` from the map (Z3's `Z3_ast_map_erase`); a no-op if absent.
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_erase(c: Z3_context, m: Z3_ast_map, k: Z3_ast) {
    if m.is_null() {
        return;
    }
    // SAFETY: as in `Z3_ast_map_insert` — `(*m)` is a distinct, valid allocation.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let _key_term = require_term_ast_or_return!(ctx, k, "Z3_ast_map_erase", "map key");
            ctx.last_error = Z3_OK;
            (*m).erase(k);
        });
    }
}

/// Remove every key from the map (Z3's `Z3_ast_map_reset`).
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_reset(c: Z3_context, m: Z3_ast_map) {
    if m.is_null() {
        return;
    }
    // SAFETY: as in `Z3_ast_map_insert` — `(*m)` is a distinct, valid allocation.
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.last_error = Z3_OK;
            (*m).reset();
        });
    }
}

/// Return the number of entries in the map (Z3's `Z3_ast_map_size`).
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_size(c: Z3_context, m: Z3_ast_map) -> c_uint {
    // SAFETY: `m`, when non-null, is a live `AstMapHandle`; `as_ref` null-checks.
    let n = unsafe { m.as_ref() }.map_or(0, |h| h.map.len() as c_uint);
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.last_error = Z3_OK;
            n
        })
    }
}

/// Return a fresh AST vector of the map's keys, in insertion order (Z3's
/// `Z3_ast_map_keys`). The keys are the REAL key handles stored in the map.
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_keys(c: Z3_context, m: Z3_ast_map) -> Z3_ast_vector {
    // Pre-extract the key list (raw deref of the distinct map allocation).
    // SAFETY: `m`, when non-null, is a live `AstMapHandle`; `as_ref` null-checks.
    let keys = unsafe { m.as_ref() }.map(|h| h.order.clone());
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let keys = keys.unwrap_or_default();
            let _terms =
                require_term_asts_or_return!(ctx, &keys, "Z3_ast_map_keys", ptr::null_mut());
            ctx.last_error = Z3_OK;
            cache_ast_vector(ctx, keys)
        })
    }
}

/// Render the map as an s-expression (Z3's `Z3_ast_map_to_string`):
/// `(ast-map` then, for each entry in insertion order, an indented
/// `(key\n   value)` pair, closed by `)`. An empty map prints `(ast-map)`.
/// Each key/value is rendered by the same formatter as `Z3_ast_to_string`.
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid map handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_map_to_string(c: Z3_context, m: Z3_ast_map) -> Z3_string {
    // Pre-extract the (key, value) pairs in insertion order. `h.map[&k]` never
    // panics: `order` and `map` are kept in lockstep by `AstMapHandle`.
    // SAFETY: `m`, when non-null, is a live `AstMapHandle`; `as_ref` null-checks.
    let pairs: Option<Vec<(Z3_ast, Z3_ast)>> =
        unsafe { m.as_ref() }.map(|h| h.order.iter().map(|&k| (k, h.map[&k])).collect());
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            let mut s = String::from("(ast-map");
            if let Some(entries) = pairs {
                for (k, v) in entries {
                    s.push_str("\n  (");
                    let Some(key) = render_ast(ctx, k, "Z3_ast_map_to_string") else {
                        return ptr::null();
                    };
                    s.push_str(&key);
                    s.push_str("\n   ");
                    let Some(value) = render_ast(ctx, v, "Z3_ast_map_to_string") else {
                        return ptr::null();
                    };
                    s.push_str(&value);
                    s.push(')');
                }
            }
            s.push(')');
            cache_string(ctx, s)
        })
    }
}

// ============================================================================
// AST vector completion (to_string + translate)
// ============================================================================

/// Render the vector as an s-expression (Z3's `Z3_ast_vector_to_string`):
/// `(ast-vector` then each element on its own two-space-indented line, closed by
/// `)`. An empty vector prints `(ast-vector)`. Each element is rendered by the
/// same formatter as `Z3_ast_to_string`.
///
/// # Safety
/// `c` must be a valid context pointer; `v`, when non-null, a valid vector handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_to_string(c: Z3_context, v: Z3_ast_vector) -> Z3_string {
    // Pre-extract the elements (raw deref of the distinct vector allocation).
    // SAFETY: `v`, when non-null, is a live `AstVectorHandle`; `as_ref` null-checks.
    let elems = unsafe { v.as_ref() }.map(|h| h.asts.clone());
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            let mut s = String::from("(ast-vector");
            if let Some(items) = elems {
                for a in items {
                    s.push_str("\n  ");
                    let Some(rendered) = render_ast(ctx, a, "Z3_ast_vector_to_string") else {
                        return ptr::null();
                    };
                    s.push_str(&rendered);
                }
            }
            s.push(')');
            cache_string(ctx, s)
        })
    }
}

/// Copy AST vector `v` from context `s` into a fresh vector in context `t`
/// (Z3's `Z3_ast_vector_translate`).
///
/// When `s == t` the element handles are already valid in `t`, so this returns a
/// real copy. When the contexts differ, each element's term DAG is re-interned
/// into `t`'s term store via the engine's
/// [`translate_terms_from`](ay_dpll::api::Solver::translate_terms_from) graft —
/// the same faithful deep copy `Z3_goal_translate`/`Z3_solver_translate` use,
/// never a fabricated element. The shared semantic-metadata portability gate
/// refuses a cross-context copy that would weaken context-resident semantics.
///
/// # Safety
/// `s`/`t` must be valid context pointers; `v`, when non-null, a valid vector
/// handle in `s`.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_translate(
    s: Z3_context,
    v: Z3_ast_vector,
    t: Z3_context,
) -> Z3_ast_vector {
    // Pre-extract the source element handles (raw deref; the vector lives in `s`).
    // SAFETY: `v`, when non-null, is a live `AstVectorHandle`; `as_ref` null-checks.
    let elems = unsafe { v.as_ref() }.map(|h| h.asts.clone());
    // SAFETY: `t` is the destination context; `ffi_guard_ptr` handles a null
    // context and catches panics.
    unsafe {
        ffi_guard_ptr(t, |tgt| {
            let Some(elems) = elems else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_ast_vector_translate: null vector handle".to_string());
                return ptr::null_mut();
            };
            // Same context: authenticate before copying so translation cannot
            // launder colliding handles from another context.
            if s == t {
                let _terms = require_term_asts_or_return!(
                    tgt,
                    &elems,
                    "Z3_ast_vector_translate",
                    ptr::null_mut()
                );
                tgt.last_error = Z3_OK;
                return cache_ast_vector(tgt, elems);
            }
            // Cross-context: re-intern each element's term DAG into `t`'s store.
            // SAFETY: `s != t`, so this borrow does not alias `tgt`; the deref is
            // under the enclosing `unsafe` block.
            let Some(src) = s.as_ref() else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_ast_vector_translate: null source context".to_string());
                return ptr::null_mut();
            };
            let Some(src_terms) = elems
                .iter()
                .map(|&ast| checked_ast_to_term(src, ast))
                .collect::<Option<Vec<Term>>>()
            else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some(
                    "Z3_ast_vector_translate: vector contains an invalid term or one from a different source context"
                        .to_string(),
                );
                return ptr::null_mut();
            };
            if !ensure_cross_context_translation_semantics(src, tgt, "Z3_ast_vector_translate") {
                return ptr::null_mut();
            }
            let new_terms = tgt.solver.translate_terms_from(&src.solver, &src_terms);
            if !transfer_cross_context_ffi_metadata(
                src,
                tgt,
                &src_terms,
                &new_terms,
                "Z3_ast_vector_translate",
            ) {
                return ptr::null_mut();
            }
            let new_asts: Vec<Z3_ast> = new_terms.iter().map(|&t| term_to_ast(tgt, t)).collect();
            for ((&source_term, &_term), &ast) in src_terms.iter().zip(&new_terms).zip(&new_asts) {
                let sort = src.solver.term_sort(source_term);
                record_ast_sort(tgt, ast, sort);
            }
            tgt.last_error = Z3_OK;
            cache_ast_vector(tgt, new_asts)
        })
    }
}

#[cfg(test)]
#[path = "ast_containers_ffi_tests.rs"]
mod ast_containers_ffi_tests;
