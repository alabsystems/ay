// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-construction C API: `Z3_add_const_interp` / `Z3_add_func_interp`.
//!
//! These let a caller populate a model created by [`Z3_mk_model`] with concrete
//! interpretations, then read them back through the ordinary model accessors.
//! The interpretations are stored on the [`ModelHandle`](super::ModelHandle)'s
//! user maps (`user_const_interps` / `user_func_interps`), which
//! `Z3_model_get_const_interp` and `Z3_model_get_func_interp` consult FIRST — so
//! a hand-built model round-trips exactly what was stored.
//!
//! Nothing here is fabricated: `Z3_add_const_interp` stores the caller's own
//! value AST verbatim, and `Z3_add_func_interp` returns a REAL, empty
//! `Z3_func_interp` handle (arena-owned, ref-counted no-op) the caller then
//! populates via `Z3_func_interp_add_entry` / `Z3_func_interp_set_else`.

use std::ffi::c_uint;
use std::ptr;

use super::{
    cache_func_interp, ffi_guard_ptr, ffi_guard_void, require_term_ast_or_return, Z3_ast,
    Z3_context, Z3_func_decl, Z3_func_interp, Z3_model, Z3_OK,
};

/// Assign a constant interpretation `f := a` in model `m`.
///
/// Records the mapping on `m`'s user constant-interpretation map; a subsequent
/// `Z3_model_get_const_interp(c, m, f)` returns exactly `a`. Intended for models
/// created with [`Z3_mk_model`](super::Z3_mk_model). `f` should be a nullary
/// declaration (a constant); its arity is not enforced, but only the decl NAME
/// is used for lookup.
///
/// # Safety
/// `c` must be a valid context pointer; `m` a valid model handle; `f` a valid
/// func_decl handle; `a` a valid `Z3_ast` (or `0`).
#[no_mangle]
pub unsafe extern "C" fn Z3_add_const_interp(
    c: Z3_context,
    m: Z3_model,
    f: Z3_func_decl,
    a: Z3_ast,
) {
    if m.is_null() || f.is_null() {
        return;
    }
    // SAFETY: `f` was null-checked; clone the decl out before entering the guard
    // (raw-pointer field read, arena-owned and single-threaded per API contract).
    let decl = unsafe { (*f).decl.clone() };
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `m` is a
    // separate arena allocation from the context, so `&mut *m` cannot alias
    // `&mut Z3Context`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if a != 0 {
                let _term = require_term_ast_or_return!(
                    ctx,
                    a,
                    "Z3_add_const_interp",
                    "interpretation value",
                );
            }
            let handle = &mut *m;
            handle.user_const_interps.push((decl, a));
            ctx.last_error = Z3_OK;
        });
    }
}

/// Create and attach a fresh function interpretation for `f` in model `m`, with
/// default (`else`) value `default_value`, returning the new `Z3_func_interp`.
///
/// The handle starts with no entries; the caller adds points with
/// `Z3_func_interp_add_entry` and may change the default with
/// `Z3_func_interp_set_else`. A subsequent `Z3_model_get_func_interp(c, m, f)`
/// returns this same handle (matched by decl name + arity). The handle is
/// arena-owned by the context (freed at `Z3_del_context`).
///
/// # Safety
/// `c` must be a valid context pointer; `m` a valid model handle; `f` a valid
/// func_decl handle; `default_value` a valid `Z3_ast` (or `0`).
#[no_mangle]
pub unsafe extern "C" fn Z3_add_func_interp(
    c: Z3_context,
    m: Z3_model,
    f: Z3_func_decl,
    default_value: Z3_ast,
) -> Z3_func_interp {
    if m.is_null() || f.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `f` was null-checked; read the decl (clone) and its arity before
    // the guard (raw-pointer field reads).
    let decl = unsafe { (*f).decl.clone() };
    let arity = unsafe { (*f).decl.arity() } as c_uint;
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics; `m` is a
    // separate arena allocation, so `&mut *m` cannot alias `&mut Z3Context`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if default_value != 0 {
                let _term = require_term_ast_or_return!(
                    ctx,
                    default_value,
                    "Z3_add_func_interp",
                    "default value",
                    ptr::null_mut()
                );
            }
            // Fresh, empty interpretation with the caller's else value. Arena
            // registration happens inside `cache_func_interp`.
            let interp = cache_func_interp(ctx, arity, Vec::new(), default_value);
            let handle = &mut *m;
            handle.user_func_interps.push((decl, interp));
            ctx.last_error = Z3_OK;
            interp
        })
    }
}
