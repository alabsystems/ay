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

use ay_dpll::api::FuncDecl;
use std::ffi::c_uint;
use std::ptr;

use super::{
    cache_func_interp, ffi_guard_ptr, ffi_guard_void, require_term_ast_or_return, Z3_ast,
    Z3_context, Z3_func_decl, Z3_func_interp, Z3_model, Z3_INVALID_ARG, Z3_OK,
};

/// Model enumeration can return synthetic handles for an existing declaration.
/// Match their semantic key and signature without treating that description as
/// declaration authority for constructing solver terms.
pub(super) fn same_model_declaration(left: &FuncDecl, right: &FuncDecl) -> bool {
    left.declaration_identity_name() == right.declaration_identity_name()
        && left.domain() == right.domain()
        && left.range() == right.range()
}

/// Assign a constant interpretation `f := a` in model `m`.
///
/// Records the mapping on `m`'s user constant-interpretation map; a subsequent
/// `Z3_model_get_const_interp(c, m, f)` returns exactly `a`. Intended for models
/// created with [`Z3_mk_model`](super::Z3_mk_model). `f` should be a nullary
/// declaration (a constant). Reassigning the same declaration replaces its
/// previous interpretation.
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
    if m.is_null() {
        return;
    }
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `m` is a
    // separate arena allocation from the context, so `&mut *m` cannot alias
    // `&mut Z3Context`.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if f.is_null() || (*f).decl.arity() != 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("constant interpretation requires a nullary declaration".into());
                return;
            }
            if a != 0 {
                let _term = require_term_ast_or_return!(
                    ctx,
                    a,
                    "Z3_add_const_interp",
                    "interpretation value",
                );
            }
            let decl = &(*f).decl;
            let handle = &mut *m;
            if let Some((_, value)) = handle
                .user_const_interps
                .iter_mut()
                .find(|(previous, _)| same_model_declaration(previous, decl))
            {
                *value = a;
            } else {
                handle.user_const_interps.push((decl.clone(), a));
            }
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
/// returns this same handle (matched by declaration identity and signature).
/// Reassigning the same declaration replaces its previous interpretation. The handle is
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
            let decl = &(*f).decl;
            let arity = decl.arity() as c_uint;
            // Fresh, empty interpretation with the caller's else value. Arena
            // registration happens inside `cache_func_interp`.
            let interp = cache_func_interp(ctx, arity, Vec::new(), default_value);
            let handle = &mut *m;
            if let Some((_, value)) = handle
                .user_func_interps
                .iter_mut()
                .find(|(previous, _)| same_model_declaration(previous, decl))
            {
                *value = interp;
            } else {
                handle.user_func_interps.push((decl.clone(), interp));
            }
            ctx.last_error = Z3_OK;
            interp
        })
    }
}
