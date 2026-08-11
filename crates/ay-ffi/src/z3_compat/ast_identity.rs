// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST identity, comparison, symbol, and sort introspection.
//!
//! Split from accessors.rs for file size compliance. Implements Z3 API
//! functions for AST equality, hashing, FuncDecl comparison/stringification,
//! symbol kind inspection, and sort identity/naming.

use std::ffi::{c_char, c_int, c_uint};
use std::ptr;

use super::{
    cache_string, cache_symbol, cache_symbol_key, ffi_guard_const_ptr, ffi_guard_int,
    ffi_guard_ptr, ffi_guard_uint, Z3_ast, Z3_context, Z3_func_decl, Z3_sort, Z3_symbol,
};

// ============================================================================
// AST identity and comparison
// ============================================================================

/// Check if two AST nodes are equal (same internal ID).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_eq_ast(_c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> bool {
    t1 == t2
}

/// Band a tagged sort/func-decl AST handle into a 32-bit id.
///
/// Sorts → `0x8000_0000 | sort_id` (mirrors z3's own observed banding: real
/// z3 4.15.4 reports sort-ast ids with the high bit set, e.g. `0x8000000B`
/// for `Int`), decls → `0xC000_0000 | decl_ast_idx`. Collision with a term id
/// would require ≥ 2^31 interned terms — unreachable in practice, and z3's
/// own ids are banded the same way. `None` for untagged (term) handles.
fn tagged_ast_id(a: Z3_ast) -> Option<c_uint> {
    match a & super::HANDLE_TAG_MASK {
        super::SORT_AST_TAG => Some(0x8000_0000 | (a & !super::HANDLE_TAG_MASK) as c_uint),
        super::FUNC_DECL_AST_TAG => Some(0xC000_0000 | (a & !super::HANDLE_TAG_MASK) as c_uint),
        _ => None,
    }
}

/// Get a unique identifier for an AST node.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_id(_c: Z3_context, a: Z3_ast) -> c_uint {
    tagged_ast_id(a).unwrap_or(a as c_uint)
}

/// Get a hash value for an AST node (same as the ID for AY).
///
/// A hash collision with a term hash is legal (dict semantics rely on
/// `__eq__` = `Z3_is_eq_ast`'s exact u64 compare).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_hash(_c: Z3_context, a: Z3_ast) -> c_uint {
    tagged_ast_id(a).unwrap_or(a as c_uint)
}

// ============================================================================
// FuncDecl conversions and comparison
// ============================================================================

/// Convert a func_decl to an AST (Z3's `Z3_func_decl_to_ast`).
///
/// Returns a value-canonical, context-salted tagged handle, interned on the
/// declaration's semantic identity: two handles for the same
/// name/domain/range/params/dt-op in one context mint the SAME ast, so
/// `Z3_is_eq_ast` / `Z3_get_ast_id` / hashing behave like z3's hash-consed decl
/// asts.
/// `Z3_to_func_decl` round-trips to the canonical `Z3_func_decl`. The tag
/// keeps the handle disjoint from every term; leaking it into a term-consuming
/// entry point fails closed via authenticated term-handle decoding. A null decl
/// returns the null AST (`0`), as does a declaration owned by another context.
///
/// # Safety
/// `c` must be a valid context pointer; `d`, when non-null, a valid func_decl
/// handle owned by `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_decl_to_ast(c: Z3_context, d: Z3_func_decl) -> Z3_ast {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ast`
    // handles the null case and catches panics. `d` is null-checked above and
    // owned by the context arena per the safety contract.
    unsafe {
        super::ffi_guard_ast(c, |ctx| {
            if !ctx.func_decl_cache.contains(&d) {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_func_decl_to_ast: declaration handle belongs to a different context"
                        .to_string(),
                );
                return 0;
            }
            ctx.last_error = super::Z3_OK;
            super::func_decl_handle_to_ast(ctx, d)
        })
    }
}

/// Check if two func_decl handles are equal (pointer equality).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_eq_func_decl(
    c: Z3_context,
    f1: Z3_func_decl,
    f2: Z3_func_decl,
) -> bool {
    if f1.is_null() || f2.is_null() {
        return f1 == f2;
    }
    // Guard the pointer dereferences
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |_ctx| {
            let d1 = &(*f1).decl;
            let d2 = &(*f2).decl;
            i32::from(d1 == d2)
        }) != 0
    }
}

/// Convert a func_decl to a string representation.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_func_decl_to_string(c: Z3_context, d: Z3_func_decl) -> *const c_char {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if d.is_null() {
                return cache_string(ctx, "(null)".to_string());
            }
            let handle = &*d;
            let decl = &handle.decl;
            let display_name = handle
                .symbol
                .as_ref()
                .map(super::SymbolKey::display_name)
                .unwrap_or_else(|| decl.name().to_string());
            let (domain, range) = ctx
                .finite_set_decl_signatures
                .get(decl.name())
                .cloned()
                .unwrap_or_else(|| (decl.domain().to_vec(), decl.range().clone()));
            let domain = domain
                .iter()
                .map(|sort| super::render_public_sort(ctx, sort))
                .collect::<Vec<_>>()
                .join(" ");
            let rendered = format!(
                "(declare-fun {} ({domain}) {})",
                ay_core::quote_symbol(&display_name),
                super::render_public_sort(ctx, &range)
            );
            cache_string(ctx, rendered)
        })
    }
}

// ============================================================================
// Symbol introspection
// ============================================================================

/// Get the kind of a symbol.
///
/// Returns 0 for int symbol (Z3_INT_SYMBOL), 1 for string symbol (Z3_STRING_SYMBOL).
/// Integer and string symbol kinds are retained explicitly in the handle.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_symbol_kind(c: Z3_context, s: Z3_symbol) -> c_uint {
    if s.is_null() {
        return 1; // string kind
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 1, |_ctx| {
            match &(*s).key {
                super::SymbolKey::Integer(_) => 0, // Z3_INT_SYMBOL
                super::SymbolKey::String(_) => 1,  // Z3_STRING_SYMBOL
            }
        })
    }
}

/// Get the integer value of an int symbol.
///
/// Returns -1 if the symbol is not an integer symbol.
/// Integer and string symbol kinds are retained explicitly in the handle.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_symbol_int(c: Z3_context, s: Z3_symbol) -> c_int {
    if s.is_null() {
        return -1;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, -1, |_ctx| match &(*s).key {
            super::SymbolKey::Integer(value) => *value,
            super::SymbolKey::String(_) => -1,
        })
    }
}

// ============================================================================
// Sort identity and naming
// ============================================================================

/// Get the name of a sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort_name(c: Z3_context, s: Z3_sort) -> Z3_symbol {
    if s.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let sort = &(*s).sort;
            if super::finite_set_basis(ctx, sort).is_some() {
                cache_symbol(ctx, "FiniteSet".to_string())
            } else if let Some(symbol) = ctx.ffi_sort_symbols.get(sort).cloned() {
                cache_symbol_key(ctx, symbol)
            } else {
                cache_symbol(ctx, format!("{sort}"))
            }
        })
    }
}

/// Check if two sorts are equal.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_eq_sort(c: Z3_context, s1: Z3_sort, s2: Z3_sort) -> bool {
    if s1.is_null() || s2.is_null() {
        return s1 == s2;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |_ctx| {
            let sort1 = &(*s1).sort;
            let sort2 = &(*s2).sort;
            i32::from(sort1 == sort2)
        }) != 0
    }
}

/// Get the unique ID of a sort.
///
/// Returns a stable semantic sort ID: same `Sort` value → same ID within
/// this context. Different sorts → different IDs. Null → 0. (#6580)
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort_id(_c: Z3_context, s: Z3_sort) -> c_uint {
    if s.is_null() {
        return 0;
    }
    // SAFETY: `s` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort_id` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    unsafe { (*s).sort_id }
}
