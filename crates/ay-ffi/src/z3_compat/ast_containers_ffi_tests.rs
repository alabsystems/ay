// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible AST-container C API (`ast_containers.rs`):
//! the `Z3_ast_map_*` family and the `Z3_ast_vector_to_string` /
//! `Z3_ast_vector_translate` completions.
//!
//! Every expected value/string is the value libz3 4.15.4 reports for the same
//! container (pinned by `tests/capi_ast_containers_consumer.c`, which runs the
//! identical assertions against both ay-ffi and libz3). Coverage:
//! - map: create → insert 3 pairs → contains/find/size/keys → erase (size
//!   drops, contains false) → reset (size 0), plus `to_string`.
//! - HONEST find on an absent key: `0` + `Z3_INVALID_ARG` (never a fake value).
//! - vector `to_string` (z3 `(ast-vector …)` shape) and cross-context
//!   `translate` (elements re-readable in the destination context).

use super::super::*;
use std::ffi::CStr;

/// Build a fresh context.
///
/// # Safety
/// The returned context must be freed by the caller with `Z3_del_context`.
unsafe fn mk_ctx() -> Z3_context {
    // SAFETY: standard context construction; single-threaded test.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        ctx
    }
}

/// An Int-sorted constant named `n`.
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn int_var(ctx: Z3_context, n: &CStr) -> Z3_ast {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, n.as_ptr()),
            Z3_mk_int_sort(ctx),
        )
    }
}

/// Read a `Z3_string` result as a `&str`.
///
/// # Safety
/// `p` must be a valid, NUL-terminated pointer owned by the context.
unsafe fn s(p: Z3_string) -> String {
    // SAFETY: `p` is a context-owned C string per the caller's contract.
    unsafe {
        CStr::from_ptr(p)
            .to_str()
            .expect("Z3 string result must be valid UTF-8")
            .to_string()
    }
}

#[test]
fn test_ast_map_lifecycle() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let i = Z3_mk_int_sort(ctx);
        let x = int_var(ctx, c"x");
        let y = int_var(ctx, c"y");
        let z = int_var(ctx, c"z");
        let one = Z3_mk_int(ctx, 1, i);
        let two = Z3_mk_int(ctx, 2, i);
        let three = Z3_mk_int(ctx, 3, i);

        let m = Z3_mk_ast_map(ctx);
        Z3_ast_map_inc_ref(ctx, m);
        assert!(!m.is_null(), "mk_ast_map non-null");
        assert_eq!(Z3_ast_map_size(ctx, m), 0, "fresh map is empty");

        // Insert 3 key -> value pairs.
        Z3_ast_map_insert(ctx, m, x, one);
        Z3_ast_map_insert(ctx, m, y, two);
        Z3_ast_map_insert(ctx, m, z, three);
        assert_eq!(Z3_ast_map_size(ctx, m), 3, "size after 3 inserts");

        // contains / find return the REAL stored values.
        assert!(Z3_ast_map_contains(ctx, m, x));
        assert!(Z3_ast_map_contains(ctx, m, y));
        assert!(Z3_ast_map_contains(ctx, m, z));
        assert_eq!(Z3_ast_map_find(ctx, m, x), one, "find x == 1");
        assert_eq!(Z3_ast_map_find(ctx, m, y), two, "find y == 2");
        assert_eq!(Z3_ast_map_find(ctx, m, z), three, "find z == 3");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK, "find hit leaves OK");

        // Re-insert an existing key replaces the value, keeps size + position.
        Z3_ast_map_insert(ctx, m, x, three);
        assert_eq!(Z3_ast_map_size(ctx, m), 3, "re-insert keeps size");
        assert_eq!(
            Z3_ast_map_find(ctx, m, x),
            three,
            "re-insert replaces value"
        );

        // keys() is a real vector of the 3 keys, in insertion order.
        let keys = Z3_ast_map_keys(ctx, m);
        Z3_ast_vector_inc_ref(ctx, keys);
        assert_eq!(Z3_ast_vector_size(ctx, keys), 3, "keys size");
        assert_eq!(Z3_ast_vector_get(ctx, keys, 0), x);
        assert_eq!(Z3_ast_vector_get(ctx, keys, 1), y);
        assert_eq!(Z3_ast_vector_get(ctx, keys, 2), z);

        // Erase one: size drops, contains=false, find errors honestly.
        Z3_ast_map_erase(ctx, m, y);
        assert_eq!(Z3_ast_map_size(ctx, m), 2, "size after erase");
        assert!(!Z3_ast_map_contains(ctx, m, y), "erased key absent");
        assert_eq!(Z3_ast_map_find(ctx, m, y), 0, "find of absent key -> 0");
        assert_eq!(
            Z3_get_error_code(ctx),
            Z3_INVALID_ARG,
            "absent find sets INVALID_ARG"
        );
        // Surviving keys still there.
        assert!(Z3_ast_map_contains(ctx, m, x));
        assert!(Z3_ast_map_contains(ctx, m, z));

        // Reset: empty.
        Z3_ast_map_reset(ctx, m);
        assert_eq!(Z3_ast_map_size(ctx, m), 0, "size after reset");
        assert!(!Z3_ast_map_contains(ctx, m, x), "no keys after reset");

        Z3_del_context(ctx);
    }
}

#[test]
fn test_ast_map_to_string() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let i = Z3_mk_int_sort(ctx);
        let x = int_var(ctx, c"x");
        let three = Z3_mk_int(ctx, 3, i);

        // Empty map renders (ast-map).
        let m = Z3_mk_ast_map(ctx);
        Z3_ast_map_inc_ref(ctx, m);
        assert_eq!(s(Z3_ast_map_to_string(ctx, m)), "(ast-map)");

        // Single entry: exact byte match to libz3 4.15.4.
        Z3_ast_map_insert(ctx, m, x, three);
        assert_eq!(s(Z3_ast_map_to_string(ctx, m)), "(ast-map\n  (x\n   3))");

        Z3_del_context(ctx);
    }
}

#[test]
fn test_ast_vector_to_string() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let i = Z3_mk_int_sort(ctx);
        let x = int_var(ctx, c"x");
        let y = int_var(ctx, c"y");
        let three = Z3_mk_int(ctx, 3, i);

        // Empty vector renders (ast-vector).
        let v = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_inc_ref(ctx, v);
        assert_eq!(s(Z3_ast_vector_to_string(ctx, v)), "(ast-vector)");

        // Vector order is deterministic (push order) — exact match to libz3.
        Z3_ast_vector_push(ctx, v, x);
        Z3_ast_vector_push(ctx, v, y);
        Z3_ast_vector_push(ctx, v, three);
        assert_eq!(
            s(Z3_ast_vector_to_string(ctx, v)),
            "(ast-vector\n  x\n  y\n  3)"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn test_ast_vector_translate_same_context() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let x = int_var(ctx, c"x");
        let y = int_var(ctx, c"y");
        let v = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_inc_ref(ctx, v);
        Z3_ast_vector_push(ctx, v, x);
        Z3_ast_vector_push(ctx, v, y);

        // Same-context translate is a real copy: handles are still valid here.
        let v2 = Z3_ast_vector_translate(ctx, v, ctx);
        assert!(!v2.is_null());
        assert_eq!(Z3_ast_vector_size(ctx, v2), 2);
        assert_eq!(Z3_ast_vector_get(ctx, v2, 0), x);
        assert_eq!(Z3_ast_vector_get(ctx, v2, 1), y);

        Z3_del_context(ctx);
    }
}

#[test]
fn test_ast_vector_translate_cross_context() {
    // SAFETY: all handles allocated/freed within these blocks; single-threaded.
    unsafe {
        let src = mk_ctx();
        let dst = mk_ctx();
        let i = Z3_mk_int_sort(src);
        let x = int_var(src, c"x");
        let y = int_var(src, c"y");
        let f = Z3_mk_lt(src, x, Z3_mk_add(src, 2, [x, y].as_ptr()));

        let v = Z3_mk_ast_vector(src);
        Z3_ast_vector_inc_ref(src, v);
        Z3_ast_vector_push(src, v, x);
        Z3_ast_vector_push(src, v, f);
        let _ = i;

        // Cross-context translate re-interns the term DAG into `dst`.
        let tv = Z3_ast_vector_translate(src, v, dst);
        assert!(!tv.is_null(), "translate non-null");
        assert_eq!(Z3_ast_vector_size(dst, tv), 2, "translated size");
        // Translated elements are re-readable in `dst` and render identically.
        assert_eq!(s(Z3_ast_to_string(dst, Z3_ast_vector_get(dst, tv, 0))), "x");
        assert_eq!(
            s(Z3_ast_vector_to_string(dst, tv)),
            "(ast-vector\n  x\n  (< x (+ x y)))",
            "translated vector renders in dst"
        );

        Z3_del_context(src);
        Z3_del_context(dst);
    }
}

#[test]
fn test_ast_map_null_and_empty_safety() {
    // SAFETY: single-threaded; exercises null-handle robustness.
    unsafe {
        let ctx = mk_ctx();
        // Operations on a null map handle are safe no-ops / honest zeros.
        assert_eq!(Z3_ast_map_size(ctx, ptr::null_mut()), 0);
        assert!(!Z3_ast_map_contains(ctx, ptr::null_mut(), 1));
        assert_eq!(Z3_ast_map_find(ctx, ptr::null_mut(), 1), 0);
        Z3_ast_map_insert(ctx, ptr::null_mut(), 1, 2); // no crash
        Z3_ast_map_erase(ctx, ptr::null_mut(), 1); // no crash
        Z3_ast_map_reset(ctx, ptr::null_mut()); // no crash
        Z3_del_context(ctx);
    }
}
