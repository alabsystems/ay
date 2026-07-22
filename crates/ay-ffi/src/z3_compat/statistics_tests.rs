// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible statistics surface
//! (`Z3_solver_get_statistics` + `Z3_stats_*`).
//!
//! Honesty is the load-bearing property: every reported value is a REAL AY
//! counter from the executor snapshot; keys map to actual counters; no
//! fabricated z3-specific stat is invented. These tests exercise the C ABI the
//! ayz3 `Solver.statistics()` wrapper rides on.

use std::ffi::{c_char, CStr};
use std::ptr;

use crate::z3_compat::*;

/// Build a fresh context + solver asserting `p` and `(not p)` (UNSAT).
///
/// # Safety
/// Test-only helper; the returned context must be freed exactly once.
unsafe fn unsat_context() -> (Z3_context, Z3_solver) {
    // SAFETY: all handles come from the `Z3_mk_*` calls and live in the context
    // arena; no pointer escapes beyond the returned context.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let bool_sort = Z3_mk_bool_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"p".as_ptr());
        let p = Z3_mk_const(ctx, sym, bool_sort);
        let not_p = Z3_mk_not(ctx, p);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, p);
        Z3_solver_assert(ctx, solver, not_p);
        (ctx, solver)
    }
}

/// Read a context-owned C string handle into an owned `String` (panics if null).
///
/// # Safety
/// `ptr` must be a valid, null-terminated, context-owned C string.
unsafe fn cstr_to_string(ptr: *const c_char) -> String {
    assert!(!ptr.is_null(), "expected non-null C string");
    // SAFETY: caller guarantees `ptr` is a valid context-owned C string.
    unsafe { CStr::from_ptr(ptr) }
        .to_str()
        .expect("stats text is valid UTF-8")
        .to_string()
}

/// Find the index of `key` in the stats handle, if present.
///
/// # Safety
/// `ctx`/`stats` must be valid handles.
unsafe fn find_key(ctx: Z3_context, stats: Z3_stats, key: &str) -> Option<c_uint> {
    // SAFETY: iterating within the reported size; keys are context-owned strings.
    unsafe {
        let n = Z3_stats_size(ctx, stats);
        for i in 0..n {
            let k = cstr_to_string(Z3_stats_get_key(ctx, stats, i));
            if k == key {
                return Some(i);
            }
        }
        None
    }
}

/// After a check, the stats handle is non-empty, every entry is exactly one of
/// uint/double, and each key is a non-empty context-owned string.
#[test]
fn stats_after_check_is_well_formed() {
    // SAFETY: single-threaded per context; context freed at end of block.
    unsafe {
        let (ctx, solver) = unsat_context();
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let stats = Z3_solver_get_statistics(ctx, solver);
        assert!(!stats.is_null(), "statistics handle must be non-null");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        let n = Z3_stats_size(ctx, stats);
        assert!(n > 0, "statistics must be non-empty after a check");

        for i in 0..n {
            let key = cstr_to_string(Z3_stats_get_key(ctx, stats, i));
            assert!(!key.is_empty(), "stat key {i} must be non-empty");
            let is_u = Z3_stats_is_uint(ctx, stats, i);
            let is_d = Z3_stats_is_double(ctx, stats, i);
            assert!(
                is_u ^ is_d,
                "stat {key} must be exactly one of uint/double (u={is_u}, d={is_d})"
            );
        }

        Z3_del_context(ctx);
    }
}

/// The core `conflicts` key is present and reads back as a uint (the z3py
/// `stats['conflicts']` path).
#[test]
fn stats_conflicts_key_reads_as_uint() {
    // SAFETY: see above.
    unsafe {
        let (ctx, solver) = unsat_context();
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let stats = Z3_solver_get_statistics(ctx, solver);
        let idx = find_key(ctx, stats, "conflicts").expect("`conflicts` key must be present");
        assert!(
            Z3_stats_is_uint(ctx, stats, idx),
            "`conflicts` must be a uint stat"
        );
        // A real counter (>= 0); reading it must not error.
        let _v = Z3_stats_get_uint_value(ctx, stats, idx);
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);

        Z3_del_context(ctx);
    }
}

/// `num assertions` reflects the REAL asserted count (honest counter, not a
/// fabricated z3 key).
#[test]
fn stats_num_assertions_reflects_real_count() {
    // SAFETY: see above.
    unsafe {
        let (ctx, solver) = unsat_context();
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let stats = Z3_solver_get_statistics(ctx, solver);
        let idx =
            find_key(ctx, stats, "num assertions").expect("`num assertions` key must be present");
        let v = Z3_stats_get_uint_value(ctx, stats, idx);
        assert_eq!(v, 2, "two assertions (p, not p) were loaded");

        Z3_del_context(ctx);
    }
}

/// Resource stats (`memory`/`max memory`/`time`) are doubles readable via the
/// double accessor.
#[test]
fn stats_resource_stats_are_doubles() {
    // SAFETY: see above.
    unsafe {
        let (ctx, solver) = unsat_context();
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let stats = Z3_solver_get_statistics(ctx, solver);
        for key in ["memory", "max memory", "time"] {
            let idx = find_key(ctx, stats, key).unwrap_or_else(|| panic!("`{key}` key present"));
            assert!(
                Z3_stats_is_double(ctx, stats, idx),
                "`{key}` must be a double stat"
            );
            let v = Z3_stats_get_double_value(ctx, stats, idx);
            assert!(v >= 0.0, "`{key}` is a non-negative resource stat");
        }
        Z3_del_context(ctx);
    }
}

/// `Z3_stats_to_string` renders the z3-style `(:key val ...)` shape and lists
/// the same keys the indexed API exposes.
#[test]
fn stats_to_string_has_z3_shape() {
    // SAFETY: see above.
    unsafe {
        let (ctx, solver) = unsat_context();
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);

        let stats = Z3_solver_get_statistics(ctx, solver);
        let text = cstr_to_string(Z3_stats_to_string(ctx, stats));
        assert!(text.starts_with('('), "stats repr must open with '('");
        assert!(text.ends_with(')'), "stats repr must close with ')'");
        assert!(
            text.contains(":conflicts"),
            "stats repr must contain :conflicts, got:\n{text}"
        );

        Z3_del_context(ctx);
    }
}

/// SAT check also yields well-formed statistics (num assertions reflects the
/// single asserted `true`).
#[test]
fn stats_after_sat_check() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let t = Z3_mk_true(ctx);
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, t);
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_TRUE);

        let stats = Z3_solver_get_statistics(ctx, solver);
        assert!(Z3_stats_size(ctx, stats) > 0);
        let idx = find_key(ctx, stats, "num assertions").expect("num assertions present");
        assert_eq!(Z3_stats_get_uint_value(ctx, stats, idx), 1);

        Z3_del_context(ctx);
    }
}

/// Before any check, a solver handle reports an all-zero (honest) statistics
/// set: the core keys exist but their counters are zero.
#[test]
fn stats_before_check_is_zeroed() {
    // SAFETY: see above.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let solver = Z3_mk_solver(ctx);

        let stats = Z3_solver_get_statistics(ctx, solver);
        assert!(!stats.is_null());
        let idx = find_key(ctx, stats, "conflicts").expect("conflicts key present pre-check");
        assert_eq!(
            Z3_stats_get_uint_value(ctx, stats, idx),
            0,
            "no check ran, so conflicts must be 0 (honest)"
        );

        Z3_del_context(ctx);
    }
}

/// Null handles are handled safely: size 0, null key, no crash.
#[test]
fn stats_null_handles_are_safe() {
    // SAFETY: passing null solver/stats is explicitly supported (returns
    // sentinels), matching the rest of the FFI surface.
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // Null solver -> non-null (empty) stats handle, all-zero.
        let stats = Z3_solver_get_statistics(ctx, ptr::null_mut());
        assert!(!stats.is_null());
        assert!(Z3_stats_size(ctx, stats) > 0);

        // Null stats handle -> safe sentinels.
        let null_stats: Z3_stats = ptr::null_mut();
        assert_eq!(Z3_stats_size(ctx, null_stats), 0);
        assert!(Z3_stats_get_key(ctx, null_stats, 0).is_null());
        assert!(!Z3_stats_is_uint(ctx, null_stats, 0));
        assert!(!Z3_stats_is_double(ctx, null_stats, 0));
        assert_eq!(Z3_stats_get_uint_value(ctx, null_stats, 0), 0);
        assert_eq!(Z3_stats_get_double_value(ctx, null_stats, 0), 0.0);
        assert!(Z3_stats_to_string(ctx, null_stats).is_null());

        // inc/dec ref are safe no-ops.
        Z3_stats_inc_ref(ctx, stats);
        Z3_stats_dec_ref(ctx, stats);

        Z3_del_context(ctx);
    }
}

/// Out-of-range index is handled safely (null key, zero values).
#[test]
fn stats_out_of_range_index_is_safe() {
    // SAFETY: see above.
    unsafe {
        let (ctx, solver) = unsat_context();
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
        let stats = Z3_solver_get_statistics(ctx, solver);
        let n = Z3_stats_size(ctx, stats);

        assert!(Z3_stats_get_key(ctx, stats, n).is_null());
        assert!(!Z3_stats_is_uint(ctx, stats, n));
        assert!(!Z3_stats_is_double(ctx, stats, n));
        assert_eq!(Z3_stats_get_uint_value(ctx, stats, n), 0);
        assert_eq!(Z3_stats_get_double_value(ctx, stats, n), 0.0);

        Z3_del_context(ctx);
    }
}
