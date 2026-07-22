// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Z3-compatible Goal completion + Probe C API
//! (`goals.rs` / `probes.rs`).
//!
//! Every expected value is the value libz3 4.15.4 reports for the same goal
//! (cross-checked by `tests/capi_goal_probe_consumer.c` compiled against both
//! ay-ffi and libz3). Coverage:
//! - Goal readback: `size`, `num_exprs`, `precision`, `depth`, `is_decided_sat`
//!   / `is_decided_unsat` / `inconsistent`, `to_string`, `reset`.
//! - Probes: `num-consts`, `num-bool-consts`, `is-qflia`, `is-qfbv`,
//!   `is-propositional`, `is-lia`, `has-quantifiers`, and the combinators
//!   (`const`/`eq`/`gt`/`le`/`and`/`or`/`not`).
//! - HONEST handling: an unknown/unimplemented probe name returns NULL +
//!   `Z3_INVALID_ARG`.
//! - `Z3_goal_translate` cross-context deep copy.

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

/// A Bool-sorted constant named `n`.
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn bool_var(ctx: Z3_context, n: &CStr) -> Z3_ast {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, n.as_ptr()),
            Z3_mk_bool_sort(ctx),
        )
    }
}

/// Build the QF_LIA goal `(< 0 x), (< y 10), (< z (+ x y))` (3 int vars).
///
/// # Safety
/// `ctx` must be a valid context handle.
unsafe fn lia_goal(ctx: Z3_context) -> Z3_goal {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let i = Z3_mk_int_sort(ctx);
        let x = int_var(ctx, c"x");
        let y = int_var(ctx, c"y");
        let z = int_var(ctx, c"z");
        let f1 = Z3_mk_lt(ctx, Z3_mk_int(ctx, 0, i), x);
        let f2 = Z3_mk_lt(ctx, y, Z3_mk_int(ctx, 10, i));
        let sum_args = [x, y];
        let f3 = Z3_mk_lt(ctx, z, Z3_mk_add(ctx, 2, sum_args.as_ptr()));
        let g = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, g, f1);
        Z3_goal_assert(ctx, g, f2);
        Z3_goal_assert(ctx, g, f3);
        g
    }
}

/// Apply a named probe to a goal.
///
/// # Safety
/// `ctx`/`g` must be valid handles.
unsafe fn probe(ctx: Z3_context, name: &CStr, g: Z3_goal) -> f64 {
    // SAFETY: forwarded under the caller's contract.
    unsafe {
        let p = Z3_mk_probe(ctx, name.as_ptr());
        assert!(!p.is_null(), "probe {name:?} should be supported");
        Z3_probe_apply(ctx, p, g)
    }
}

#[test]
fn test_goal_readback_lia() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let g = lia_goal(ctx);

        assert_eq!(Z3_goal_size(ctx, g), 3);
        assert_eq!(Z3_goal_num_exprs(ctx, g), 9);
        assert_eq!(Z3_goal_depth(ctx, g), 0);
        assert_eq!(Z3_goal_precision(ctx, g), Z3_GOAL_PRECISE);
        assert!(!Z3_goal_is_decided_sat(ctx, g));
        assert!(!Z3_goal_is_decided_unsat(ctx, g));
        assert!(!Z3_goal_inconsistent(ctx, g));
        assert_ne!(Z3_goal_formula(ctx, g, 0), 0);
        assert_ne!(Z3_goal_formula(ctx, g, 2), 0);
        // Out-of-range formula index -> 0 + Z3_INVALID_ARG.
        assert_eq!(Z3_goal_formula(ctx, g, 3), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);

        let s = CStr::from_ptr(Z3_goal_to_string(ctx, g))
            .to_str()
            .expect("LIA goal rendering must be valid UTF-8");
        assert_eq!(s, "(goal\n  (< 0 x)\n  (< y 10)\n  (< z (+ x y)))");

        Z3_del_context(ctx);
    }
}

#[test]
fn test_probes_lia_match_z3() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let g = lia_goal(ctx);

        assert_eq!(probe(ctx, c"num-consts", g), 3.0);
        assert_eq!(probe(ctx, c"num-exprs", g), 9.0);
        assert_eq!(probe(ctx, c"size", g), 3.0);
        assert_eq!(probe(ctx, c"depth", g), 0.0);
        assert_eq!(probe(ctx, c"num-arith-consts", g), 3.0);
        assert_eq!(probe(ctx, c"num-bool-consts", g), 0.0);
        assert_eq!(probe(ctx, c"has-quantifiers", g), 0.0);
        assert_eq!(probe(ctx, c"is-qflia", g), 1.0);
        assert_eq!(probe(ctx, c"is-qflira", g), 1.0);
        assert_eq!(probe(ctx, c"is-lia", g), 1.0);
        assert_eq!(probe(ctx, c"is-qfbv", g), 0.0);
        assert_eq!(probe(ctx, c"is-qflra", g), 0.0);
        assert_eq!(probe(ctx, c"is-propositional", g), 0.0);
        assert_eq!(probe(ctx, c"is-qfnia", g), 0.0);

        Z3_del_context(ctx);
    }
}

#[test]
fn test_probe_combinators() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let g = lia_goal(ctx);

        let nc = Z3_mk_probe(ctx, c"num-consts".as_ptr());
        let three = Z3_probe_const(ctx, 3.0);
        assert_eq!(Z3_probe_apply(ctx, three, g), 3.0);
        assert_eq!(Z3_probe_apply(ctx, Z3_probe_eq(ctx, nc, three), g), 1.0);
        assert_eq!(Z3_probe_apply(ctx, Z3_probe_gt(ctx, nc, three), g), 0.0);
        assert_eq!(Z3_probe_apply(ctx, Z3_probe_le(ctx, nc, three), g), 1.0);
        let qflia = Z3_mk_probe(ctx, c"is-qflia".as_ptr());
        let eq = Z3_probe_eq(ctx, nc, three);
        assert_eq!(Z3_probe_apply(ctx, Z3_probe_and(ctx, eq, qflia), g), 1.0);
        assert_eq!(Z3_probe_apply(ctx, Z3_probe_not(ctx, qflia), g), 0.0);
        let gt = Z3_probe_gt(ctx, nc, three);
        assert_eq!(Z3_probe_apply(ctx, Z3_probe_or(ctx, gt, qflia), g), 1.0);

        Z3_del_context(ctx);
    }
}

#[test]
fn test_bool_goal_propositional() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let a = bool_var(ctx, c"a");
        let b = bool_var(ctx, c"b");
        let or_args = [a, b];
        let g = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, g, Z3_mk_or(ctx, 2, or_args.as_ptr()));
        Z3_goal_assert(ctx, g, a);

        assert_eq!(Z3_goal_size(ctx, g), 2);
        assert_eq!(Z3_goal_num_exprs(ctx, g), 3);
        assert_eq!(probe(ctx, c"num-consts", g), 0.0);
        assert_eq!(probe(ctx, c"num-bool-consts", g), 2.0);
        assert_eq!(probe(ctx, c"is-propositional", g), 1.0);
        // Propositional logic is a subset of QF_LIA / QF_BV (matches libz3).
        assert_eq!(probe(ctx, c"is-qflia", g), 1.0);
        assert_eq!(probe(ctx, c"is-qfbv", g), 1.0);
        let s = CStr::from_ptr(Z3_goal_to_string(ctx, g))
            .to_str()
            .expect("Boolean goal rendering must be valid UTF-8");
        assert_eq!(s, "(goal\n  (or a b)\n  a)");

        Z3_del_context(ctx);
    }
}

#[test]
fn test_empty_and_false_goals() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();

        let empty = Z3_mk_goal(ctx, false, false, false);
        assert_eq!(Z3_goal_size(ctx, empty), 0);
        assert!(Z3_goal_is_decided_sat(ctx, empty));
        assert!(!Z3_goal_is_decided_unsat(ctx, empty));
        let es = CStr::from_ptr(Z3_goal_to_string(ctx, empty))
            .to_str()
            .expect("empty goal rendering must be valid UTF-8");
        assert_eq!(es, "(goal)");

        let gf = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, gf, Z3_mk_false(ctx));
        assert_eq!(Z3_goal_size(ctx, gf), 1);
        assert!(Z3_goal_inconsistent(ctx, gf));
        assert!(Z3_goal_is_decided_unsat(ctx, gf));
        assert!(!Z3_goal_is_decided_sat(ctx, gf));
        let fs = CStr::from_ptr(Z3_goal_to_string(ctx, gf))
            .to_str()
            .expect("false goal rendering must be valid UTF-8");
        assert_eq!(fs, "(goal\n  false)");

        Z3_del_context(ctx);
    }
}

#[test]
fn test_goal_reset() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let g = lia_goal(ctx);
        assert_eq!(Z3_goal_size(ctx, g), 3);
        Z3_goal_reset(ctx, g);
        assert_eq!(Z3_goal_size(ctx, g), 0);
        assert!(Z3_goal_is_decided_sat(ctx, g));
        Z3_del_context(ctx);
    }
}

#[test]
fn test_unknown_probe_is_honest_null() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        // A bogus (non-z3) name -> NULL + Z3_INVALID_ARG.
        assert!(Z3_mk_probe(ctx, c"not-a-probe".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(ctx), Z3_INVALID_ARG);
        // Every REAL z3-4.15.4 probe name is now registered (the p3-tactics
        // batch closed the probe-name gap): `arith-max-deg` builds and
        // evaluates. On {x > 5} the atom sides are x (degree 1) and 5
        // (degree 0) -> max 1.0, byte-equal to libz3 (measured).
        let p = Z3_mk_probe(ctx, c"arith-max-deg".as_ptr());
        assert!(!p.is_null(), "arith-max-deg is a real z3 probe: must build");
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        Z3_del_context(ctx);
    }
}

#[test]
fn test_new_probe_values_match_measured_z3() {
    // Values cross-checked against libz3 4.15.4 (2026-07-18 battery) on the
    // LIA goal {(< 0 x), (< y 10), (< z (+ x y))} and simple variants.
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        let g = lia_goal(ctx);

        // x/z have only lower/no bounds -> unbounded reads 1 (libz3: 1.0).
        assert_eq!(probe(ctx, c"is-unbounded", g), 1.0);
        // Linear int-only goal without Boolean constants -> ILP (libz3: 1.0).
        assert_eq!(probe(ctx, c"is-ilp", g), 1.0);
        // Linear goal -> NOT NIRA (libz3 requires genuine nonlinearity: 0.0).
        assert_eq!(probe(ctx, c"is-nira", g), 0.0);
        // No quantifiers anywhere -> no patterns (libz3: 0.0).
        assert_eq!(probe(ctx, c"has-patterns", g), 0.0);
        // No uninterpreted functions -> zero Ackermann lemmas (libz3: 0.0).
        assert_eq!(probe(ctx, c"ackr-bound-probe", g), 0.0);
        // Numerals {0, 10}: bit widths {1, 4} -> max 4 (libz3 measured
        // convention: bits(|n|) with 0 reading 1).
        assert_eq!(probe(ctx, c"arith-max-bw", g), 4.0);
        // Atom sides: 0,x | y,10 | z,(+ x y) -> degrees 0,1,1,0,1,1 -> max 1.
        assert_eq!(probe(ctx, c"arith-max-deg", g), 1.0);
        assert_eq!(probe(ctx, c"arith-avg-deg", g), 4.0 / 6.0);
        // Goal flags match z3's default goal (measured 1/0/0).
        assert_eq!(probe(ctx, c"produce-model", g), 1.0);
        assert_eq!(probe(ctx, c"produce-proofs", g), 0.0);
        assert_eq!(probe(ctx, c"produce-unsat-cores", g), 0.0);
        // Documented conservative reads (never fabricated): memory meters 0.
        assert_eq!(probe(ctx, c"memory", g), 0.0);

        Z3_del_context(ctx);
    }
}

#[test]
fn test_probe_introspection() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        // The registry covers every z3-4.15.4 probe name (z3 -probes: 42).
        assert_eq!(Z3_get_num_probes(ctx), 42);
        let name0 = Z3_get_probe_name(ctx, 0);
        assert!(!name0.is_null());
        let descr = Z3_probe_get_descr(ctx, c"is-qflia".as_ptr());
        assert!(!descr.is_null());
        let d = CStr::from_ptr(descr)
            .to_str()
            .expect("probe description must be valid UTF-8");
        assert_eq!(d, "true if the goal is in QF_LIA.");
        // Every enumerated probe name is buildable via Z3_mk_probe and has a
        // description (registry lock-step, both directions).
        let n = Z3_get_num_probes(ctx);
        for i in 0..n {
            let name = Z3_get_probe_name(ctx, i);
            assert!(!name.is_null(), "probe name {i} must be non-null");
            let p = Z3_mk_probe(ctx, name);
            assert!(!p.is_null(), "enumerated probe {i} must be buildable");
            let d = Z3_probe_get_descr(ctx, name);
            assert!(!d.is_null(), "enumerated probe {i} must have a descr");
        }
        Z3_del_context(ctx);
    }
}

#[test]
fn test_goal_translate_cross_context() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let src = mk_ctx();
        let tgt = mk_ctx();
        let g = lia_goal(src);
        let g2 = Z3_goal_translate(src, g, tgt);
        assert!(!g2.is_null());
        assert_eq!(Z3_goal_size(tgt, g2), 3);
        // Probes evaluate correctly over the re-interned goal in the new context.
        assert_eq!(probe(tgt, c"num-consts", g2), 3.0);
        assert_eq!(probe(tgt, c"is-qflia", g2), 1.0);
        let s = CStr::from_ptr(Z3_goal_to_string(tgt, g2))
            .to_str()
            .expect("translated goal rendering must be valid UTF-8");
        assert_eq!(s, "(goal\n  (< 0 x)\n  (< y 10)\n  (< z (+ x y)))");
        Z3_del_context(src);
        Z3_del_context(tgt);
    }
}

#[test]
fn test_qfbv_and_nonlinear_fragments() {
    // SAFETY: all handles allocated/freed within this block; single-threaded.
    unsafe {
        let ctx = mk_ctx();
        // QF_BV: (= (bvadd bx by) 3)
        let bv8 = Z3_mk_bv_sort(ctx, 8);
        let bx = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"bx".as_ptr()), bv8);
        let by = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"by".as_ptr()), bv8);
        let three = Z3_mk_unsigned_int(ctx, 3, bv8);
        let gbv = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(ctx, gbv, Z3_mk_eq(ctx, Z3_mk_bvadd(ctx, bx, by), three));
        assert_eq!(probe(ctx, c"is-qfbv", gbv), 1.0);
        assert_eq!(probe(ctx, c"is-qflia", gbv), 0.0);
        assert_eq!(probe(ctx, c"num-bv-consts", gbv), 2.0);

        // QF_NIA: (< 0 (* x y))
        let i = Z3_mk_int_sort(ctx);
        let x = int_var(ctx, c"x");
        let y = int_var(ctx, c"y");
        let mul_args = [x, y];
        let gnl = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_assert(
            ctx,
            gnl,
            Z3_mk_lt(
                ctx,
                Z3_mk_int(ctx, 0, i),
                Z3_mk_mul(ctx, 2, mul_args.as_ptr()),
            ),
        );
        assert_eq!(probe(ctx, c"is-qfnia", gnl), 1.0);
        assert_eq!(probe(ctx, c"is-nia", gnl), 1.0);
        assert_eq!(probe(ctx, c"is-qflia", gnl), 0.0);

        Z3_del_context(ctx);
    }
}
