// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the T1 verification findings (`~/ay-bench/api-t1v`):
//! structural `Z3_substitute` / `Z3_update_term` on rewritten terms, the
//! `encoding` parameter, recognizer declarations, the Optimize core and
//! unbounded objectives, numeral text, string accessors and the identity of
//! parsed declarations. Each pins z3 5.1.0's answer or a fail-closed error.

use std::ffi::{c_char, c_uint, CStr};
use std::ptr;

use crate::z3_compat::*;

/// Fresh context; caller frees via `Z3_del_context`.
unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn konst(c: Z3_context, name: &CStr, sort: Z3_sort) -> Z3_ast {
    // SAFETY: `c` is live and `name` NUL-terminated.
    unsafe { Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), sort) }
}

unsafe fn text(p: *const c_char) -> String {
    // SAFETY: `p` is a context-owned NUL-terminated string.
    unsafe { CStr::from_ptr(p).to_string_lossy().into_owned() }
}

unsafe fn decl_name(c: Z3_context, d: Z3_func_decl) -> String {
    // SAFETY: `d` is a live decl of `c`.
    unsafe { text(Z3_get_symbol_string(c, Z3_get_decl_name(c, d))) }
}

/// `Z3_substitute(t, from -> to)` and the error code it left.
unsafe fn subst(c: Z3_context, t: Z3_ast, from: &[Z3_ast], to: &[Z3_ast]) -> (Z3_ast, c_uint) {
    // SAFETY: `from`/`to` hold `from.len()` live ASTs of `c`.
    unsafe {
        let r = Z3_substitute(c, t, from.len() as c_uint, from.as_ptr(), to.as_ptr());
        (r, Z3_get_error_code(c))
    }
}

/// The verifier's rows R1-R10 (`subst_repro.py`): z3 substitutes in the term
/// as built, where none of these patterns occurs, so its answer is the input
/// unchanged. AY must give that answer or refuse: never a rewritten-away or
/// rewritten-into match.
#[test]
fn substitute_matches_z3_or_refuses_on_rewritten_terms() {
    // SAFETY: every handle lives in one context; arrays outlive each call.
    unsafe {
        let c = ctx();
        let (int, boolean) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let [a, b, x, y] = [c"a", c"b", c"x", c"y"].map(|n| konst(c, n, int));
        let [p, q, r] = [c"p", c"q", c"r"].map(|n| konst(c, n, boolean));
        let (zero, one, two) = (
            Z3_mk_int(c, 0, int),
            Z3_mk_int(c, 1, int),
            Z3_mk_int(c, 2, int),
        );
        let add = |l: Z3_ast, r: Z3_ast| Z3_mk_add(c, 2, [l, r].as_ptr());
        let and = |l: Z3_ast, r: Z3_ast| Z3_mk_and(c, 2, [l, r].as_ptr());
        let unchanged_or_refused = |row: &str, t: Z3_ast, from: Z3_ast, to: Z3_ast| {
            let got = subst(c, t, &[from], &[to]);
            assert!(
                got == (t, Z3_OK) || got == (0, Z3_INVALID_ARG),
                "{row}: z3 leaves the input unchanged, AY returned {got:?}"
            );
        };
        let not_q = Z3_mk_not(c, q);

        // R1: Not(Not(p)) is stored as p.
        let nnp = Z3_mk_not(c, Z3_mk_not(c, p));
        unchanged_or_refused("R1", and(p, not_q), nnp, q);
        // R2: a + 0 is stored as a.
        unchanged_or_refused("R2", add(a, b), add(a, zero), y);
        // R3: 1 + 1 is stored as the numeral 2.
        unchanged_or_refused("R3", add(x, two), add(one, one), y);
        // R6: And(p, True) is stored as p.
        unchanged_or_refused(
            "R6",
            Z3_mk_or(c, 2, [p, q].as_ptr()),
            and(p, Z3_mk_true(c)),
            r,
        );
        // R7: (b + 1) + 1 is stored as b + 2, which is absent from z3's term.
        let b11 = Z3_mk_eq(c, add(add(b, one), one), Z3_mk_int(c, 5, int));
        unchanged_or_refused("R7", b11, add(b, two), x);
        // R8: Implies(p, q) is stored as Or(Not p, q).
        let or_not = Z3_mk_or(c, 2, [Z3_mk_not(c, p), q].as_ptr());
        unchanged_or_refused("R8", and(Z3_mk_implies(c, p, q), r), or_not, r);
        // R9: x > y may be stored as y < x.
        unchanged_or_refused("R9", and(Z3_mk_gt(c, x, y), r), Z3_mk_lt(c, y, x), q);
        // R10: Distinct(a, b) may be stored as Not(a = b).
        let ne = Z3_mk_not(c, Z3_mk_eq(c, a, b));
        unchanged_or_refused("R10", and(Z3_mk_distinct(c, 2, [a, b].as_ptr()), r), ne, q);
        // Fuzz minimum: Not(False) folds to True.
        unchanged_or_refused(
            "Not(False)",
            Z3_mk_not(c, Z3_mk_false(c)),
            Z3_mk_false(c),
            q,
        );

        // Both faithful occurrences must be replaced. A representation that
        // has rewritten either occurrence may still conservatively refuse.
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        let a1 = add(a, one);
        let r4 = add(Z3_mk_app(c, f, 1, [a1].as_ptr()), add(a1, one));
        let (got, error) = subst(c, r4, &[a1], &[b]);
        if got == 0 {
            assert_eq!(error, Z3_INVALID_ARG);
        } else {
            assert_eq!(error, Z3_OK);
            let expected = add(Z3_mk_app(c, f, 1, [b].as_ptr()), add(b, one));
            let solver = Z3_mk_solver(c);
            Z3_solver_assert(c, solver, Z3_mk_not(c, Z3_mk_eq(c, got, expected)));
            assert_eq!(
                Z3_solver_check(c, solver),
                Z3_L_FALSE,
                "both occurrences must be replaced"
            );
        }
        // After R1, the handle p may stand for Not(Not(p)): as a pattern it
        // is refused, or replaced exactly as z3 replaces the constant p.
        let got = subst(c, and(p, not_q), &[p], &[q]);
        assert!(
            got == (0, Z3_INVALID_ARG) || got == (and(q, not_q), Z3_OK),
            "{got:?}"
        );
        Z3_del_context(c);
    }
}

/// What still substitutes: clean constants anywhere (also in rewritten
/// terms, since replacing a free constant commutes with every rewrite), and
/// compound patterns in terms stored exactly as built.
#[test]
fn substitute_keeps_constant_and_faithful_compound_patterns() {
    // SAFETY: every handle lives in one context; arrays outlive each call.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let [a, b, x, y] = [c"a", c"b", c"x", c"y"].map(|n| konst(c, n, int));
        let one = Z3_mk_int(c, 1, int);
        // (x + 1) + 1 is stored as x + 2; replacing x is still exact.
        let x11 = Z3_mk_add(c, 2, [Z3_mk_add(c, 2, [x, one].as_ptr()), one].as_ptr());
        let (got, err) = subst(c, x11, &[x], &[y]);
        assert_eq!(err, Z3_OK);
        let y2 = Z3_mk_add(c, 2, [y, Z3_mk_int(c, 2, int)].as_ptr());
        assert_eq!(got, y2);

        // g(f(a), b) built faithfully: replace f(a).
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        let g = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"g".as_ptr()),
            2,
            [int, int].as_ptr(),
            int,
        );
        let fa = Z3_mk_app(c, f, 1, [a].as_ptr());
        let gfab = Z3_mk_app(c, g, 2, [fa, b].as_ptr());
        let (got, err) = subst(c, gfab, &[fa], &[x]);
        assert_eq!(err, Z3_OK);
        assert_eq!(got, Z3_mk_app(c, g, 2, [x, b].as_ptr()));
        Z3_del_context(c);
    }
}

/// Rows U1-U5: `Z3_update_term` keeps z3's operator only on a term stored as
/// built; Implies (stored as Or), x > y (stored swapped), a - b and
/// g(..) + 0 (folded) are refused. A faithful application still updates.
#[test]
fn update_term_refuses_rewritten_operators() {
    // SAFETY: every handle lives in one context; arrays outlive each call.
    unsafe {
        let c = ctx();
        let (int, boolean) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let [a, b, x, y] = [c"a", c"b", c"x", c"y"].map(|n| konst(c, n, int));
        let [p, q, r, s] = [c"p", c"q", c"r", c"s"].map(|n| konst(c, n, boolean));
        let upd = |t: Z3_ast, kids: &[Z3_ast]| {
            let got = Z3_update_term(c, t, kids.len() as c_uint, kids.as_ptr());
            (got, Z3_get_error_code(c))
        };
        let refused = |t: Z3_ast, kids: &[Z3_ast]| {
            let (got, err) = upd(t, kids);
            assert_eq!((got, err), (0, Z3_INVALID_ARG));
        };
        let imp = Z3_mk_implies(c, p, q);
        if Z3_get_app_num_args(c, imp) == 2
            && Z3_get_decl_kind(c, Z3_get_app_decl(c, imp)) != Z3_OP_IMPLIES
        {
            refused(imp, &[r, s]);
        }
        let sub = Z3_mk_sub(c, 2, [a, b].as_ptr());
        if Z3_get_decl_kind(c, Z3_get_app_decl(c, sub)) != Z3_OP_SUB {
            refused(sub, &[x, y]);
        }
        let g = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"g".as_ptr()),
            2,
            [int, int].as_ptr(),
            int,
        );
        let gplus0 = Z3_mk_add(
            c,
            2,
            [Z3_mk_app(c, g, 2, [a, b].as_ptr()), Z3_mk_int(c, 0, int)].as_ptr(),
        );
        if Z3_get_decl_kind(c, Z3_get_app_decl(c, gplus0)) == Z3_OP_ADD
            && Z3_get_app_num_args(c, gplus0) == 2
        {
            assert_eq!(
                upd(gplus0, &[x, y]),
                (Z3_mk_add(c, 2, [x, y].as_ptr()), Z3_OK)
            );
        } else {
            refused(gplus0, &[x, y]);
        }
        // x > y and x >= y: refused unless AY stored them as built (then the
        // operator is z3's and the update is exact).
        for build in [Z3_mk_gt as unsafe extern "C" fn(_, _, _) -> _, Z3_mk_ge] {
            let t = build(c, x, y);
            let args_kept = Z3_get_app_num_args(c, t) == 2
                && Z3_get_app_arg(c, t, 0) == x
                && Z3_get_app_arg(c, t, 1) == y;
            let (got, err) = upd(t, &[a, b]);
            if args_kept {
                assert_eq!((got, err), (build(c, a, b), Z3_OK));
            } else {
                assert_eq!((got, err), (0, Z3_INVALID_ARG));
            }
        }
        // Fuzz case 68: -(-(f(a))) is stored as f(a); updating it with [a]
        // is -(a) on z3, so AY must not return f(a) unchanged.
        let f1 = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f1".as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        let neg_neg = Z3_mk_unary_minus(c, Z3_mk_unary_minus(c, Z3_mk_app(c, f1, 1, [a].as_ptr())));
        let (got, err) = upd(neg_neg, &[a]);
        assert!(
            (got, err) == (0, Z3_INVALID_ARG) || (got, err) == (Z3_mk_unary_minus(c, a), Z3_OK),
            "{got:?} {err}"
        );
        // The z3py doctest: f(a, b).update(c, c) == f(c, c).
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"f".as_ptr()),
            2,
            [int, int].as_ptr(),
            int,
        );
        let fab = Z3_mk_app(c, f, 2, [a, b].as_ptr());
        assert_eq!(
            upd(fab, &[x, x]),
            (Z3_mk_app(c, f, 2, [x, x].as_ptr()), Z3_OK)
        );
        Z3_del_context(c);
    }
}

/// Under `encoding=ascii`/`bmp` z3's alphabet is smaller; AY implements only
/// unicode, so string terms are refused rather than decoded or solved with
/// unicode semantics (`enc_probe.py`). Exercised through the helper with the
/// encoding passed in: the global parameter is process-wide and would race
/// with the other tests.
#[test]
fn non_unicode_encoding_refuses_string_terms() {
    assert!(encoding_is_unicode(None));
    assert!(encoding_is_unicode(Some("unicode")));
    assert!(!encoding_is_unicode(Some("ascii")));
    assert!(!encoding_is_unicode(Some("bmp")));
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let s = Z3_mk_string(c, c"\\u{100}".as_ptr());
        let len = Z3_mk_seq_length(c, s);
        let n = Z3_mk_int(c, 256, Z3_mk_int_sort(c));
        let from_code = Z3_mk_string_from_code(c, n);
        let context = &mut *c;
        for ast in [s, len, from_code] {
            assert!(zstring::refuse_for_encoding(context, ast, false));
            assert_eq!(context.last_error, Z3_INVALID_ARG);
            context.last_error = Z3_OK;
            assert!(!zstring::refuse_for_encoding(context, ast, true));
        }
        assert!(!zstring::refuse_for_encoding(context, n, false));
        Z3_del_context(c);
    }
}

/// `rec_print.py`: z3's recognizer is named `is` and carries its constructor
/// as its one `Z3_PARAMETER_FUNC_DECL` parameter; z3py's printer reads
/// `params()[0]` (an IndexError on the previous build).
#[test]
fn recognizer_decl_carries_its_constructor() {
    // SAFETY: every handle lives in one context; the output arrays hold `n`.
    unsafe {
        let c = ctx();
        let names = [c"red", c"green"].map(|n| Z3_mk_string_symbol(c, n.as_ptr()));
        let mut consts = [ptr::null_mut(); 2];
        let mut testers = [ptr::null_mut(); 2];
        let sort = Z3_mk_enumeration_sort(
            c,
            Z3_mk_string_symbol(c, c"Color".as_ptr()),
            2,
            names.as_ptr(),
            consts.as_mut_ptr(),
            testers.as_mut_ptr(),
        );
        let col = konst(c, c"col", sort);
        let is_red = Z3_mk_app(c, testers[0], 1, [col].as_ptr());
        for decl in [testers[0], Z3_get_app_decl(c, is_red)] {
            assert_eq!(decl_name(c, decl), "is");
            assert_eq!(Z3_get_decl_kind(c, decl), Z3_OP_DT_IS);
            assert_eq!(Z3_get_decl_num_parameters(c, decl), 1);
            assert_eq!(
                Z3_get_decl_parameter_kind(c, decl, 0),
                Z3_PARAMETER_FUNC_DECL
            );
            let ctor = Z3_get_decl_func_decl_parameter(c, decl, 0);
            assert_eq!(Z3_get_error_code(c), Z3_OK);
            assert!(!ctor.is_null());
            assert_eq!(decl_name(c, ctor), "red");
            assert_eq!(Z3_get_decl_kind(c, ctor), Z3_OP_DT_CONSTRUCTOR);
            assert!(Z3_get_decl_func_decl_parameter(c, decl, 1).is_null());
            assert_eq!(Z3_get_error_code(c), Z3_IOB);
        }
        // A constructor has no parameter.
        assert_eq!(Z3_get_decl_num_parameters(c, consts[0]), 0);
        Z3_del_context(c);
    }
}

/// T11: a literal tracking two constraints is one core entry, as in z3.
#[test]
fn optimize_core_lists_each_tracking_literal_once() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = konst(c, c"x", int);
        let p = konst(c, c"p", Z3_mk_bool_sort(c));
        let o = Z3_mk_optimize(c);
        Z3_optimize_inc_ref(c, o);
        Z3_optimize_assert_and_track(c, o, Z3_mk_gt(c, x, Z3_mk_int(c, 5, int)), p);
        Z3_optimize_assert_and_track(c, o, Z3_mk_lt(c, x, Z3_mk_int(c, 3, int)), p);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        let core = Z3_optimize_get_unsat_core(c, o);
        assert_eq!(Z3_ast_vector_size(c, core), 1);
        assert_eq!(Z3_ast_vector_get(c, core, 0), p);
        Z3_optimize_dec_ref(c, o);
        Z3_del_context(c);
    }
}

/// `opt_panic.py`: an unbounded minimize of an `ite` after a push and a new
/// constraint panicked in the LRA optimizer (`NeedLemmas` was unreachable);
/// the unbounded value was a NULL AST with no error.
#[test]
fn optimize_unbounded_ite_objective_neither_panics_nor_returns_silent_null() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let (int, boolean) = (Z3_mk_int_sort(c), Z3_mk_bool_sort(c));
        let [b1, b3] = [c"b1", c"b3"].map(|n| konst(c, n, boolean));
        let [x0, x1, x2] = [c"x0", c"x1", c"x2"].map(|n| konst(c, n, int));
        let o = Z3_mk_optimize(c);
        Z3_optimize_inc_ref(c, o);
        let h = Z3_optimize_minimize(c, o, Z3_mk_ite(c, b1, x0, x1));
        let check_and_read = |o: Z3_optimize| {
            let verdict = Z3_optimize_check(c, o, 0, ptr::null());
            let check_error = Z3_get_error_code(c);
            assert_ne!(check_error, Z3_EXCEPTION, "check raised: panic surfaced");
            // Either a value, or an error: never a silent null.
            let value = Z3_optimize_get_upper(c, o, h);
            let err = Z3_get_error_code(c);
            assert!(
                value != 0 || err != Z3_OK,
                "silent null objective value ({verdict})"
            );
            if verdict != Z3_L_TRUE {
                assert_eq!((value, err), (0, Z3_INVALID_USAGE));
            }
        };
        check_and_read(o);
        Z3_optimize_push(c, o);
        let m2 = Z3_mk_int(c, -2, int);
        let ite = Z3_mk_ite(c, b3, x2, m2);
        let lhs = Z3_mk_mul(c, 2, [m2, ite].as_ptr());
        Z3_optimize_assert(c, o, Z3_mk_not(c, Z3_mk_eq(c, lhs, x2)));
        check_and_read(o);
        Z3_optimize_dec_ref(c, o);
        Z3_del_context(c);
    }
}
