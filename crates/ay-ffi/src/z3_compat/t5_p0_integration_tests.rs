// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the cross-file fixes of the T5 P0 integration
//! (`~/ay-bench/campaign/2026-10-02-T5-DESIGN.md` §4 P0.2, Q1 and Q5): the
//! bound name of a privately spelled de Bruijn binder, the de Bruijn body of
//! nested and open quantifiers, and the app decl of a recursive function.
//!
//! Each test pins libz3 5.1.0's measured answer: `int_pins.py` and
//! `int_pins.real.out` in `~/ay-bench/t5-int/probes/` (z3-solver 5.1.0.0),
//! and `t5x/body_pins.py` in `~/ay-bench/campaign/t5design-probes/`.

use std::ffi::{c_int, CStr};
use std::ptr;

use crate::z3_compat::*;

unsafe fn fresh_ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn sym(c: Z3_context, name: &CStr) -> Z3_symbol {
    // SAFETY: `c` is live and `name` NUL-terminated.
    unsafe { Z3_mk_string_symbol(c, name.as_ptr()) }
}

/// `Z3_mk_quantifier` over one de Bruijn declaration.
unsafe fn db_quantifier(
    c: Z3_context,
    is_forall: bool,
    sort: Z3_sort,
    name: &CStr,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: the one-element arrays outlive the call.
    unsafe {
        let symbol = sym(c, name);
        Z3_mk_quantifier(
            c,
            is_forall,
            0,
            0,
            ptr::null(),
            1,
            &raw const sort,
            &raw const symbol,
            body,
        )
    }
}

/// The verdict of a fresh solver over `assertion`.
unsafe fn check(c: Z3_context, assertion: Z3_ast) -> c_int {
    // SAFETY: `assertion` is a live Bool AST of `c`.
    unsafe {
        let s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, assertion);
        let r = Z3_solver_check(c, s);
        Z3_solver_dec_ref(c, s);
        r
    }
}

unsafe fn bound_name(c: Z3_context, q: Z3_ast) -> String {
    // SAFETY: `q` is a live quantifier of `c`; the string is context-owned.
    unsafe {
        let name = Z3_get_quantifier_bound_name(c, q, 0);
        assert!(!name.is_null());
        CStr::from_ptr(Z3_get_symbol_string(c, name))
            .to_string_lossy()
            .into_owned()
    }
}

/// A de Bruijn binder that cannot take the caller's spelling (it names one of
/// the caller's constants, or a constant of another sort) is minted under a
/// private spelling; its bound name is still the caller's. z3: `w` and `wb`
/// (`int_pins.py` 1 and 2), with `forall w. (:var 0) > w` unsat.
#[test]
fn privately_spelled_de_bruijn_binder_shows_the_caller_name() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = fresh_ctx();
        let int_sort = Z3_mk_int_sort(c);
        let w = Z3_mk_const(c, sym(c, c"w"), int_sort);
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let q = db_quantifier(c, true, int_sort, c"w", Z3_mk_gt(c, v0, w));
        assert_ne!(q, 0);
        assert_eq!(bound_name(c, q), "w");
        assert_eq!(check(c, q), Z3_L_FALSE, "z3: unsat");

        let _wb = Z3_mk_const(c, sym(c, c"wb"), Z3_mk_bool_sort(c));
        let positive = Z3_mk_gt(c, v0, Z3_mk_int(c, 0, int_sort));
        let qb = db_quantifier(c, true, int_sort, c"wb", positive);
        assert_ne!(qb, 0);
        assert_eq!(bound_name(c, qb), "wb");
        Z3_del_context(c);
    }
}

/// `Z3_get_quantifier_body` of a nested quantifier built from constants:
/// `ForAll x. Exists y. x < y`. z3 (`body_pins.py` 1, `int_pins.py` 3): the
/// body's body is `(< (:var 1) (:var 0))`, and `substitute_vars(body, 5)` is
/// `Exists y. 5 < y`, whose negation is unsat. The body used to name `x` as
/// `(:var 1)` relative to `y`'s binder, which `substitute_vars` (anchored at
/// the root) missed.
#[test]
fn nested_constant_quantifier_body_is_de_bruijn_at_its_root() {
    // SAFETY: every handle lives in `c`; arrays outlive each call.
    unsafe {
        let c = fresh_ctx();
        let int_sort = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, sym(c, c"x"), int_sort);
        let y = Z3_mk_const(c, sym(c, c"y"), int_sort);
        let ys = [y];
        let exists = Z3_mk_exists_const(c, 0, 1, ys.as_ptr(), 0, ptr::null(), Z3_mk_lt(c, x, y));
        let xs = [x];
        let q = Z3_mk_forall_const(c, 0, 1, xs.as_ptr(), 0, ptr::null(), exists);
        assert_ne!(q, 0);

        let body = Z3_get_quantifier_body(c, q);
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let v1 = Z3_mk_bound(c, 1, int_sort);
        assert!(Z3_is_eq_ast(
            c,
            Z3_get_quantifier_body(c, body),
            Z3_mk_lt(c, v1, v0)
        ));
        let five = [Z3_mk_int(c, 5, int_sort)];
        let instance = Z3_substitute_vars(c, body, 1, five.as_ptr());
        assert_ne!(instance, 0);
        assert_eq!(check(c, Z3_mk_not(c, instance)), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// An open inner de Bruijn quantifier `Exists y. (:var 1) < (:var 0)` and the
/// closed `ForAll x.` over it. z3 (`body_pins.py` 2 and 3, `int_pins.py` 4):
/// the inner body is `(< (:var 1) (:var 0))` (it was captured as
/// `(< (:var 0) (:var 0))`), the outer quantifier is sat, and
/// `substitute_vars` of the inner quantifier and of the outer body by 5 both
/// have unsat negations.
#[test]
fn open_de_bruijn_quantifier_body_shifts_its_loose_variable() {
    // SAFETY: every handle lives in `c`; arrays outlive each call.
    unsafe {
        let c = fresh_ctx();
        let int_sort = Z3_mk_int_sort(c);
        let v0 = Z3_mk_bound(c, 0, int_sort);
        let v1 = Z3_mk_bound(c, 1, int_sort);
        let open = Z3_mk_lt(c, v1, v0);
        let inner = db_quantifier(c, false, int_sort, c"y", open);
        assert_ne!(inner, 0);
        assert!(Z3_is_eq_ast(c, Z3_get_quantifier_body(c, inner), open));
        let five = [Z3_mk_int(c, 5, int_sort)];
        let instance = Z3_substitute_vars(c, inner, 1, five.as_ptr());
        assert_eq!(check(c, Z3_mk_not(c, instance)), Z3_L_FALSE, "z3: unsat");

        let outer = db_quantifier(c, true, int_sort, c"x", inner);
        assert_ne!(outer, 0);
        assert_eq!(check(c, outer), Z3_L_TRUE, "z3: sat");
        let body = Z3_get_quantifier_body(c, outer);
        assert!(Z3_is_eq_ast(c, Z3_get_quantifier_body(c, body), open));
        let instance = Z3_substitute_vars(c, body, 1, five.as_ptr());
        assert_eq!(check(c, Z3_mk_not(c, instance)), Z3_L_FALSE, "z3: unsat");
        Z3_del_context(c);
    }
}

/// The app decl of a recursive function's application is the recursive decl
/// itself. z3 (`int_pins.py` 5): `fact(3).decl().eq(fact)` is True and the
/// decl applies to `4`. With Q5's own identity for recursive functions the
/// lookup missed it: the decl was not eq and applying it was INVALID_ARG.
#[test]
fn recursive_function_application_has_its_recursive_decl() {
    // SAFETY: every handle lives in `c`; arrays outlive each call.
    unsafe {
        let c = fresh_ctx();
        let int_sort = Z3_mk_int_sort(c);
        let domain = [int_sort];
        let fact = Z3_mk_rec_func_decl(c, sym(c, c"fact"), 1, domain.as_ptr(), int_sort);
        assert!(!fact.is_null());
        let n = Z3_mk_const(c, sym(c, c"n"), int_sort);
        let one = Z3_mk_int(c, 1, int_sort);
        let n_minus_one = Z3_mk_sub(c, 2, [n, one].as_ptr());
        let recursive = Z3_mk_app(c, fact, 1, [n_minus_one].as_ptr());
        let product = Z3_mk_mul(c, 2, [n, recursive].as_ptr());
        let base = Z3_mk_le(c, n, Z3_mk_int(c, 0, int_sort));
        let definition = Z3_mk_ite(c, base, one, product);
        Z3_add_rec_def(c, fact, 1, [n].as_ptr(), definition);
        assert_eq!(Z3_get_error_code(c), Z3_OK);

        let three = Z3_mk_app(c, fact, 1, [Z3_mk_int(c, 3, int_sort)].as_ptr());
        let decl = Z3_get_app_decl(c, three);
        assert!(!decl.is_null());
        assert!(Z3_is_eq_func_decl(c, decl, fact), "z3: decl().eq(fact)");
        let four = Z3_mk_app(c, decl, 1, [Z3_mk_int(c, 4, int_sort)].as_ptr());
        assert_ne!(four, 0);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}
