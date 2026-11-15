// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T5 P0.2 quarantine, implementer Y: Q2 (loose bound variables), Q5
//! (recursive vs uninterpreted identity) and Q6 (sort vs datatype names);
//! Q7, Q10 and Q11 are in `t5_p0_y_handle_tests`, Q8, Q9 and Q12 in
//! `t5_p0_y_obligation_tests`.
//!
//! Every pin cites its libz3 5.1.0 measurement: z3py 5.1.0 over the real
//! library, one case of the T5 P0 implementer-Y pin script `ypins.py`
//! (`~/ay-bench/t5y-bench`), each case in its own process.

use std::ffi::{c_uint, CStr};
use std::ptr;

use crate::z3_compat::*;

/// Fresh context; caller frees via `Z3_del_context`.
pub(super) unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

pub(super) unsafe fn sym(c: Z3_context, name: &CStr) -> Z3_symbol {
    // SAFETY: `c` is live and `name` NUL-terminated.
    unsafe { Z3_mk_string_symbol(c, name.as_ptr()) }
}

pub(super) unsafe fn int_const(c: Z3_context, name: &CStr) -> Z3_ast {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe { Z3_mk_const(c, sym(c, name), Z3_mk_int_sort(c)) }
}

pub(super) unsafe fn int(c: Z3_context, v: i32) -> Z3_ast {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe { Z3_mk_int(c, v, Z3_mk_int_sort(c)) }
}

pub(super) unsafe fn text(s: *const c_char) -> String {
    assert!(!s.is_null(), "expected a string");
    // SAFETY: a non-null string returned by the API is NUL-terminated and
    // context-owned for the duration of this read.
    unsafe { CStr::from_ptr(s).to_string_lossy().into_owned() }
}

/// `Var(0, Int) > 1`.
unsafe fn loose_gt(c: Z3_context) -> Z3_ast {
    // SAFETY: the caller passes a live context `c` owned by this test.
    unsafe { Z3_mk_gt(c, Z3_mk_bound(c, 0, Z3_mk_int_sort(c)), int(c, 1)) }
}

/// libz3 5.1.0 (ypins.py q2_loose_assert): `Z3_solver_check` over `Var(0) > 1` returns
/// `Z3_L_UNDEF`, error `Z3_OK`, reason "Formulas should not contain unbound
/// variables"; after `reset` the solver works normally.
#[test]
fn q2_loose_bound_variable_assertion_is_unknown_with_z3_reason() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, loose_gt(c));
        assert_eq!(Z3_solver_check(c, s), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(
            text(Z3_solver_get_reason_unknown(c, s)),
            "Formulas should not contain unbound variables"
        );
        Z3_solver_reset(c, s);
        Z3_solver_assert(c, s, Z3_mk_gt(c, int_const(c, c"x"), int(c, 1)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q2_loose_assumption, q2_loose_optimize): an assumption with a loose variable returns
/// `Z3_L_UNDEF` with error `Z3_EXCEPTION` (12), same text; an Optimize
/// constraint with one does too.
#[test]
fn q2_loose_bound_variable_assumption_and_optimize_are_errors() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, int_const(c, c"x"), int(c, 1)));
        let assumption = [loose_gt(c)];
        assert_eq!(
            Z3_solver_check_assumptions(c, s, 1, assumption.as_ptr()),
            Z3_L_UNDEF
        );
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert_eq!(
            text(Z3_get_error_msg(c, Z3_EXCEPTION)),
            "Formulas should not contain unbound variables"
        );
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_TRUE,
            "the solver itself is fine"
        );

        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, loose_gt(c));
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        Z3_del_context(c);
    }
}

/// A variable bound by a quantifier built from constants is not loose: the
/// goal still reaches the engine (libz3 5.1.0: `forall x. x > 0` is unsat).
#[test]
fn q2_bound_variable_under_its_binder_is_decided() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let x = int_const(c, c"qx");
        let body = Z3_mk_gt(c, x, int(c, 0));
        let bound = [x];
        let q = Z3_mk_forall_const(c, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, q);
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

pub(super) unsafe fn int_decl(c: Z3_context, name: &CStr, recursive: bool) -> Z3_func_decl {
    // SAFETY: `c` is live; the domain array lives across the call.
    unsafe {
        let domain = [Z3_mk_int_sort(c)];
        let range = Z3_mk_int_sort(c);
        if recursive {
            Z3_mk_rec_func_decl(c, sym(c, name), 1, domain.as_ptr(), range)
        } else {
            Z3_mk_func_decl(c, sym(c, name), 1, domain.as_ptr(), range)
        }
    }
}

pub(super) unsafe fn app1(c: Z3_context, f: Z3_func_decl, a: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is live; the argument array lives across the call.
    unsafe { Z3_mk_app(c, f, 1, [a].as_ptr()) }
}

/// libz3 5.1.0 (ypins.py q5_rec_then_uf, q5_uf_then_rec): a recursive `f` and
/// an uninterpreted `f`, both `Int -> Int`, are two functions:
/// `RecFunction('f').eq(Function('f'))` is False and `g(3) == 7, f(3) == 3`
/// (`f(n) = if n <= 0 then 0 else f(n-1) + 1`) is sat. AY merged them and
/// answered unsat.
#[test]
fn q5_recursive_and_uninterpreted_functions_are_distinct() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let f = int_decl(c, c"f", true);
        let g = int_decl(c, c"f", false);
        assert!(!Z3_is_eq_func_decl(c, f, g));
        let n = int_const(c, c"n");
        let le = Z3_mk_le(c, n, int(c, 0));
        let pred = Z3_mk_sub(c, 2, [n, int(c, 1)].as_ptr());
        let step = Z3_mk_add(c, 2, [app1(c, f, pred), int(c, 1)].as_ptr());
        Z3_add_rec_def(c, f, 1, [n].as_ptr(), Z3_mk_ite(c, le, int(c, 0), step));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, app1(c, g, int(c, 3)), int(c, 7)));
        Z3_solver_assert(c, s, Z3_mk_eq(c, app1(c, f, int(c, 3)), int(c, 3)));
        assert_ne!(Z3_solver_check(c, s), Z3_L_FALSE, "z3: sat; never unsat");
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q5_rec_twice, q5_add_rec_def_on_uf): a second `Z3_mk_rec_func_decl` of
/// one name and signature returns null with `Z3_EXCEPTION` ("recursive
/// function f already defined"); another signature is allowed;
/// `Z3_add_rec_def` on a `Z3_mk_func_decl` declaration is `Z3_INVALID_ARG`
/// ("... needs to be declared using rec_func_decl").
#[test]
fn q5_recursive_declaration_identity_errors() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        assert!(!int_decl(c, c"r2", true).is_null());
        assert!(int_decl(c, c"r2", true).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        assert!(text(Z3_get_error_msg(c, Z3_EXCEPTION)).contains("already defined"));
        let real_domain = [Z3_mk_real_sort(c)];
        let other =
            Z3_mk_rec_func_decl(c, sym(c, c"r2"), 1, real_domain.as_ptr(), Z3_mk_int_sort(c));
        assert!(!other.is_null(), "another signature is another function");

        let g = int_decl(c, c"u1", false);
        let n = int_const(c, c"n");
        Z3_add_rec_def(
            c,
            g,
            1,
            [n].as_ptr(),
            Z3_mk_add(c, 2, [n, int(c, 1)].as_ptr()),
        );
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert!(text(Z3_get_error_msg(c, Z3_INVALID_ARG)).contains("rec_func_decl"));
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, app1(c, g, int(c, 0)), int(c, 5)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE, "g stays uninterpreted");
        Z3_del_context(c);
    }
}

unsafe fn enum_sort(c: Z3_context, name: &CStr) -> Z3_sort {
    // SAFETY: `c` is live; the arrays live across the call.
    unsafe {
        let names = [sym(c, c"red"), sym(c, c"green")];
        let mut consts = [ptr::null_mut(); 2];
        let mut testers = [ptr::null_mut(); 2];
        Z3_mk_enumeration_sort(
            c,
            sym(c, name),
            2,
            names.as_ptr(),
            consts.as_mut_ptr(),
            testers.as_mut_ptr(),
        )
    }
}

/// libz3 5.1.0 (ypins.py q6_api_usort_then_enum, q6_api_enum_then_usort): an uninterpreted sort and an enumeration of
/// one name are two sorts (`Distinct(a, b, c)` over the former is sat). AY
/// lowers both to one engine sort and answered unsat; it now refuses the
/// second declaration in either order (error, never unsat).
#[test]
fn q6_uninterpreted_sort_and_datatype_of_one_name_are_refused() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let u = Z3_mk_uninterpreted_sort(c, sym(c, c"Color"));
        assert!(!u.is_null());
        assert!(enum_sort(c, c"Color").is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let again = Z3_mk_uninterpreted_sort(c, sym(c, c"Color"));
        assert!(
            Z3_is_eq_sort(c, u, again),
            "z3: DeclareSort twice is one sort"
        );

        assert!(!enum_sort(c, c"Color2").is_null());
        assert!(Z3_mk_uninterpreted_sort(c, sym(c, c"Color2")).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// The same collision through a parsed text, in both orders (libz3 5.1.0:
/// q6.text_usort_then_api_enum and q6.api_usort_then_text_dt are sat).
#[test]
fn q6_text_declarations_collide_too() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_from_string(c, s, c"(declare-sort T 0) (declare-const a T)".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert!(
            enum_sort(c, c"T").is_null(),
            "API datatype named like a text sort"
        );

        let _v = Z3_mk_uninterpreted_sort(c, sym(c, c"V"));
        let s2 = Z3_mk_solver(c);
        Z3_solver_from_string(c, s2, c"(declare-datatypes ((V 0)) (((v1) (v2))))".as_ptr());
        assert_ne!(
            Z3_get_error_code(c),
            Z3_OK,
            "text datatype named like an API sort"
        );

        assert!(!enum_sort(c, c"W").is_null());
        let s3 = Z3_mk_solver(c);
        Z3_solver_from_string(c, s3, c"(declare-sort W 0) (declare-const w W)".as_ptr());
        assert_ne!(
            Z3_get_error_code(c),
            Z3_OK,
            "text sort named like an API datatype"
        );
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q2_loose_nested): `Exists x. x > Var(1)` (the
/// variable escapes the one binder) is `unknown` with the same reason; AY
/// answered `sat` with `__db1 = -1`.
#[test]
fn q2_variable_escaping_its_binders_is_loose() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let x = int_const(c, c"ex");
        let body = Z3_mk_gt(c, x, Z3_mk_bound(c, 1, Z3_mk_int_sort(c)));
        let q = Z3_mk_exists_const(c, 0, 1, [x].as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, q);
        assert_eq!(Z3_solver_check(c, s), Z3_L_UNDEF);
        assert_eq!(
            text(Z3_solver_get_reason_unknown(c, s)),
            "Formulas should not contain unbound variables"
        );
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q2_loose_implied_equalities): implied equalities of
/// a solver asserting `Var(0) == x` raise `Z3_EXCEPTION` with the reason; AY
/// answered with classes.
#[test]
fn q2_loose_variable_in_implied_equalities_is_an_error() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let x = int_const(c, c"ix");
        let y = int_const(c, c"iy");
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, Z3_mk_bound(c, 0, Z3_mk_int_sort(c)), x));
        let terms = [x, y];
        let mut classes: [c_uint; 2] = [0; 2];
        let verdict = Z3_get_implied_equalities(c, s, 2, terms.as_ptr(), classes.as_mut_ptr());
        assert_eq!(verdict, Z3_L_UNDEF);
        assert_eq!(Z3_get_error_code(c), Z3_EXCEPTION);
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q6_text_then_text): a `declare-sort T2` in one text
/// and a `declare-datatypes ((T2 0))` in a later one are two sorts (the
/// first solver's `distinct a b c` stays sat); AY merged them and answered
/// unsat. The second text is now refused.
#[test]
fn q6_text_sort_then_text_datatype_is_refused() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_from_string(
            c,
            s,
            c"(declare-sort T2 0) (declare-const a T2) (declare-const b T2) (declare-const c T2) (assert (distinct a b c))".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let s2 = Z3_mk_solver(c);
        Z3_solver_from_string(
            c,
            s2,
            c"(declare-datatypes ((T2 0)) (((u1) (u2))))".as_ptr(),
        );
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        assert_ne!(Z3_solver_check(c, s), Z3_L_FALSE, "z3: sat");
        Z3_del_context(c);
    }
}

/// libz3 5.1.0 (ypins.py q5_text_recdef_vs_api): beside an API `f : Int ->
/// Int` (uninterpreted), a text `define-fun-rec f` parses and the two stay
/// apart (the API goal `f(0) == 5` is sat); beside an API recursive `r`, the
/// text is refused ("recursive function r already defined"). AY attached the
/// text's definition to the API's uninterpreted `f` and answered `unsat`; the
/// text is now refused in both cases, and the API goal stays sat. A text
/// defining a fresh name still parses.
#[test]
fn q5_text_recursive_definition_never_defines_an_api_function() {
    // SAFETY: all handles belong to `c`, freed at the end.
    unsafe {
        let c = ctx();
        let f = int_decl(c, c"f", false);
        let s = Z3_mk_solver(c);
        Z3_solver_from_string(
            c,
            s,
            c"(define-fun-rec f ((n Int)) Int (ite (<= n 0) 0 (f (- n 1)))) (assert (= (f 2) 0))"
                .as_ptr(),
        );
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_eq(c, app1(c, f, int(c, 0)), int(c, 5)));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE, "z3: sat");

        let _r = int_decl(c, c"r", true);
        let s_r = Z3_mk_solver(c);
        Z3_solver_from_string(
            c,
            s_r,
            c"(define-fun-rec r ((n Int)) Int (ite (<= n 0) 0 (r (- n 1))))".as_ptr(),
        );
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        assert!(text(Z3_get_error_msg(c, Z3_get_error_code(c))).contains("already defined"));

        let s3 = Z3_mk_solver(c);
        let fresh = c"(define-fun-rec h ((n Int)) Int (ite (<= n 0) 0 (+ 1 (h (- n 1))))) (assert (= (h 2) 2))";
        Z3_solver_from_string(c, s3, fresh.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_ne!(Z3_solver_check(c, s3), Z3_L_FALSE);
        // The same definition in a later text is the same function.
        let s4 = Z3_mk_solver(c);
        Z3_solver_from_string(c, s4, fresh.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}
