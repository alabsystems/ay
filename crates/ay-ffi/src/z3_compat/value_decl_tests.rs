// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value declarations, applying decls AY hands out, and the interim
//! `Z3_substitute` guard, each pinned to z3 5.1.0's answer (critic probes S9,
//! S10, S20, O4/O5 and the C04/C16 clusters of the z3py corpus).

use std::ffi::{c_uint, CStr};
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

unsafe fn decl_name(c: Z3_context, d: Z3_func_decl) -> String {
    // SAFETY: `d` is a live decl of `c`; the symbol text is context-owned.
    unsafe {
        let text = Z3_get_symbol_string(c, Z3_get_decl_name(c, d));
        CStr::from_ptr(text).to_string_lossy().into_owned()
    }
}

/// z3 5.1.0 (measured, triage-4/repro.out): `true` 256 `true`, `false` 257
/// `false`, `7` 512 `Int`, `1/3` 512 `Real`, `#x05` 1024 `bv`, `"ab"` 49165
/// `String`; `true`/`false`/`"ab"` are APP_AST, the numerals NUMERAL_AST.
#[test]
fn literals_report_z3_value_decls() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let seven = Z3_mk_int(c, 7, Z3_mk_int_sort(c));
        let bv5 = Z3_mk_numeral(c, c"5".as_ptr(), Z3_mk_bv_sort(c, 8));
        let ab = Z3_mk_string(c, c"ab".as_ptr());
        let cases = [
            (Z3_mk_true(c), Z3_OP_TRUE, "true", Z3_APP_AST),
            (Z3_mk_false(c), Z3_OP_FALSE, "false", Z3_APP_AST),
            (seven, Z3_OP_ANUM, "Int", Z3_NUMERAL_AST),
            (Z3_mk_real(c, 1, 3), Z3_OP_ANUM, "Real", Z3_NUMERAL_AST),
            (bv5, Z3_OP_BNUM, "bv", Z3_NUMERAL_AST),
            (ab, Z3_OP_INTERNAL, "String", Z3_APP_AST),
        ];
        for (value, kind, name, ast_kind) in cases {
            let d = Z3_get_app_decl(c, value);
            assert!(!d.is_null(), "{name}");
            assert_eq!(Z3_get_error_code(c), Z3_OK, "{name}");
            assert_eq!(Z3_get_decl_kind(c, d), kind, "{name}");
            assert_eq!(decl_name(c, d), name);
            assert_eq!(Z3_get_ast_kind(c, value), ast_kind, "{name}");
            let numeral = ast_kind == Z3_NUMERAL_AST;
            assert_eq!(Z3_is_numeral_ast(c, value), numeral, "{name}");
            // Applying the decl to no arguments rebuilds the literal.
            assert_eq!(Z3_mk_app(c, d, 0, ptr::null()), value, "{name}");
        }
        Z3_del_context(c);
    }
}

#[test]
fn value_decl_identity_is_the_literal() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let seven = Z3_get_app_decl(c, Z3_mk_int(c, 7, int));
        let eight = Z3_get_app_decl(c, Z3_mk_int(c, 8, int));
        let seven_again = Z3_get_app_decl(c, Z3_mk_int(c, 7, int));
        assert!(!Z3_is_eq_func_decl(c, seven, eight));
        assert!(Z3_is_eq_func_decl(c, seven, seven_again));
        assert_ne!(Z3_func_decl_to_ast(c, seven), Z3_func_decl_to_ast(c, eight));

        // A user constant NAMED like a value decl stays uninterpreted.
        for name in [c"Int", c"true", c"bv", c"String"] {
            let user = Z3_get_app_decl(c, konst(c, name, int));
            assert_eq!(Z3_get_decl_kind(c, user), Z3_OP_UNINTERPRETED, "{name:?}");
        }
        // A null decl is an error, not an uninterpreted symbol.
        assert_eq!(Z3_get_decl_kind(c, ptr::null_mut()), Z3_OP_UNINTERPRETED);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// S20: for `p, not q`, z3py's `is_true(m[p])` and `is_false(m[q])` are both
/// True on z3; AY's model values had no decl, so both read False.
#[test]
fn bool_model_values_have_true_false_decls() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let bool_sort = Z3_mk_bool_sort(c);
        let (p, q) = (konst(c, c"pp", bool_sort), konst(c, c"qq", bool_sort));
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, p);
        Z3_solver_assert(c, s, Z3_mk_not(c, q));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        for (atom, kind) in [(p, Z3_OP_TRUE), (q, Z3_OP_FALSE)] {
            let mut value: Z3_ast = 0;
            assert!(Z3_model_eval(c, m, atom, true, &raw mut value));
            assert_eq!(Z3_get_decl_kind(c, Z3_get_app_decl(c, value)), kind);
        }
        Z3_del_context(c);
    }
}

/// C16 / probes O4, O5: z3py's model enumeration applies each model decl
/// (`d() != m[d]`). AY panicked inside `Z3_mk_app` ("does not match a
/// registered native declaration"). On z3, `b` asserted true has 1 model.
#[test]
fn decls_from_models_and_apps_apply_to_their_constant() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c0 = ctx();
        let x = konst(c0, c"x", Z3_mk_int_sort(c0));
        assert_eq!(Z3_mk_app(c0, Z3_get_app_decl(c0, x), 0, ptr::null()), x);
        Z3_del_context(c0);

        // `b` is the only constant of this context, so the count does not
        // depend on which constants a model lists.
        let c = ctx();
        let b = konst(c, c"b", Z3_mk_bool_sort(c));
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, b);
        let mut models = 0;
        while models < 5 && Z3_solver_check(c, s) == Z3_L_TRUE {
            models += 1;
            let m = Z3_solver_get_model(c, s);
            let mut block = Vec::new();
            for i in 0..Z3_model_get_num_consts(c, m) {
                let d = Z3_model_get_const_decl(c, m, i);
                let constant = Z3_mk_app(c, d, 0, ptr::null());
                assert_ne!(constant, 0, "model decl {i} must apply");
                assert_eq!(Z3_get_error_code(c), Z3_OK);
                let value = Z3_model_get_const_interp(c, m, d);
                block.push(Z3_mk_not(c, Z3_mk_eq(c, constant, value)));
            }
            Z3_solver_assert(c, s, Z3_mk_or(c, block.len() as c_uint, block.as_ptr()));
        }
        assert_eq!(models, 1);
        Z3_del_context(c);
    }
}

/// S9 `substitute((a+1)+1 == 5, a+1 -> b)` is `b + 1 == 5` on z3 (unsat with
/// `b != 4`); AY stores `a + 2 == 5`, has no `a + 1` to replace and returned
/// the formula unchanged (sat). S10 `substitute(Not(Not p), Not p -> q)` is
/// `Not(q)` on z3; AY stores `p`. Lost patterns must fail closed; faithfully
/// retained arithmetic patterns must instead substitute correctly.
#[test]
fn substitute_refuses_a_compound_pattern_rewritten_away() {
    // SAFETY: every handle lives in one context; arrays outlive each call.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let (a, b) = (konst(c, c"a", int), konst(c, c"b", int));
        let one = Z3_mk_int(c, 1, int);
        let a1 = Z3_mk_add(c, 2, [a, one].as_ptr());
        let lhs = Z3_mk_add(c, 2, [a1, one].as_ptr());
        let f = Z3_mk_eq(c, lhs, Z3_mk_int(c, 5, int));
        let got = Z3_substitute(c, f, 1, [a1].as_ptr(), [b].as_ptr());
        let error = Z3_get_error_code(c);
        if got == 0 {
            assert_eq!(error, Z3_INVALID_ARG);
        } else {
            assert_eq!(error, Z3_OK);
            // Faithfully retained patterns are supported, not quarantined.
            // Substitution must make this true at b=4 and false at b=3.
            for (value, expected) in [(4, Z3_L_TRUE), (3, Z3_L_FALSE)] {
                let grounded =
                    Z3_substitute(c, got, 1, [b].as_ptr(), [Z3_mk_int(c, value, int)].as_ptr());
                assert_eq!(Z3_get_bool_value(c, Z3_simplify(c, grounded)), expected);
            }
        }

        let bool_sort = Z3_mk_bool_sort(c);
        let (p, q) = (konst(c, c"p", bool_sort), konst(c, c"q", bool_sort));
        let not_p = Z3_mk_not(c, p);
        let g = Z3_mk_not(c, not_p);
        assert_eq!(Z3_substitute(c, g, 1, [not_p].as_ptr(), [q].as_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        // Z3_update_term on the same shape fails closed too: `g` is stored as
        // the atom `p`, not as the `Not` the caller built.
        assert_eq!(Z3_update_term(c, g, 1, [q].as_ptr()), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        // A compound pattern that is present still substitutes, as in z3py's
        // doctest `substitute(f(x) + f(y), (f(x), 1), (f(y), 1))` -> `1 + 1`.
        let f_name = Z3_mk_string_symbol(c, c"f".as_ptr());
        let fd = Z3_mk_func_decl(c, f_name, 1, [int].as_ptr(), int);
        let fa = Z3_mk_app(c, fd, 1, [a].as_ptr());
        let fb = Z3_mk_app(c, fd, 1, [b].as_ptr());
        let sum = Z3_mk_add(c, 2, [fa, fb].as_ptr());
        let got = Z3_substitute(c, sum, 2, [fa, fb].as_ptr(), [one, one].as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let mut numeral = 0;
        assert!(Z3_get_numeral_int(c, Z3_simplify(c, got), &raw mut numeral));
        assert_eq!(numeral, 2);
        Z3_del_context(c);
    }
}

/// z3 reports datatype operators as `Z3_OP_DT_CONSTRUCTOR` (2048) and
/// `Z3_OP_DT_IS` (2050), also for the decl read back from an application
/// (z3util's `is_expr_val(On)` is True on z3).
#[test]
fn datatype_decls_report_z3_kinds() {
    // SAFETY: every handle lives in one context; the output arrays hold `n`.
    unsafe {
        let c = ctx();
        let names = [c"On", c"Off"].map(|n| Z3_mk_string_symbol(c, n.as_ptr()));
        let mut consts = [ptr::null_mut(); 2];
        let mut testers = [ptr::null_mut(); 2];
        let sort_name = Z3_mk_string_symbol(c, c"LOnOff".as_ptr());
        let sort = Z3_mk_enumeration_sort(
            c,
            sort_name,
            2,
            names.as_ptr(),
            consts.as_mut_ptr(),
            testers.as_mut_ptr(),
        );
        assert!(!sort.is_null());
        assert_eq!(Z3_get_decl_kind(c, consts[0]), Z3_OP_DT_CONSTRUCTOR);
        assert_eq!(Z3_get_decl_kind(c, testers[0]), Z3_OP_DT_IS);
        let on = Z3_mk_app(c, consts[0], 0, ptr::null());
        let read_back = Z3_get_app_decl(c, on);
        assert_eq!(Z3_get_decl_kind(c, read_back), Z3_OP_DT_CONSTRUCTOR);
        let block = konst(c, c"Block", sort);
        let user = Z3_get_app_decl(c, block);
        assert_eq!(Z3_get_decl_kind(c, user), Z3_OP_UNINTERPRETED);
        Z3_del_context(c);
    }
}
