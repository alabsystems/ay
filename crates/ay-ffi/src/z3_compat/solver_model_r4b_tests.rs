// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression battery for the round-3 verification of the Z3 C API, second
//! part (see `solver_model_r4_tests` for the parse binding): Optimize texts,
//! models, objectives and assumptions; the backstop's completion of
//! floating-point constants; translated models; Boolean and floating-point
//! decl kinds; division by zero under quantifiers; tactic timeouts; and the
//! printing of binders and de Bruijn variables.

use std::ffi::{CStr, CString};

use super::solver_model_scope_tests::{evaluates_true, mk_ctx, named_const};
use super::*;

unsafe fn error_message(c: Z3_context) -> String {
    // SAFETY: live context.
    unsafe {
        CStr::from_ptr(Z3_get_error_msg(c, Z3_get_error_code(c)))
            .to_string_lossy()
            .into_owned()
    }
}

/// Every name of the published model of `m`.
unsafe fn model_decl_names(c: Z3_context, m: Z3_model) -> Vec<String> {
    // SAFETY: live context and model.
    unsafe {
        let mut names = Vec::new();
        for i in 0..Z3_model_get_num_consts(c, m) {
            let d = Z3_model_get_const_decl(c, m, i);
            names.push(
                CStr::from_ptr(Z3_get_symbol_string(c, Z3_get_decl_name(c, d)))
                    .to_string_lossy()
                    .into_owned(),
            );
        }
        for i in 0..Z3_model_get_num_funcs(c, m) {
            let d = Z3_model_get_func_decl(c, m, i);
            names.push(
                CStr::from_ptr(Z3_get_symbol_string(c, Z3_get_decl_name(c, d)))
                    .to_string_lossy()
                    .into_owned(),
            );
        }
        names.sort();
        names
    }
}

/// verify-3 R6: an Optimize text's names are the context's.
#[test]
fn optimize_from_string_binds_the_contexts_constant() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let a = named_const(c, "a", int);
        let o = Z3_mk_optimize(c);
        let text = CString::new("(declare-fun a () Int)(assert (> a 2))").expect("no NUL");
        Z3_optimize_from_string(c, o, text.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        Z3_optimize_assert(c, o, Z3_mk_eq(c, a, Z3_mk_int(c, 0, int)));
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
        Z3_del_context(c);

        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let a = named_const(c, "a", int);
        let o = Z3_mk_optimize(c);
        let text =
            CString::new("(declare-fun a () Int)(assert (< a 5))(maximize a)").expect("no NUL");
        Z3_optimize_from_string(c, o, text.as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK, "{}", error_message(c));
        Z3_optimize_assert(c, o, Z3_mk_not(c, Z3_mk_eq(c, a, Z3_mk_int(c, 4, int))));
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        let m = Z3_optimize_get_model(c, o);
        assert!(evaluates_true(c, m, Z3_mk_eq(c, a, Z3_mk_int(c, 3, int))));
        assert_eq!(model_decl_names(c, m), vec!["a".to_string()]);
        Z3_del_context(c);
    }
}

/// verify-3 R5 and the round-3 verifier's `f(x) == x` form: an Optimize sat
/// model interprets the caller's function, so every hard constraint holds
/// under z3's completion (or the optimum is not published as sat).
#[test]
fn optimize_models_carry_function_tables() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let x = named_const(c, "x", int);
        let name = CString::new("f").expect("no NUL");
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, name.as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        let o = Z3_mk_optimize(c);
        let fx = Z3_mk_app(c, f, 1, [x].as_ptr());
        let f2 = Z3_mk_app(c, f, 1, [Z3_mk_int(c, 2, int)].as_ptr());
        let hard = [
            Z3_mk_eq(c, fx, Z3_mk_int(c, 5, int)),
            Z3_mk_lt(c, x, Z3_mk_int(c, 3, int)),
            Z3_mk_gt(c, f2, Z3_mk_int(c, 7, int)),
        ];
        for &h in &hard {
            Z3_optimize_assert(c, o, h);
        }
        Z3_optimize_maximize(c, o, x);
        let r = Z3_optimize_check(c, o, 0, ptr::null());
        assert_ne!(r, Z3_L_FALSE);
        if r == Z3_L_TRUE {
            let m = Z3_optimize_get_model(c, o);
            for &h in &hard {
                assert!(
                    evaluates_true(c, m, h),
                    "optimum model violates a hard constraint:\n{}",
                    CStr::from_ptr(Z3_model_to_string(c, m)).to_string_lossy()
                );
            }
        }
        Z3_del_context(c);
    }
}

/// verify-3 C1: maximizing a variable that occurs in a disequality panicked
/// in the LRA optimizer ("unexpected TheoryResult variant").
#[test]
fn unbounded_objective_under_a_disequality_does_not_panic() {
    for real in [false, true] {
        // SAFETY: every handle below belongs to the live context `c`.
        unsafe {
            let c = mk_ctx();
            let sort = if real {
                Z3_mk_real_sort(c)
            } else {
                Z3_mk_int_sort(c)
            };
            let b = named_const(c, "b", sort);
            let d = named_const(c, "d", sort);
            let o = Z3_mk_optimize(c);
            let ne = Z3_mk_not(c, Z3_mk_eq(c, b, d));
            Z3_optimize_assert(c, o, ne);
            Z3_optimize_maximize(c, o, b);
            let r = Z3_optimize_check(c, o, 0, ptr::null());
            let message = error_message(c);
            assert!(!message.contains("panic"), "{message}");
            if r == Z3_L_TRUE {
                let m = Z3_optimize_get_model(c, o);
                assert!(evaluates_true(c, m, ne));
            }
            // The handle stays usable.
            Z3_optimize_assert(c, o, Z3_mk_eq(c, b, d));
            assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_FALSE);
            Z3_del_context(c);
        }
    }
}

/// verify-3 K1: a model translated into a fresh context names the caller's
/// declarations there.
#[test]
fn translated_models_name_the_callers_declarations() {
    // SAFETY: every handle below belongs to its live context.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let x = named_const(c, "x", int);
        let name = CString::new("g").expect("no NUL");
        let g = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, name.as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, Z3_mk_int(c, 3, int)));
        let gx = Z3_mk_app(c, g, 1, [x].as_ptr());
        Z3_solver_assert(c, s, Z3_mk_eq(c, gx, Z3_mk_int(c, 9, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let c2 = mk_ctx();
        let m2 = Z3_model_translate(c, m, c2);
        assert!(!m2.is_null());
        assert_eq!(
            model_decl_names(c2, m2),
            vec!["g".to_string(), "x".to_string()]
        );
        let int2 = Z3_mk_int_sort(c2);
        let x2 = named_const(c2, "x", int2);
        assert!(evaluates_true(
            c2,
            m2,
            Z3_mk_gt(c2, x2, Z3_mk_int(c2, 3, int2))
        ));
        Z3_del_context(c2);
        Z3_del_context(c);
    }
}

/// verify-3 M1/M2: floating-point and rounding-mode sorts report z3's kinds,
/// and model completion reads an absent floating-point constant as NaN.
#[test]
fn floating_point_sort_kinds_and_completion() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let fp16 = Z3_mk_fpa_sort_16(c);
        assert_eq!(Z3_get_sort_kind(c, fp16), Z3_FLOATING_POINT_SORT);
        let rm = Z3_mk_fpa_rounding_mode_sort(c);
        assert_eq!(Z3_get_sort_kind(c, rm), Z3_ROUNDING_MODE_SORT);
        let fa = named_const(c, "fa", fp16);
        let fb = named_const(c, "fb", fp16);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_fpa_is_zero(c, fa));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        assert!(evaluates_true(c, m, Z3_mk_fpa_is_nan(c, fb)));
        Z3_del_context(c);
    }
}

/// verify-3 R5's empty-printing values: `true` / `false` (built, or returned
/// by `Z3_model_eval`) are z3's nullary applications `true` / `false`.
#[test]
fn boolean_constants_are_true_and_false_applications() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        for (t, kind, name) in [
            (Z3_mk_true(c), Z3_OP_TRUE, "true"),
            (Z3_mk_false(c), Z3_OP_FALSE, "false"),
        ] {
            assert_eq!(Z3_get_ast_kind(c, t), Z3_APP_AST);
            let d = Z3_get_app_decl(c, t);
            assert!(!d.is_null());
            assert_eq!(Z3_get_decl_kind(c, d), kind);
            assert_eq!(
                CStr::from_ptr(Z3_get_symbol_string(c, Z3_get_decl_name(c, d))).to_string_lossy(),
                name
            );
        }
        Z3_del_context(c);
    }
}

/// verify-3 W2: a quantified formula over a division by a literal zero is
/// satisfiable (`div0(-1)` may be 4), and no check of it, first or repeated,
/// in this solver or another, answers unsat (the exact closed-sentence lane
/// read `(div -1 0)` as a fixed value and refuted it).
#[test]
fn division_by_literal_zero_under_a_quantifier_is_never_refuted() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let qi = named_const(c, "qi", int);
        let div = Z3_mk_div(c, Z3_mk_int(c, -1, int), Z3_mk_int(c, 0, int));
        let range = Z3_mk_and(
            c,
            2,
            [
                Z3_mk_ge(c, qi, Z3_mk_int(c, 0, int)),
                Z3_mk_le(c, qi, Z3_mk_int(c, 3, int)),
            ]
            .as_ptr(),
        );
        let body = Z3_mk_implies(c, range, Z3_mk_le(c, Z3_mk_int(c, 4, int), div));
        let qapp = Z3_to_app(c, qi);
        let f = Z3_mk_forall_const(c, 0, 1, [qapp].as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, f);
        for _ in 0..3 {
            assert_ne!(Z3_solver_check(c, s), Z3_L_FALSE);
        }
        let t = Z3_mk_solver(c);
        Z3_solver_assert(c, t, f);
        assert_ne!(Z3_solver_check(c, t), Z3_L_FALSE);
        // `or` form: unsat only if `(div 9 0)` had a fixed value.
        let g_body = Z3_mk_or(
            c,
            2,
            [
                Z3_mk_lt(c, qi, Z3_mk_int(c, 0, int)),
                Z3_mk_eq(
                    c,
                    Z3_mk_int(c, 4, int),
                    Z3_mk_div(c, Z3_mk_int(c, 9, int), Z3_mk_int(c, 0, int)),
                ),
            ]
            .as_ptr(),
        );
        let g = Z3_mk_forall_const(c, 0, 1, [qapp].as_ptr(), 0, ptr::null(), g_body);
        let u = Z3_mk_solver(c);
        Z3_solver_assert(c, u, g);
        assert_ne!(Z3_solver_check(c, u), Z3_L_FALSE);
        Z3_del_context(c);
    }
}

/// z3py's `add_soft` passes the empty symbol as the default group, and z3
/// returns one objective per group: the soft constraints of one group are
/// optimized, and the group's value is the weight it violates.
#[test]
fn soft_constraints_of_the_default_group_are_one_objective() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let bool_sort = Z3_mk_bool_sort(c);
        let a = named_const(c, "a", bool_sort);
        let b = named_const(c, "b", bool_sort);
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_or(c, 2, [a, b].as_ptr()));
        let empty = CString::new("").expect("no NUL");
        let id = Z3_mk_string_symbol(c, empty.as_ptr());
        let one = CString::new("1").expect("no NUL");
        let two = CString::new("2").expect("no NUL");
        let i0 = Z3_optimize_assert_soft(c, o, Z3_mk_not(c, a), one.as_ptr(), id);
        let i1 = Z3_optimize_assert_soft(c, o, Z3_mk_not(c, b), two.as_ptr(), id);
        assert_eq!((i0, i1), (0, 0));
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        let cost = Z3_optimize_get_lower(c, o, 0);
        assert!(cost != 0, "{}", error_message(c));
        let mut value: i64 = -1;
        assert!(Z3_get_numeral_int64(c, cost, &raw mut value));
        assert_eq!(value, 1, "violating Not(a) costs 1");
        // A second Optimize in the same context (z3 allows any number).
        let o2 = Z3_mk_optimize(c);
        assert!(!o2.is_null(), "{}", error_message(c));
        Z3_optimize_assert(c, o2, a);
        assert_eq!(Z3_optimize_check(c, o2, 0, ptr::null()), Z3_L_TRUE);
        assert_eq!(Z3_optimize_check(c, o, 0, ptr::null()), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

/// verify-3 M3: a tactic solver's timeout bounds the whole check, the nested
/// checks of `ctx-simplify` included (it ran 43-50 s under a 3 s timeout).
#[test]
fn a_tactic_solver_honours_its_timeout() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let real = Z3_mk_real_sort(c);
        let ta = named_const(c, "ta", int);
        let tx = named_const(c, "tx", real);
        let names = ["simplify", "propagate-values", "ctx-simplify", "smt"];
        let mut tactic: Z3_tactic = ptr::null_mut();
        for name in names {
            let name = CString::new(name).expect("no NUL");
            let t = Z3_mk_tactic(c, name.as_ptr());
            tactic = if tactic.is_null() {
                t
            } else {
                Z3_tactic_and_then(c, tactic, t)
            };
        }
        let s = Z3_mk_solver_from_tactic(c, tactic);
        let params = Z3_mk_params(c);
        let timeout = CString::new("timeout").expect("no NUL");
        Z3_params_set_uint(c, params, Z3_mk_string_symbol(c, timeout.as_ptr()), 1000);
        Z3_solver_set_params(c, s, params);
        let seven_ta = Z3_mk_mul(c, 2, [Z3_mk_int(c, 7, int), ta].as_ptr());
        Z3_solver_assert(c, s, Z3_mk_gt(c, Z3_mk_int2real(c, seven_ta), tx));
        let two = Z3_mk_int(c, 2, int);
        let five = Z3_mk_int(c, 5, int);
        Z3_solver_assert(
            c,
            s,
            Z3_mk_gt(c, Z3_mk_mod(c, ta, two), Z3_mk_mod(c, ta, five)),
        );
        let started = std::time::Instant::now();
        let r = Z3_solver_check(c, s);
        assert_ne!(r, Z3_L_FALSE);
        assert!(
            started.elapsed() < Duration::from_secs(10),
            "a 1 s timeout took {:?}",
            started.elapsed()
        );
        Z3_del_context(c);
    }
}

/// verify-3 K1 and the round-3 verifier's printing gaps: a binder shows the
/// caller's name, a de Bruijn variable prints as `(:var i)`, and unary minus
/// is z3's negation.
#[test]
fn binder_names_de_bruijn_variables_and_negation_print_as_in_z3() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let v = Z3_mk_bound(c, 0, int);
        let text = CStr::from_ptr(Z3_ast_to_string(c, v))
            .to_string_lossy()
            .into_owned();
        assert_eq!(text, "(:var 0)");
        let x = named_const(c, "x", int);
        let neg = Z3_mk_unary_minus(c, x);
        if Z3_get_ast_kind(c, neg) == Z3_APP_AST {
            let d = Z3_get_app_decl(c, neg);
            if Z3_get_arity(c, d) == 1 {
                assert_eq!(Z3_get_decl_kind(c, d), Z3_OP_UMINUS);
            }
        }
        let y = named_const(c, "y", int);
        let q = Z3_mk_exists_const(
            c,
            0,
            1,
            [Z3_to_app(c, y)].as_ptr(),
            0,
            ptr::null(),
            Z3_mk_gt(c, y, x),
        );
        // C03: the body names the binder by de Bruijn index, so
        // `substitute_vars` instantiates it.
        let body = Z3_get_quantifier_body(c, q);
        let shown = CStr::from_ptr(Z3_ast_to_string(c, body))
            .to_string_lossy()
            .into_owned();
        assert!(
            shown.contains("(:var 0)") && !shown.contains('y'),
            "{shown}"
        );
        let seven = Z3_mk_int(c, 7, int);
        let instance = Z3_substitute_vars(c, body, 1, [seven].as_ptr());
        let shown = CStr::from_ptr(Z3_ast_to_string(c, instance))
            .to_string_lossy()
            .into_owned();
        assert!(shown.contains('7') && !shown.contains(":var"), "{shown}");
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_gt(c, x, Z3_mk_int(c, 0, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let mut out: Z3_ast = 0;
        assert!(Z3_model_eval(c, m, q, true, &raw mut out));
        if Z3_get_ast_kind(c, out) == Z3_QUANTIFIER_AST {
            let name = Z3_get_quantifier_bound_name(c, out, 0);
            assert_eq!(
                CStr::from_ptr(Z3_get_symbol_string(c, name)).to_string_lossy(),
                "y"
            );
        }
        Z3_del_context(c);
    }
}

/// The round-3 verifiers' Optimize value gaps: an unbounded objective's value
/// is z3's `oo` and an unattained one's is `value + eps*epsilon` (both were a
/// null AST, which z3py raised on).
#[test]
fn unbounded_and_unattained_optima_have_values() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let x = named_const(c, "x", int);
        let y = named_const(c, "y", int);
        let o = Z3_mk_optimize(c);
        Z3_optimize_assert(c, o, Z3_mk_gt(c, x, y));
        let h = Z3_optimize_maximize(c, o, x);
        let r = Z3_optimize_check(c, o, 0, ptr::null());
        if r == Z3_L_TRUE {
            let v = Z3_optimize_get_upper(c, o, h);
            assert!(v != 0, "{}", error_message(c));
            assert_eq!(
                CStr::from_ptr(Z3_ast_to_string(c, v)).to_string_lossy(),
                "oo"
            );
        }
        let c2 = mk_ctx();
        let real = Z3_mk_real_sort(c2);
        let r_ = named_const(c2, "r", real);
        let o2 = Z3_mk_optimize(c2);
        Z3_optimize_assert(c2, o2, Z3_mk_lt(c2, r_, Z3_mk_real(c2, 3, 1)));
        let h2 = Z3_optimize_maximize(c2, o2, r_);
        if Z3_optimize_check(c2, o2, 0, ptr::null()) == Z3_L_TRUE {
            let v = Z3_optimize_get_upper(c2, o2, h2);
            assert!(v != 0, "{}", error_message(c2));
            let shown = CStr::from_ptr(Z3_ast_to_string(c2, v))
                .to_string_lossy()
                .into_owned();
            assert!(shown.contains("epsilon") && shown.contains('3'), "{shown}");
        }
        Z3_del_context(c2);
        Z3_del_context(c);
    }
}
