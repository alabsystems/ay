// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression battery for the Z3 C API findings of the 2026-09-30 differential
//! fuzz run (z3py 5.1.0 against AY's dylib), continuing
//! `solver_model_scope_tests`: Int powers are Real-sorted; function tables keep
//! negative-Int rows and bit-vector ranges; context state (built-only terms,
//! model evaluation, assumptions) never empties another check's model; a bound
//! variable is not a model constant and a quantifier-only constant is; decimal
//! numerals parse; the evaluator folds ground powers and const arrays; a solver
//! timeout bounds a nonlinear check; and a mixed Int/Real conjunction is
//! published with a valid model.

use std::ffi::{CStr, CString};

use super::solver_model_scope_tests::{
    evaluates_true, mk_ctx, model_const_names, named_const, sat_only_with_valid_model,
};
use super::*;

/// A one-argument function declaration `name : dom -> range`.
unsafe fn func1(c: Z3_context, name: &str, dom: Z3_sort, range: Z3_sort) -> Z3_func_decl {
    let name = CString::new(name).expect("test symbol has no NUL");
    // SAFETY: live context and sorts; `name` outlives the call.
    unsafe {
        Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, name.as_ptr()),
            1,
            [dom].as_ptr(),
            range,
        )
    }
}

/// `f(arg)`.
unsafe fn app1(c: Z3_context, f: Z3_func_decl, arg: Z3_ast) -> Z3_ast {
    // SAFETY: live context, declaration and argument of the declared sort.
    unsafe { Z3_mk_app(c, f, 1, [arg].as_ptr()) }
}

#[test]
fn an_int_power_is_real_sorted_so_its_division_is_real() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let a = named_const(c, "a", int);
        let sq = Z3_mk_power(c, a, Z3_mk_int(c, 2, int));
        // z3 5.1: `(a**2).sort()` is Real.
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, sq)), Z3_REAL_SORT);
        // So `a**2 / 2` is real division: a = 3 gives 9/2, never 4.
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_eq(c, a, Z3_mk_int(c, 3, int)));
        let half = Z3_mk_div(c, sq, Z3_mk_real(c, 2, 1));
        Z3_solver_assert(c, s, Z3_mk_eq(c, half, Z3_mk_real(c, 4, 1)));
        // z3 answers unsat; the integer reading (`9 div 2 = 4`) answered sat.
        assert_ne!(Z3_solver_check(c, s), Z3_L_TRUE);
        // Integer-only operators reject the Real power, as in z3.
        assert_eq!(
            Z3_mk_mod(c, sq, a),
            0,
            "mod of a Real power must be refused"
        );
        Z3_del_context(c);
    }
}

#[test]
fn function_tables_keep_rows_and_values_at_negative_int_points() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let f = func1(c, "f", int, int);
        let pr = func1(c, "pr", int, Z3_mk_bool_sort(c));
        let k = |v: i32| Z3_mk_int(c, v, int);
        let goals = [
            Z3_mk_eq(c, app1(c, f, k(-1)), k(5)),
            Z3_mk_eq(c, app1(c, f, k(2)), k(6)),
            app1(c, pr, k(-1)),
            Z3_mk_not(c, app1(c, pr, k(5))),
        ];
        let s = Z3_mk_solver(c);
        for &g in &goals {
            Z3_solver_assert(c, s, g);
        }
        assert_eq!(sat_only_with_valid_model(c, s, &goals), Z3_L_TRUE);

        // A negative else value is carried, not published as NULL.
        let neg = Z3_mk_eq(c, app1(c, f, k(1)), k(-1));
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, neg);
        assert_eq!(sat_only_with_valid_model(c, s, &[neg]), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let fi = Z3_model_get_func_interp(c, m, f);
        assert!(!fi.is_null(), "f has an interpretation");
        assert_ne!(
            Z3_func_interp_get_else(c, fi),
            0,
            "the else value is carried"
        );
        Z3_del_context(c);
    }
}

#[test]
fn a_bitvector_ranged_function_reaches_the_model() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let bv8 = Z3_mk_bv_sort(c, 8);
        let bf = func1(c, "bf", bv8, bv8);
        let zero = Z3_mk_int(c, 0, bv8);
        let goal = Z3_mk_bvult(c, zero, app1(c, bf, zero));
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, goal);
        assert_eq!(sat_only_with_valid_model(c, s, &[goal]), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        assert_eq!(Z3_model_get_num_funcs(c, m), 1);
        assert!(Z3_model_has_interp(c, m, bf) || !Z3_model_get_func_interp(c, m, bf).is_null());
        // The model's text carries the table too (it was empty for a
        // functions-only model).
        let text = CStr::from_ptr(Z3_model_to_string(c, m)).to_string_lossy();
        assert!(text.contains("bf"), "model text lacks bf: {text}");
        Z3_del_context(c);
    }
}

#[test]
fn context_state_never_empties_another_checks_model() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let real = Z3_mk_real_sort(c);
        let a = named_const(c, "a", int);
        // A Real-ranged UF application built and never asserted.
        let h = func1(c, "h", int, real);
        let _ = app1(c, h, a);
        let arr = named_const(c, "A", Z3_mk_array_sort(c, int, int));
        let goals = [
            Z3_mk_eq(c, Z3_mk_select(c, arr, a), Z3_mk_int(c, 7, int)),
            Z3_mk_eq(c, a, Z3_mk_int(c, 2, int)),
        ];
        let s = Z3_mk_solver(c);
        for &g in &goals {
            Z3_solver_assert(c, s, g);
        }
        assert_eq!(sat_only_with_valid_model(c, s, &goals), Z3_L_TRUE);

        // Evaluating the model, and a check with a Real-UF assumption, leave
        // the next plain check's model whole.
        let pr = func1(c, "pr", int, Z3_mk_bool_sort(c));
        let x = named_const(c, "x", real);
        let s2 = Z3_mk_solver(c);
        let pr3 = app1(c, pr, Z3_mk_int(c, 3, int));
        Z3_solver_assert(c, s2, pr3);
        let hx = app1(c, func1(c, "h2", real, real), x);
        assert_eq!(
            Z3_solver_check_assumptions(c, s2, 1, [Z3_mk_gt(c, x, hx)].as_ptr()),
            Z3_L_TRUE
        );
        let mut v: Z3_ast = 0;
        assert!(Z3_model_eval(
            c,
            Z3_solver_get_model(c, s2),
            pr3,
            true,
            &raw mut v
        ));
        assert_eq!(sat_only_with_valid_model(c, s2, &[pr3]), Z3_L_TRUE);
        assert_eq!(sat_only_with_valid_model(c, s, &goals), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

#[test]
fn a_bound_variable_is_not_a_model_constant() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let q0 = named_const(c, "q0", int);
        let body = Z3_mk_lt(c, q0, Z3_mk_int(c, 0, int));
        let bound = [Z3_to_app(c, q0)];
        let ex = Z3_mk_exists_const(c, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_simple_solver(c);
        Z3_solver_assert(c, s, ex);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s), Vec::<String>::new());
        Z3_del_context(c);
    }
}

#[test]
fn decimal_numerals_are_exact_reals() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let real = Z3_mk_real_sort(c);
        for (text, want) in [
            ("2.5", "5/2"),
            ("-0.5", "-1/2"),
            ("1e2", "100"),
            ("2.5E-1", "1/4"),
        ] {
            let t = CString::new(text).expect("no NUL");
            let ast = Z3_mk_numeral(c, t.as_ptr(), real);
            assert_ne!(ast, 0, "{text} must be a numeral");
            let got = CStr::from_ptr(Z3_get_numeral_string(c, ast)).to_string_lossy();
            assert_eq!(got, want, "{text}");
        }
        // A non-numeral sets an error code instead of a silent NULL.
        let bad = CString::new("2.5.1").expect("no NUL");
        assert_eq!(Z3_mk_numeral(c, bad.as_ptr(), real), 0);
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        // z3py `FPVal(1.0)` / `FPVal(-2.5)` reach the API as `n/dp<exp>`.
        let f64s = Z3_mk_fpa_sort(c, 11, 53);
        for (text, value) in [("1/1p0", 1.0), ("-5/2p0", -2.5), ("3/1p-1", 1.5)] {
            let t = CString::new(text).expect("no NUL");
            let ast = Z3_mk_numeral(c, t.as_ptr(), f64s);
            assert_ne!(ast, 0, "{text} must be an FP numeral");
            let expected = Z3_mk_fpa_numeral_double(c, value, f64s);
            assert!(Z3_is_eq_ast(c, ast, expected), "{text} must equal {value}");
        }
        Z3_del_context(c);
    }
}

#[test]
fn the_model_evaluator_folds_a_ground_power() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let s = Z3_mk_solver(c);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let eight = Z3_mk_power(c, Z3_mk_int(c, 2, int), Z3_mk_int(c, 3, int));
        let goal = Z3_mk_eq(c, eight, Z3_mk_real(c, 8, 1));
        assert!(evaluates_true(c, m, goal), "2^3 must evaluate to 8");
        // Ground const-array (dis)equalities fold like z3's evaluator.
        let k0 = Z3_mk_const_array(c, int, Z3_mk_int(c, 0, int));
        let k1 = Z3_mk_const_array(c, int, Z3_mk_int(c, 1, int));
        let differ = Z3_mk_not(c, Z3_mk_eq(c, k0, k1));
        assert!(evaluates_true(c, m, differ), "K(0) != K(1)");
        let stored = Z3_mk_store(c, k0, Z3_mk_int(c, 3, int), Z3_mk_int(c, 1, int));
        let restored = Z3_mk_store(c, stored, Z3_mk_int(c, 3, int), Z3_mk_int(c, 0, int));
        assert!(
            evaluates_true(c, m, Z3_mk_eq(c, restored, k0)),
            "store(store(K0,3,1),3,0) = K0"
        );
        Z3_del_context(c);
    }
}

#[test]
fn a_solver_timeout_bounds_a_nonlinear_division_check() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let real = Z3_mk_real_sort(c);
        let x = named_const(c, "x", real);
        let y = named_const(c, "y", real);
        let s = Z3_mk_solver(c);
        let p = Z3_mk_params(c);
        let key = CString::new("timeout").expect("no NUL");
        Z3_params_set_uint(c, p, Z3_mk_string_symbol(c, key.as_ptr()), 2000);
        Z3_solver_set_params(c, s, p);
        let goals = [
            Z3_mk_gt(c, Z3_mk_div(c, y, x), x),
            Z3_mk_eq(c, y, Z3_mk_real(c, 1, 1)),
        ];
        for &g in &goals {
            Z3_solver_assert(c, s, g);
        }
        let started = std::time::Instant::now();
        let r = sat_only_with_valid_model(c, s, &goals);
        let elapsed = started.elapsed();
        assert!(
            elapsed < Duration::from_secs(30),
            "a 2 s timeout ran {elapsed:?} (verdict {r})"
        );
        Z3_del_context(c);
    }
}

#[test]
fn a_constant_occurring_only_under_a_quantifier_stays_in_the_model() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let k = |v: i32| Z3_mk_int(c, v, int);
        let a = named_const(c, "a", int);
        let q = named_const(c, "q", int);
        // z3py `ForAll([q], Implies(And(q >= 3, q <= 6), a == 1))`: z3 [a = 1].
        let guard = Z3_mk_and(c, 2, [Z3_mk_ge(c, q, k(3)), Z3_mk_le(c, q, k(6))].as_ptr());
        let body = Z3_mk_implies(c, guard, Z3_mk_eq(c, a, k(1)));
        let bound = [Z3_to_app(c, q)];
        let all = Z3_mk_forall_const(c, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, all);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s), vec!["a".to_string()]);
        let m = Z3_solver_get_model(c, s);
        assert!(evaluates_true(c, m, Z3_mk_eq(c, a, k(1))), "a must be 1");

        // z3py `ForAll([y], f(y) == y + 1)`: a published sat must interpret f
        // (z3: f = [else -> 1 + Var(0)]), never list the bound y instead.
        let f = func1(c, "f", int, int);
        let y = named_const(c, "y", int);
        let body = Z3_mk_eq(c, app1(c, f, y), Z3_mk_add(c, 2, [y, k(1)].as_ptr()));
        let bound = [Z3_to_app(c, y)];
        let all = Z3_mk_forall_const(c, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, all);
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        assert_eq!(model_const_names(c, s), Vec::<String>::new());
        let m = Z3_solver_get_model(c, s);
        let at5 = Z3_mk_eq(c, app1(c, f, k(5)), k(6));
        assert!(evaluates_true(c, m, at5), "f(5) must be 6");
        // The interpretation's else is the body over the de Bruijn argument.
        let fi = Z3_model_get_func_interp(c, m, f);
        assert!(!fi.is_null(), "f has an interpretation");
        assert_ne!(Z3_func_interp_get_else(c, fi), 0, "f's else is carried");
        Z3_del_context(c);
    }
}

#[test]
fn a_mixed_int_real_conjunction_is_sat_with_a_valid_model() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let real = Z3_mk_real_sort(c);
        let (a, b) = (named_const(c, "a", int), named_const(c, "b", int));
        let (x, y) = (named_const(c, "x", real), named_const(c, "y", real));
        let p = named_const(c, "p", Z3_mk_bool_sort(c));
        // z3py `And(b < a, y == x, p)`: z3 sat; AY answered unknown because the
        // engine's own model gate refused the model it published.
        let goal = Z3_mk_and(c, 3, [Z3_mk_lt(c, b, a), Z3_mk_eq(c, y, x), p].as_ptr());
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, goal);
        assert_eq!(sat_only_with_valid_model(c, s, &[goal]), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

#[test]
fn an_eliminated_real_uf_application_keeps_its_asserted_value() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let real = Z3_mk_real_sort(c);
        // Fuzz case s2/765: `Exists q4. pr(q4 * b)`, `A[b] = 2`, `h(x) = x - 3`
        // published sat with an EMPTY model ("no model value for
        // function-table entry of sort Real").
        let b = named_const(c, "b", int);
        let x = named_const(c, "x", real);
        let arr = named_const(c, "A", Z3_mk_array_sort(c, int, int));
        let h = func1(c, "h", real, real);
        let pr = func1(c, "pr", int, Z3_mk_bool_sort(c));
        let q4 = named_const(c, "q4", int);
        let body = app1(c, pr, Z3_mk_mul(c, 2, [q4, b].as_ptr()));
        let bound = [Z3_to_app(c, q4)];
        let exists = Z3_mk_exists_const(c, 0, 1, bound.as_ptr(), 0, ptr::null(), body);
        let ground = [
            Z3_mk_eq(c, Z3_mk_select(c, arr, b), Z3_mk_int(c, 2, int)),
            Z3_mk_eq(
                c,
                app1(c, h, x),
                Z3_mk_sub(c, 2, [x, Z3_mk_real(c, 3, 1)].as_ptr()),
            ),
        ];
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, exists);
        for &g in &ground {
            Z3_solver_assert(c, s, g);
        }
        // Never sat with a model that falsifies a ground assertion.
        assert_ne!(sat_only_with_valid_model(c, s, &ground), Z3_L_FALSE);
        Z3_del_context(c);
    }
}
