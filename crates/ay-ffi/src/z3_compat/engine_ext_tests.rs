// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Track B batch 3a: engine-backed C-API (mk set/lambda, fp numeral
//! introspection, substitute/is_ground, mk_model, qe).

use super::super::*;

unsafe fn ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

#[test]
fn fp_numeral_introspection() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_fpa_sort_32(c);

        let nan = Z3_mk_fpa_nan(c, s);
        assert!(Z3_fpa_is_numeral(c, nan));
        assert!(Z3_fpa_is_numeral_nan(c, nan));
        assert!(!Z3_fpa_is_numeral_inf(c, nan));
        assert!(!Z3_fpa_is_numeral_zero(c, nan));

        let inf = Z3_mk_fpa_inf(c, s, false); // +inf
        assert!(Z3_fpa_is_numeral_inf(c, inf));
        assert!(Z3_fpa_is_numeral_positive(c, inf));

        let zero = Z3_mk_fpa_zero(c, s, false); // +0
        assert!(Z3_fpa_is_numeral_zero(c, zero));

        // A finite normal value: 1.5
        let onefive = Z3_mk_fpa_numeral_double(c, 1.5, s);
        assert!(Z3_fpa_is_numeral(c, onefive));
        assert!(Z3_fpa_is_numeral_normal(c, onefive));
        let mut sgn: bool = true;
        assert!(Z3_fpa_get_numeral_sign(c, onefive, &raw mut sgn));
        assert!(!sgn); // positive → sign bit false

        // A symbolic FP const is NOT a numeral.
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), s);
        assert!(!Z3_fpa_is_numeral(c, x));

        Z3_del_context(c);
    }
}

#[test]
fn set_operations_are_well_sorted() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let full = Z3_mk_full_set(c, int);
        let empty = Z3_mk_empty_set(c, int);
        let u = Z3_mk_set_union(c, 2, [full, empty].as_ptr());
        let i = Z3_mk_set_intersect(c, 2, [full, empty].as_ptr());
        let d = Z3_mk_set_difference(c, full, empty);
        let comp = Z3_mk_set_complement(c, empty);
        for t in [u, i, d, comp] {
            assert_ne!(t, 0);
            // A set is an (Array elem Bool)
            assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, t)), Z3_ARRAY_SORT);
        }
        Z3_del_context(c);
    }
}

#[test]
fn mk_model_is_non_null() {
    unsafe {
        let c = ctx();
        let m = Z3_mk_model(c);
        assert!(!m.is_null());
        Z3_del_context(c);
    }
}

#[test]
fn is_ground_and_substitute() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), int);
        let y = Z3_mk_const(c, Z3_mk_string_symbol(c, c"y".as_ptr()), int);
        // (+ x y) is ground (only declared consts, no bound vars)
        let sum = Z3_mk_add(c, 2, [x, y].as_ptr());
        assert!(Z3_is_ground(c, sum));

        // substitute x -> y in (+ x y) gives (+ y y)
        let from = [x];
        let to = [y];
        let subst = Z3_substitute(c, sum, 1, from.as_ptr(), to.as_ptr());
        assert_ne!(subst, 0);
        Z3_del_context(c);
    }
}

#[test]
fn str_lex_ops_build() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_string_sort(c);
        let a = Z3_mk_const(c, Z3_mk_string_symbol(c, c"a".as_ptr()), s);
        let b = Z3_mk_const(c, Z3_mk_string_symbol(c, c"b".as_ptr()), s);
        let le = Z3_mk_str_le(c, a, b);
        let lt = Z3_mk_str_lt(c, a, b);
        assert_ne!(le, 0);
        assert_ne!(lt, 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, le)), Z3_BOOL_SORT);
        Z3_del_context(c);
    }
}

/// Render an AST via `Z3_ast_to_string` (test helper).
unsafe fn ast_str(c: Z3_context, a: Z3_ast) -> String {
    // SAFETY: caller passes a live context and AST from that context.
    unsafe {
        std::ffi::CStr::from_ptr(Z3_ast_to_string(c, a))
            .to_string_lossy()
            .into_owned()
    }
}

/// Regression (2026-07-10 re-audit, gap #4 WRONG-RESULT): the de Bruijn
/// `Z3_mk_lambda` path must resolve `__db{k}` bound occurrences into the
/// named binder vars. Before the fix, `select((lambda x:Int. x+1), 41)`
/// "simplified" to the OPEN term `(+ __db0 1)` instead of `42` (libz3: `42`),
/// and the lambda printed the nonstandard `(lambda-array x ...)` shape
/// instead of z3's `(lambda ((x Int)) (+ x 1))`.
#[test]
fn lambda_de_bruijn_beta_reduction_and_print() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // lambda x:Int. x + 1  (body over de Bruijn index 0)
        let db0 = Z3_mk_bound(c, 0, int);
        let one = Z3_mk_int(c, 1, int);
        let add_args = [db0, one];
        let body = Z3_mk_add(c, 2, add_args.as_ptr());
        let xn = Z3_mk_string_symbol(c, c"x".as_ptr());
        let lam = Z3_mk_lambda(c, 1, &raw const int, &raw const xn, body);
        assert_ne!(lam, 0);
        // z3-standard binder shape, no internal `lambda-array` / `__db` names.
        assert_eq!(ast_str(c, lam), "(lambda ((x Int)) (+ x 1))");
        // Beta reduction: select at 41 → 42, twin-checked vs libz3.
        let sel = Z3_mk_select(c, lam, Z3_mk_int(c, 41, int));
        let simp = Z3_simplify(c, sel);
        let s = ast_str(c, simp);
        assert_eq!(s, "42", "select(lambda x. x+1, 41) must simplify to 42");
        assert!(!s.contains("__db"), "no open de Bruijn var may leak: {s}");
        Z3_del_context(c);
    }
}

/// Nested de Bruijn lambdas: `select((lambda x. select((lambda y. x+y), 10)), 5)`
/// must evaluate to `15` (libz3-twin-checked) — the outer binder's occurrence
/// inside the inner lambda is index 1, and surviving indices must be
/// re-anchored when the inner binder is constructed/reduced.
#[test]
fn lambda_de_bruijn_nested_beta_reduction() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let db0 = Z3_mk_bound(c, 0, int);
        let db1 = Z3_mk_bound(c, 1, int);
        let a2 = [db1, db0];
        let inner_body = Z3_mk_add(c, 2, a2.as_ptr()); // x + y
        let yn = Z3_mk_string_symbol(c, c"y".as_ptr());
        let inner = Z3_mk_lambda(c, 1, &raw const int, &raw const yn, inner_body);
        let inner_sel = Z3_mk_select(c, inner, Z3_mk_int(c, 10, int));
        let xn = Z3_mk_string_symbol(c, c"x".as_ptr());
        let outer = Z3_mk_lambda(c, 1, &raw const int, &raw const xn, inner_sel);
        let outer_sel = Z3_mk_select(c, outer, Z3_mk_int(c, 5, int));
        let s = ast_str(c, Z3_simplify(c, outer_sel));
        assert_eq!(s, "15", "nested lambda beta reduction must yield 15");
        Z3_del_context(c);
    }
}

/// Solver-path verdicts for select-over-lambda must match libz3:
/// `(= (select (lambda x. x+1) 41) 42)` is sat; `(= ... 43)` alone is unsat.
#[test]
fn lambda_select_solver_verdicts_match_z3() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let db0 = Z3_mk_bound(c, 0, int);
        let one = Z3_mk_int(c, 1, int);
        let add_args = [db0, one];
        let body = Z3_mk_add(c, 2, add_args.as_ptr());
        let xn = Z3_mk_string_symbol(c, c"x".as_ptr());
        let lam = Z3_mk_lambda(c, 1, &raw const int, &raw const xn, body);
        let sel = Z3_mk_select(c, lam, Z3_mk_int(c, 41, int));

        let s1 = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s1);
        Z3_solver_assert(c, s1, Z3_mk_eq(c, sel, Z3_mk_int(c, 42, int)));
        assert_eq!(Z3_solver_check(c, s1), Z3_L_TRUE, "= 42 must be sat");

        let s2 = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s2);
        Z3_solver_assert(c, s2, Z3_mk_eq(c, sel, Z3_mk_int(c, 43, int)));
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_FALSE,
            "= 43 alone must be unsat"
        );
        Z3_del_context(c);
    }
}
