// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Round-3 regression tests, second battery: lambdas through the Z3 C API
//! (verify-2 cases B_501, B_230, B_123, A_726: `Z3_is_lambda` answers for a
//! lambda, so z3py gives it its array sort, and the variable a lambda binds is
//! neither listed in the published model nor replaced by a model value when
//! `Z3_model_eval` reads the lambda); de Bruijn variables of one index at
//! several sorts; a parsed function listed under its own name; a constant's
//! declaration applied to no arguments; and datatype selectors over
//! constructor values in model evaluation.

use std::ffi::{CStr, CString};

use super::solver_model_scope_tests::{
    evaluates_true, mk_ctx, model_const_names, named_const, sat_only_with_valid_model,
};
use super::*;

#[test]
fn a_lambda_is_a_lambda_and_binds_its_variable() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let a = named_const(c, "a", int);
        let q0 = named_const(c, "q0", int);
        let arr = named_const(c, "A", Z3_mk_array_sort(c, int, int));
        let lam = Z3_mk_lambda_const(c, 1, [q0].as_ptr(), q0);
        assert_ne!(lam, 0);
        assert!(Z3_is_lambda(c, lam), "Z3_mk_lambda_const builds a lambda");
        assert!(!Z3_is_lambda(c, q0));
        assert_eq!(
            Z3_get_sort_kind(c, Z3_get_sort(c, lam)),
            Z3_ARRAY_SORT,
            "a lambda over Int -> Int is an array"
        );
        // B_501: (lambda q0. q0) != A or 1 > a: z3 [a = 0]; AY listed q0.
        let goal = Z3_mk_or(
            c,
            2,
            [
                Z3_mk_not(c, Z3_mk_eq(c, lam, arr)),
                Z3_mk_gt(c, Z3_mk_int(c, 1, int), a),
            ]
            .as_ptr(),
        );
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, goal);
        if sat_only_with_valid_model(c, s, &[goal]) == Z3_L_TRUE {
            let names = model_const_names(c, s);
            assert!(
                !names.iter().any(|n| n == "q0"),
                "the lambda's bound variable is not a model constant: {names:?}"
            );
            // A_726: evaluating the lambda keeps its variable bound.
            let m = Z3_solver_get_model(c, s);
            let mut out: Z3_ast = 0;
            if Z3_model_eval(c, m, lam, true, &raw mut out) {
                let text = CStr::from_ptr(Z3_ast_to_string(c, out))
                    .to_string_lossy()
                    .into_owned();
                assert!(
                    !text.contains("lambda-array 0"),
                    "the bound variable was substituted: {text}"
                );
            }
        }
        Z3_del_context(c);
    }
}

#[test]
fn one_de_bruijn_index_takes_several_sorts() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        let boolean = Z3_mk_bool_sort(c);
        let vi = Z3_mk_bound(c, 0, int);
        let vb = Z3_mk_bound(c, 0, boolean);
        assert_ne!(vi, 0);
        assert_ne!(
            vb,
            0,
            "Var(0, Bool) beside Var(0, Int): {:?}",
            Z3_get_error_code(c)
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_get_index_value(c, vb), 0);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, vb)), Z3_BOOL_SORT);
        // A quantifier over the Bool variable binds it: forall p. p or not p.
        let name = Z3_mk_string_symbol(c, c"p".as_ptr());
        let body = Z3_mk_or(c, 2, [vb, Z3_mk_not(c, vb)].as_ptr());
        let q = Z3_mk_forall(
            c,
            0,
            0,
            ptr::null(),
            1,
            [boolean].as_ptr(),
            [name].as_ptr(),
            body,
        );
        assert_ne!(q, 0);
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_not(c, q));
        assert_ne!(
            Z3_solver_check(c, s),
            Z3_L_TRUE,
            "a valid formula's negation is not sat"
        );
        Z3_del_context(c);
    }
}

#[test]
fn parsed_functions_and_nullary_decls_keep_their_names() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let s = Z3_mk_solver(c);
        let text = CString::new(
            "(declare-const a Int) (declare-fun h (Int) Int) (assert (> a 1)) (assert (= (h a) 7))",
        )
        .expect("no NUL");
        Z3_solver_from_string(c, s, text.as_ptr());
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        let m = Z3_solver_get_model(c, s);
        let funcs: Vec<String> = (0..Z3_model_get_num_funcs(c, m))
            .map(|i| {
                let d = Z3_model_get_func_decl(c, m, i);
                CStr::from_ptr(Z3_get_symbol_string(c, Z3_get_decl_name(c, d)))
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        assert_eq!(
            funcs,
            vec!["h".to_string()],
            "no private identity is listed"
        );
        let text = CStr::from_ptr(Z3_model_to_string(c, m))
            .to_string_lossy()
            .into_owned();
        assert!(
            !text.contains("!ay."),
            "model text names private identities: {text}"
        );
        // z3py `d()` for each `d` in `m.decls()`: a constant's declaration
        // applied to no arguments is the constant (it raised a panic).
        let d = Z3_model_get_const_decl(c, m, 0);
        let a = Z3_mk_app(c, d, 0, ptr::null());
        assert_ne!(a, 0, "{:?}", Z3_get_error_code(c));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}

#[test]
fn a_selector_of_a_constructor_value_evaluates() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let int = Z3_mk_int_sort(c);
        // L = nil | cons(hd: Int, tl: L), built as z3py's Datatype does.
        let fnames = [
            Z3_mk_string_symbol(c, c"hd".as_ptr()),
            Z3_mk_string_symbol(c, c"tl".as_ptr()),
        ];
        let fsorts = [int, ptr::null_mut()];
        let frefs = [0u32, 0u32];
        let cons = Z3_mk_constructor(
            c,
            Z3_mk_string_symbol(c, c"cons".as_ptr()),
            Z3_mk_string_symbol(c, c"is-cons".as_ptr()),
            2,
            fnames.as_ptr(),
            fsorts.as_ptr(),
            frefs.as_ptr(),
        );
        let nil = Z3_mk_constructor(
            c,
            Z3_mk_string_symbol(c, c"nil".as_ptr()),
            Z3_mk_string_symbol(c, c"is-nil".as_ptr()),
            0,
            ptr::null(),
            ptr::null(),
            ptr::null(),
        );
        let mut ctors = [nil, cons];
        let list = Z3_mk_datatype(
            c,
            Z3_mk_string_symbol(c, c"L".as_ptr()),
            2,
            ctors.as_mut_ptr(),
        );
        assert!(!list.is_null());
        let mut cons_decl: Z3_func_decl = ptr::null_mut();
        let mut is_cons: Z3_func_decl = ptr::null_mut();
        let mut accessors: [Z3_func_decl; 2] = [ptr::null_mut(); 2];
        Z3_query_constructor(
            c,
            cons,
            2,
            &raw mut cons_decl,
            &raw mut is_cons,
            accessors.as_mut_ptr(),
        );
        let l = named_const(c, "l", list);
        let hd_l = Z3_mk_app(c, accessors[0], 1, [l].as_ptr());
        let goal = Z3_mk_eq(c, hd_l, Z3_mk_int(c, 3, int));
        let tested = Z3_mk_app(c, is_cons, 1, [l].as_ptr());
        // z3: sat [l = cons(3, nil)]. AY's evaluator left `hd(cons(3, nil))`
        // unreduced, so the published model could not be confirmed.
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, goal);
        Z3_solver_assert(c, s, tested);
        assert_eq!(sat_only_with_valid_model(c, s, &[goal, tested]), Z3_L_TRUE);
        Z3_del_context(c);
    }
}

#[test]
fn a_rejected_scoped_parse_is_z3s_parser_error_and_leaves_the_context_usable() {
    // SAFETY: every handle below belongs to the live context `c`.
    unsafe {
        let c = mk_ctx();
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_true(c));
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        // The last assertion has sort Int: z3 reports Z3_PARSER_ERROR, adds
        // nothing, and the context stays usable.
        Z3_solver_from_string(
            c,
            s,
            c"(declare-const y Int)(assert (= y 0))(assert 1)".as_ptr(),
        );
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        let v = Z3_solver_get_assertions(c, s);
        assert_eq!(Z3_ast_vector_size(c, v), 1, "nothing of the text was added");
        assert_eq!(Z3_solver_check(c, s), Z3_L_TRUE);
        Z3_solver_assert(c, s, Z3_mk_false(c));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        // Re-reading another solver's model is unaffected by a parse.
        let int = Z3_mk_int_sort(c);
        let x = named_const(c, "x", int);
        let t = Z3_mk_solver(c);
        let eq = Z3_mk_eq(c, x, Z3_mk_int(c, 7, int));
        Z3_solver_assert(c, t, eq);
        assert_eq!(Z3_solver_check(c, t), Z3_L_TRUE);
        let u = Z3_mk_solver(c);
        Z3_solver_from_string(c, u, c"(declare-const z Int)(assert (> z 0))".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let m = Z3_solver_get_model(c, t);
        assert!(!m.is_null(), "another solver's parse kept this model");
        assert!(evaluates_true(c, m, eq));
        // A solver's second declaration of the same name and signature is
        // z3's error (its command context keeps the first).
        Z3_solver_from_string(c, u, c"(declare-const z Int)".as_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        Z3_del_context(c);
    }
}
