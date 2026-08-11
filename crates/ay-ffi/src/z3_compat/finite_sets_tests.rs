// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::ffi::{CStr, CString};
use std::ptr;

use super::*;

unsafe fn context() -> Z3_context {
    // SAFETY: test owns the configuration and returned context.
    unsafe {
        let config = Z3_mk_config();
        let ctx = Z3_mk_context(config);
        Z3_del_config(config);
        ctx
    }
}

unsafe fn ast_text(ctx: Z3_context, ast: Z3_ast) -> String {
    // SAFETY: the AST belongs to the live test context.
    unsafe {
        CStr::from_ptr(Z3_ast_to_string(ctx, ast))
            .to_string_lossy()
            .into_owned()
    }
}

unsafe fn sort_text(ctx: Z3_context, sort: Z3_sort) -> String {
    // SAFETY: the sort belongs to the live test context.
    unsafe {
        CStr::from_ptr(Z3_sort_to_string(ctx, sort))
            .to_string_lossy()
            .into_owned()
    }
}

unsafe fn decl_name(ctx: Z3_context, ast: Z3_ast) -> String {
    // SAFETY: the application and declaration belong to the live test context.
    unsafe {
        let decl = Z3_get_app_decl(ctx, ast);
        let symbol = Z3_get_decl_name(ctx, decl);
        CStr::from_ptr(Z3_get_symbol_string(ctx, symbol))
            .to_string_lossy()
            .into_owned()
    }
}

unsafe fn prove(ctx: Z3_context, formula: Z3_ast) {
    // SAFETY: all handles belong to the live test context.
    unsafe {
        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, formula));
        assert_eq!(Z3_solver_check(ctx, solver), Z3_L_FALSE);
    }
}

#[test]
fn finite_set_z3_500_constants_and_all_fourteen_entry_points() {
    assert_eq!(Z3_OP_FINITE_SET_EMPTY, 49152);
    assert_eq!(Z3_OP_FINITE_SET_SINGLETON, 49153);
    assert_eq!(Z3_OP_FINITE_SET_UNION, 49154);
    assert_eq!(Z3_OP_FINITE_SET_INTERSECT, 49155);
    assert_eq!(Z3_OP_FINITE_SET_DIFFERENCE, 49156);
    assert_eq!(Z3_OP_FINITE_SET_IN, 49157);
    assert_eq!(Z3_OP_FINITE_SET_SIZE, 49158);
    assert_eq!(Z3_OP_FINITE_SET_SUBSET, 49159);
    assert_eq!(Z3_OP_FINITE_SET_MAP, 49160);
    assert_eq!(Z3_OP_FINITE_SET_FILTER, 49161);
    assert_eq!(Z3_OP_FINITE_SET_RANGE, 49162);
    assert_eq!(Z3_OP_FINITE_SET_EXT, 49163);
    assert_eq!(Z3_OP_FINITE_SET_MAP_INVERSE, 49164);
    assert_eq!(Z3_OP_INTERNAL, 49165);
    assert_eq!(Z3_OP_RECURSIVE, 49166);
    assert_eq!(Z3_OP_UNINTERPRETED, 49167);

    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        assert!(Z3_is_finite_set_sort(ctx, finite_int));
        assert_eq!(
            sort_text(ctx, Z3_get_finite_set_sort_basis(ctx, finite_int)),
            "Int"
        );
        assert_eq!(sort_text(ctx, finite_int), "(FiniteSet Int)");
        assert_eq!(Z3_get_sort_kind(ctx, finite_int), Z3_UNKNOWN_SORT);

        let one = Z3_mk_int(ctx, 1, int);
        let three = Z3_mk_int(ctx, 3, int);
        let seven = Z3_mk_int(ctx, 7, int);
        let empty = Z3_mk_finite_set_empty(ctx, finite_int);
        let singleton = Z3_mk_finite_set_singleton(ctx, one);
        let union = Z3_mk_finite_set_union(ctx, singleton, empty);
        let intersect = Z3_mk_finite_set_intersect(ctx, singleton, empty);
        let difference = Z3_mk_finite_set_difference(ctx, singleton, empty);
        let member = Z3_mk_finite_set_member(ctx, one, singleton);
        let size = Z3_mk_finite_set_size(ctx, singleton);
        let subset = Z3_mk_finite_set_subset(ctx, empty, singleton);
        let constant_function = Z3_mk_const_array(ctx, int, seven);
        let mapped = Z3_mk_finite_set_map(ctx, constant_function, singleton);
        let true_ast = Z3_mk_true(ctx);
        let predicate = Z3_mk_const_array(ctx, int, true_ast);
        let filtered = Z3_mk_finite_set_filter(ctx, predicate, singleton);
        let range = Z3_mk_finite_set_range(ctx, one, three);

        let apps = [
            (empty, "set.empty", 49152, 0),
            (singleton, "set.singleton", 49153, 1),
            (union, "set.union", 49154, 2),
            (intersect, "set.intersect", 49155, 2),
            (difference, "set.difference", 49156, 2),
            (member, "set.in", 49157, 2),
            (size, "set.size", 49158, 1),
            (subset, "set.subset", 49159, 2),
            (mapped, "set.map", 49160, 2),
            (filtered, "set.filter", 49161, 2),
            (range, "set.range", 49162, 2),
        ];
        for (app, name, kind, arity) in apps {
            assert_ne!(app, 0);
            assert_eq!(decl_name(ctx, app), name);
            let decl = Z3_get_app_decl(ctx, app);
            assert_eq!(Z3_get_decl_kind(ctx, decl), kind);
            assert_eq!(Z3_get_app_num_args(ctx, app), arity);
        }

        assert_eq!(ast_text(ctx, empty), "(as set.empty (FiniteSet Int))");
        assert_eq!(ast_text(ctx, singleton), "(set.singleton 1)");
        assert_eq!(ast_text(ctx, range), "(set.range 1 3)");

        let empty_decl = Z3_get_app_decl(ctx, empty);
        assert_eq!(Z3_get_decl_num_parameters(ctx, empty_decl), 1);
        assert_eq!(
            Z3_get_decl_parameter_kind(ctx, empty_decl, 0),
            Z3_PARAMETER_SORT
        );
        let parameter = Z3_get_decl_sort_parameter(ctx, empty_decl, 0);
        assert!(Z3_is_eq_sort(ctx, parameter, finite_int));

        let colliding_name = CString::new("set.singleton").expect("literal has no NUL");
        let colliding_user_decl = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, colliding_name.as_ptr()),
            1,
            [int].as_ptr(),
            int,
        );
        assert!(!colliding_user_decl.is_null());
        assert_eq!(
            Z3_get_decl_kind(ctx, colliding_user_decl),
            Z3_OP_UNINTERPRETED,
            "a same-name user UF must not inherit FiniteSet builtin provenance"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn finite_set_nested_rendering_and_legacy_array_isolation() {
    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        let nested = Z3_mk_finite_set_sort(ctx, finite_int);
        assert_eq!(sort_text(ctx, nested), "(FiniteSet (FiniteSet Int))");

        let empty = Z3_mk_finite_set_empty(ctx, finite_int);
        let nested_singleton = Z3_mk_finite_set_singleton(ctx, empty);
        assert_eq!(
            ast_text(ctx, nested_singleton),
            "(set.singleton (as set.empty (FiniteSet Int)))"
        );

        let array_nested = Z3_mk_array_sort(ctx, nested, finite_int);
        assert_eq!(
            sort_text(ctx, array_nested),
            "(Array (FiniteSet (FiniteSet Int)) (FiniteSet Int))"
        );

        let p_name = CString::new("p").expect("literal has no NUL");
        let p_symbol = Z3_mk_string_symbol(ctx, p_name.as_ptr());
        let p = Z3_mk_const(ctx, p_symbol, Z3_mk_bool_sort(ctx));
        let one = Z3_mk_int(ctx, 1, int);
        let singleton = Z3_mk_finite_set_singleton(ctx, one);
        let composed = Z3_mk_ite(ctx, p, singleton, empty);
        let composed_text = ast_text(ctx, composed);
        assert!(composed_text.contains("(set.singleton 1)"));
        assert!(composed_text.contains("(as set.empty (FiniteSet Int))"));
        assert!(!composed_text.contains("finite_set_app"));
        let composed_decl = Z3_get_app_decl(ctx, composed);
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, composed_decl, 1)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, composed_decl, 2)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(ctx, Z3_get_range(ctx, composed_decl)),
            "(FiniteSet Int)"
        );

        let finite_equality = Z3_mk_eq(ctx, singleton, empty);
        let equality_decl = Z3_get_app_decl(ctx, finite_equality);
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, equality_decl, 0)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, equality_decl, 1)),
            "(FiniteSet Int)"
        );

        let finite_value_array = Z3_mk_const_array(ctx, int, empty);
        let array_decl = Z3_get_app_decl(ctx, finite_value_array);
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, array_decl, 0)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(ctx, Z3_get_range(ctx, array_decl)),
            "(Array Int (FiniteSet Int))"
        );

        let legacy_empty = Z3_mk_empty_set(ctx, int);
        assert_eq!(Z3_mk_eq(ctx, empty, legacy_empty), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);
        assert_eq!(Z3_mk_select(ctx, empty, one), 0);
        assert_eq!(Z3_mk_store(ctx, empty, one, Z3_mk_true(ctx)), 0);
        assert_eq!(Z3_mk_set_member(ctx, one, empty), 0);
        assert_eq!(Z3_mk_finite_set_member(ctx, one, legacy_empty), 0);
        assert_eq!(Z3_mk_array_default(ctx, empty), 0);
        assert_eq!(Z3_mk_array_ext(ctx, empty, empty), 0);
        assert_eq!(Z3_mk_array_ext(ctx, empty, legacy_empty), 0);
        let one_index = [one];
        assert_eq!(Z3_mk_select_n(ctx, empty, 1, one_index.as_ptr()), 0);
        assert_eq!(
            Z3_mk_store_n(ctx, empty, 1, one_index.as_ptr(), Z3_mk_true(ctx)),
            0
        );
        let mixed = [empty, legacy_empty];
        assert_eq!(Z3_mk_distinct(ctx, 2, mixed.as_ptr()), 0);
        assert_eq!(Z3_mk_ite(ctx, p, empty, legacy_empty), 0);

        // A genuine Array indexed by FiniteSet remains supported and lowers
        // its domain recursively; it is not confused with a FiniteSet value.
        let constant = Z3_mk_const_array(ctx, finite_int, one);
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, constant)),
            "(Array (FiniteSet Int) Int)"
        );
        assert_ne!(Z3_mk_select(ctx, constant, empty), 0);
        assert_ne!(Z3_mk_select_n(ctx, constant, 1, [empty].as_ptr()), 0);
        assert_ne!(Z3_mk_store_n(ctx, constant, 1, [empty].as_ptr(), one), 0);
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, Z3_mk_array_default(ctx, constant))),
            "Int"
        );
        assert_eq!(
            sort_text(
                ctx,
                Z3_get_sort(ctx, Z3_mk_array_ext(ctx, constant, constant))
            ),
            "(FiniteSet Int)"
        );

        assert_eq!(
            sort_text(
                ctx,
                Z3_get_sort(ctx, Z3_mk_array_default(ctx, finite_value_array))
            ),
            "(FiniteSet Int)"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn finite_set_public_function_and_lambda_signatures_round_trip() {
    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        let nested = Z3_mk_finite_set_sort(ctx, finite_int);
        let empty = Z3_mk_finite_set_empty(ctx, finite_int);
        let nested_source = Z3_mk_finite_set_singleton(ctx, empty);

        let f_name = CString::new("finite_identity").expect("literal has no NUL");
        let f_domain = [finite_int];
        let f = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, f_name.as_ptr()),
            1,
            f_domain.as_ptr(),
            finite_int,
        );
        let function_array = Z3_mk_as_array(ctx, f);
        let function_array_sort = Z3_get_sort(ctx, function_array);
        assert_eq!(
            sort_text(ctx, function_array_sort),
            "(Array (FiniteSet Int) (FiniteSet Int))"
        );
        assert!(Z3_is_eq_sort(
            ctx,
            Z3_get_array_sort_domain(ctx, function_array_sort),
            finite_int
        ));
        assert!(Z3_is_eq_sort(
            ctx,
            Z3_get_array_sort_range(ctx, function_array_sort),
            finite_int
        ));
        let mapped_function = Z3_mk_finite_set_map(ctx, function_array, nested_source);
        assert_ne!(mapped_function, 0);
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, mapped_function)),
            "(FiniteSet (FiniteSet Int))"
        );

        let x_name = CString::new("x").expect("literal has no NUL");
        let x_symbol = Z3_mk_string_symbol(ctx, x_name.as_ptr());
        let predicate_name = CString::new("finite_predicate").expect("literal has no NUL");
        let predicate_decl = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, predicate_name.as_ptr()),
            1,
            f_domain.as_ptr(),
            Z3_mk_bool_sort(ctx),
        );
        let predicate_array = Z3_mk_as_array(ctx, predicate_decl);
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, predicate_array)),
            "(Array (FiniteSet Int) Bool)"
        );
        assert_ne!(
            Z3_mk_finite_set_filter(ctx, predicate_array, nested_source),
            0
        );

        let bound = Z3_mk_bound(ctx, 0, finite_int);
        let bound_sorts = [finite_int];
        let bound_names = [x_symbol];
        let lambda = Z3_mk_lambda(ctx, 1, bound_sorts.as_ptr(), bound_names.as_ptr(), bound);
        let lambda_sort = Z3_get_sort(ctx, lambda);
        assert_eq!(
            sort_text(ctx, lambda_sort),
            "(Array (FiniteSet Int) (FiniteSet Int))"
        );
        assert!(Z3_is_eq_sort(
            ctx,
            Z3_get_array_sort_domain(ctx, lambda_sort),
            finite_int
        ));
        assert!(Z3_is_eq_sort(
            ctx,
            Z3_get_array_sort_range(ctx, lambda_sort),
            finite_int
        ));
        let mapped_lambda = Z3_mk_finite_set_map(ctx, lambda, nested_source);
        assert_ne!(mapped_lambda, 0);
        assert!(Z3_is_eq_sort(ctx, Z3_get_sort(ctx, mapped_lambda), nested));

        let bound_const_name = CString::new("bound_set").expect("literal has no NUL");
        let bound_const = Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, bound_const_name.as_ptr()),
            finite_int,
        );
        let lambda_const = Z3_mk_lambda_const(ctx, 1, [bound_const].as_ptr(), bound_const);
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, lambda_const)),
            "(Array (FiniteSet Int) (FiniteSet Int))"
        );

        let predicate = Z3_mk_lambda(
            ctx,
            1,
            bound_sorts.as_ptr(),
            bound_names.as_ptr(),
            Z3_mk_true(ctx),
        );
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, predicate)),
            "(Array (FiniteSet Int) Bool)"
        );
        assert_ne!(Z3_mk_finite_set_filter(ctx, predicate, nested_source), 0);

        Z3_del_context(ctx);
    }
}

#[test]
fn finite_set_smtlib_parse_preserves_surface_and_fail_closed_gates() {
    // SAFETY: every handle is created in and retained by its test context.
    unsafe {
        let ctx = context();
        let script = CString::new(
            "(declare-const parsed_s (FiniteSet Int)) \
             (assert (= parsed_s (as set.empty (FiniteSet Int))))",
        )
        .expect("literal has no NUL");
        let parsed = Z3_parse_smtlib2_string(
            ctx,
            script.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(ctx), Z3_OK);
        assert_eq!(Z3_ast_vector_size(ctx, parsed), 1);
        let assertion = Z3_ast_vector_get(ctx, parsed, 0);
        assert_eq!(
            ast_text(ctx, assertion),
            "(= parsed_s (as set.empty (FiniteSet Int)))"
        );
        let parsed_empty = Z3_get_app_arg(ctx, assertion, 1);
        assert_eq!(
            sort_text(ctx, Z3_get_sort(ctx, parsed_empty)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, parsed_empty)),
            Z3_OP_FINITE_SET_EMPTY
        );
        let parsed_equality_decl = Z3_get_app_decl(ctx, assertion);
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, parsed_equality_decl, 0)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(ctx, Z3_get_domain(ctx, parsed_equality_decl, 1)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(ctx, Z3_get_range(ctx, parsed_equality_decl)),
            "Bool"
        );

        let sat_solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, sat_solver, assertion);
        assert_eq!(Z3_solver_check(ctx, sat_solver), Z3_L_UNDEF);

        // An arbitrary parsed FiniteSet value only invalidates SAT; a direct
        // contradiction remains a sound UNSAT.
        let unsat_solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, unsat_solver, Z3_mk_false(ctx));
        assert_eq!(Z3_solver_check(ctx, unsat_solver), Z3_L_FALSE);
        Z3_del_context(ctx);

        let mixed_ctx = context();
        let mixed_script = CString::new(
            "(declare-const parsed_fs (FiniteSet Int)) \
             (declare-const parsed_legacy (Set Int)) \
             (assert (= parsed_fs (as set.empty (FiniteSet Int)))) \
             (assert (= parsed_legacy ((as const (Array Int Bool)) false)))",
        )
        .expect("literal has no NUL");
        let mixed = Z3_parse_smtlib2_string(
            mixed_ctx,
            mixed_script.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(mixed_ctx), Z3_OK);
        assert_eq!(Z3_ast_vector_size(mixed_ctx, mixed), 2);
        let finite_empty = Z3_get_app_arg(mixed_ctx, Z3_ast_vector_get(mixed_ctx, mixed, 0), 1);
        let legacy_empty = Z3_get_app_arg(mixed_ctx, Z3_ast_vector_get(mixed_ctx, mixed, 1), 1);
        assert_ne!(
            finite_empty, legacy_empty,
            "public FiniteSet and legacy Set occurrences need distinct handles"
        );
        assert_eq!(
            sort_text(mixed_ctx, Z3_get_sort(mixed_ctx, finite_empty)),
            "(FiniteSet Int)"
        );
        assert_eq!(
            sort_text(mixed_ctx, Z3_get_sort(mixed_ctx, legacy_empty)),
            "(Array Int Bool)"
        );
        assert_eq!(
            Z3_get_decl_kind(mixed_ctx, Z3_get_app_decl(mixed_ctx, finite_empty)),
            Z3_OP_FINITE_SET_EMPTY
        );
        assert_ne!(
            Z3_get_decl_kind(mixed_ctx, Z3_get_app_decl(mixed_ctx, legacy_empty)),
            Z3_OP_FINITE_SET_EMPTY
        );
        Z3_del_context(mixed_ctx);

        let quantified_ctx = context();
        let quantified_script =
            CString::new("(assert (forall ((parsed_bound (FiniteSet Int))) true))")
                .expect("literal has no NUL");
        let quantified = Z3_parse_smtlib2_string(
            quantified_ctx,
            quantified_script.as_ptr(),
            0,
            ptr::null(),
            ptr::null(),
            0,
            ptr::null(),
            ptr::null(),
        );
        assert_eq!(Z3_get_error_code(quantified_ctx), Z3_OK);
        assert_eq!(Z3_ast_vector_size(quantified_ctx, quantified), 1);
        let solver = Z3_mk_solver(quantified_ctx);
        Z3_solver_assert(quantified_ctx, solver, Z3_mk_false(quantified_ctx));
        assert_eq!(Z3_solver_check(quantified_ctx, solver), Z3_L_FALSE);
        let relevant_solver = Z3_mk_solver(quantified_ctx);
        Z3_solver_assert(
            quantified_ctx,
            relevant_solver,
            Z3_ast_vector_get(quantified_ctx, quantified, 0),
        );
        assert_eq!(Z3_solver_check(quantified_ctx, relevant_solver), Z3_L_UNDEF);
        Z3_del_context(quantified_ctx);
    }
}

#[test]
fn finite_set_solver_from_string_reaches_parsed_gate_provenance() {
    // SAFETY: every handle is created in and retained by its test context.
    unsafe {
        let arbitrary_sat_ctx = context();
        let arbitrary_sat_solver = Z3_mk_solver(arbitrary_sat_ctx);
        let arbitrary_sat_script = CString::new(
            "(declare-const parsed_s (FiniteSet Int)) \
             (assert (= parsed_s (as set.empty (FiniteSet Int))))",
        )
        .expect("literal has no NUL");
        Z3_solver_from_string(
            arbitrary_sat_ctx,
            arbitrary_sat_solver,
            arbitrary_sat_script.as_ptr(),
        );
        assert_eq!(
            Z3_solver_check(arbitrary_sat_ctx, arbitrary_sat_solver),
            Z3_L_UNDEF,
            "arbitrary parsed FiniteSet provenance must be reachable from installed assertions"
        );
        Z3_del_context(arbitrary_sat_ctx);

        let arbitrary_ctx = context();
        let arbitrary_solver = Z3_mk_solver(arbitrary_ctx);
        let arbitrary_script = CString::new(
            "(declare-const parsed_s (FiniteSet Int)) \
             (assert (= parsed_s (as set.empty (FiniteSet Int)))) \
             (assert false)",
        )
        .expect("literal has no NUL");
        Z3_solver_from_string(arbitrary_ctx, arbitrary_solver, arbitrary_script.as_ptr());
        assert_eq!(
            Z3_solver_check(arbitrary_ctx, arbitrary_solver),
            Z3_L_FALSE,
            "arbitrary parsed FiniteSet provenance must preserve UNSAT polarity"
        );
        Z3_del_context(arbitrary_ctx);

        let binder_ctx = context();
        let binder_solver = Z3_mk_solver(binder_ctx);
        let binder_script = CString::new(
            "(assert (forall ((parsed_bound (FiniteSet Int))) true)) \
             (assert false)",
        )
        .expect("literal has no NUL");
        Z3_solver_from_string(binder_ctx, binder_solver, binder_script.as_ptr());
        assert_eq!(
            Z3_solver_check(binder_ctx, binder_solver),
            Z3_L_UNDEF,
            "parsed FiniteSet binder provenance must gate both polarities"
        );
        Z3_del_context(binder_ctx);
    }
}

#[test]
fn finite_set_ground_cardinality_and_range_laws() {
    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        let zero = Z3_mk_int(ctx, 0, int);
        let one = Z3_mk_int(ctx, 1, int);
        let three = Z3_mk_int(ctx, 3, int);
        let four = Z3_mk_int(ctx, 4, int);
        let seven = Z3_mk_int(ctx, 7, int);
        let eight = Z3_mk_int(ctx, 8, int);

        let empty = Z3_mk_finite_set_empty(ctx, finite_int);
        prove(ctx, Z3_mk_eq(ctx, Z3_mk_finite_set_size(ctx, empty), zero));

        let singleton = Z3_mk_finite_set_singleton(ctx, one);
        prove(
            ctx,
            Z3_mk_eq(ctx, Z3_mk_finite_set_size(ctx, singleton), one),
        );
        prove(ctx, Z3_mk_finite_set_member(ctx, one, singleton));
        prove(
            ctx,
            Z3_mk_eq(
                ctx,
                Z3_mk_finite_set_difference(ctx, singleton, empty),
                singleton,
            ),
        );
        prove(ctx, Z3_mk_finite_set_subset(ctx, empty, singleton));
        prove(
            ctx,
            Z3_mk_not(ctx, Z3_mk_finite_set_subset(ctx, singleton, empty)),
        );

        let range = Z3_mk_finite_set_range(ctx, one, three);
        prove(ctx, Z3_mk_eq(ctx, Z3_mk_finite_set_size(ctx, range), three));
        prove(ctx, Z3_mk_finite_set_member(ctx, one, range));
        prove(ctx, Z3_mk_finite_set_member(ctx, three, range));
        prove(
            ctx,
            Z3_mk_not(ctx, Z3_mk_finite_set_member(ctx, four, range)),
        );

        let constant_seven = Z3_mk_const_array(ctx, int, seven);
        let mapped = Z3_mk_finite_set_map(ctx, constant_seven, singleton);
        prove(ctx, Z3_mk_finite_set_member(ctx, seven, mapped));
        prove(
            ctx,
            Z3_mk_not(ctx, Z3_mk_finite_set_member(ctx, eight, mapped)),
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn finite_set_decision_gates_follow_each_solver_goal_and_scope() {
    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        let name = CString::new("arbitrary").expect("literal has no NUL");
        let arbitrary = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name.as_ptr()), finite_int);
        let empty = Z3_mk_finite_set_empty(ctx, finite_int);
        let uses_arbitrary = Z3_mk_eq(ctx, arbitrary, empty);

        // Merely constructing an arbitrary FiniteSet AST cannot infect a
        // solver handle that does not reach it.
        let scoped = Z3_mk_solver(ctx);
        assert_eq!(Z3_solver_check(ctx, scoped), Z3_L_TRUE);
        assert_eq!(
            Z3_solver_check_assumptions(ctx, scoped, 1, [uses_arbitrary].as_ptr()),
            Z3_L_UNDEF
        );
        assert_eq!(Z3_solver_check(ctx, scoped), Z3_L_TRUE);

        Z3_solver_push(ctx, scoped);
        Z3_solver_assert(ctx, scoped, uses_arbitrary);
        assert_eq!(Z3_solver_check(ctx, scoped), Z3_L_UNDEF);
        Z3_solver_pop(ctx, scoped, 1);
        assert_eq!(Z3_solver_check(ctx, scoped), Z3_L_TRUE);

        Z3_solver_assert(ctx, scoped, uses_arbitrary);
        assert_eq!(Z3_solver_check(ctx, scoped), Z3_L_UNDEF);
        Z3_solver_reset(ctx, scoped);
        assert_eq!(Z3_solver_check(ctx, scoped), Z3_L_TRUE);

        // A sibling solver remains independent and can still prove a direct
        // contradiction while the first handle reaches an arbitrary carrier.
        let sibling = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, sibling, Z3_mk_false(ctx));
        assert_eq!(Z3_solver_check(ctx, sibling), Z3_L_FALSE);
        let arbitrary_unsat = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, arbitrary_unsat, uses_arbitrary);
        Z3_solver_assert(ctx, arbitrary_unsat, Z3_mk_false(ctx));
        assert_eq!(
            Z3_solver_check(ctx, arbitrary_unsat),
            Z3_L_FALSE,
            "arbitrary FiniteSet is a SAT-only gate; UNSAT must be preserved"
        );

        let nested = Z3_mk_finite_set_sort(ctx, finite_int);
        let source = Z3_mk_finite_set_empty(ctx, nested);
        let function_sort = Z3_mk_array_sort(ctx, finite_int, int);
        let function_name = CString::new("f").expect("literal has no NUL");
        let function = Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, function_name.as_ptr()),
            function_sort,
        );
        let nested_map = Z3_mk_finite_set_map(ctx, function, source);
        assert_ne!(nested_map, 0);

        // The quantified backing of a nested map is likewise local: unused it
        // cannot demote the sibling contradiction, but once its result is
        // asserted through a Boolean use the fail-closed gate applies.
        assert_eq!(Z3_solver_check(ctx, sibling), Z3_L_FALSE);
        let relevant = Z3_mk_finite_set_subset(ctx, nested_map, nested_map);
        let quantified = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, quantified, relevant);
        assert_eq!(Z3_solver_check(ctx, quantified), Z3_L_UNDEF);

        // `set.map` also binds its image variable in the result lambda. A
        // FiniteSet image therefore needs the same two-sided quantifier gate
        // even when the source/domain itself is plain Int.
        let one = Z3_mk_int(ctx, 1, int);
        let int_source = Z3_mk_finite_set_singleton(ctx, one);
        let finite_image_function = Z3_mk_const_array(ctx, int, empty);
        let finite_image_map = Z3_mk_finite_set_map(ctx, finite_image_function, int_source);
        let nested_empty = Z3_mk_finite_set_empty(ctx, nested);
        let image_formula = Z3_mk_eq(ctx, finite_image_map, nested_empty);
        let image_solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, image_solver, image_formula);
        assert_eq!(Z3_solver_check(ctx, image_solver), Z3_L_UNDEF);

        let bound_name = CString::new("bound").expect("literal has no NUL");
        let bound = Z3_mk_const(
            ctx,
            Z3_mk_string_symbol(ctx, bound_name.as_ptr()),
            finite_int,
        );
        let forall =
            Z3_mk_forall_const(ctx, 0, 1, [bound].as_ptr(), 0, ptr::null(), Z3_mk_true(ctx));
        assert_eq!(
            sort_text(ctx, Z3_get_quantifier_bound_sort(ctx, forall, 0)),
            "(FiniteSet Int)"
        );
        let unused_quantifier = Z3_mk_solver(ctx);
        assert_eq!(Z3_solver_check(ctx, unused_quantifier), Z3_L_TRUE);
        Z3_solver_assert(ctx, unused_quantifier, forall);
        assert_eq!(Z3_solver_check(ctx, unused_quantifier), Z3_L_UNDEF);
        Z3_solver_assert(ctx, unused_quantifier, Z3_mk_false(ctx));
        assert_eq!(
            Z3_solver_check(ctx, unused_quantifier),
            Z3_L_UNDEF,
            "FiniteSet binders invalidate both SAT and UNSAT polarity"
        );

        Z3_del_context(ctx);
    }
}

#[test]
fn finite_set_optimize_gate_follows_live_objectives_and_constraints() {
    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        let name = CString::new("opt_arbitrary").expect("literal has no NUL");
        let arbitrary = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name.as_ptr()), finite_int);
        let empty = Z3_mk_finite_set_empty(ctx, finite_int);
        let relevant = Z3_mk_eq(ctx, arbitrary, empty);

        let optimize = Z3_mk_optimize(ctx);
        assert_eq!(Z3_optimize_check(ctx, optimize, 0, ptr::null()), Z3_L_TRUE);
        Z3_optimize_push(ctx, optimize);
        Z3_optimize_assert(ctx, optimize, relevant);
        assert_eq!(Z3_optimize_check(ctx, optimize, 0, ptr::null()), Z3_L_UNDEF);
        Z3_optimize_pop(ctx, optimize);
        assert_eq!(Z3_optimize_check(ctx, optimize, 0, ptr::null()), Z3_L_TRUE);

        Z3_del_context(ctx);
    }
}

#[test]
fn finite_set_public_signature_rejects_legacy_array_argument_to_mk_app() {
    // SAFETY: every handle is created in and retained by this test's context.
    unsafe {
        let ctx = context();
        let int = Z3_mk_int_sort(ctx);
        let finite_int = Z3_mk_finite_set_sort(ctx, int);
        let name = CString::new("takes_finite").expect("literal has no NUL");
        let domain = [finite_int];
        let decl = Z3_mk_func_decl(
            ctx,
            Z3_mk_string_symbol(ctx, name.as_ptr()),
            1,
            domain.as_ptr(),
            int,
        );
        let legacy = Z3_mk_empty_set(ctx, int);
        assert_eq!(Z3_mk_app(ctx, decl, 1, &raw const legacy), 0);
        assert_eq!(Z3_get_error_code(ctx), Z3_SORT_ERROR);
        Z3_del_context(ctx);
    }
}
