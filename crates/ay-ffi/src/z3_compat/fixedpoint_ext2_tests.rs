// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Track B batch 3b: fixedpoint (CHC) + model-construction C-API.

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
fn model_const_interp_roundtrip() {
    // SAFETY: the test owns its context and keeps all derived handles alive
    // until the final context destruction.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // A user-built model with an explicit interpretation for a 0-ary decl.
        let m = Z3_mk_model(c);
        assert!(!m.is_null());
        let f = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"k".as_ptr()),
            0,
            ptr::null(),
            int,
        );
        let seven = Z3_mk_int(c, 7, int);
        assert!(!Z3_model_has_interp(c, m, f));
        assert_eq!(Z3_model_get_num_consts(c, m), 0);
        Z3_add_const_interp(c, m, f, seven);
        assert_eq!(Z3_model_get_num_consts(c, m), 1);
        let listed = Z3_model_get_const_decl(c, m, 0);
        assert!(!listed.is_null());
        assert!(Z3_is_eq_func_decl(c, listed, f));
        assert_eq!(Z3_model_get_const_interp(c, m, listed), seven);
        // Read it back.
        let got = Z3_model_get_const_interp(c, m, f);
        assert_eq!(
            got, seven,
            "const interp must read back the value it was given"
        );
        assert!(Z3_model_has_interp(c, m, f));
        let eleven = Z3_mk_int(c, 11, int);
        Z3_add_const_interp(c, m, f, eleven);
        assert_eq!(Z3_model_get_num_consts(c, m), 1);
        assert_eq!(Z3_model_get_const_interp(c, m, f), eleven);
        assert!(Z3_model_has_interp(c, m, f));
        Z3_add_const_interp(c, m, listed, seven);
        assert_eq!(Z3_model_get_const_interp(c, m, f), seven);
        assert_eq!(Z3_model_get_num_consts(c, m), 1);
        Z3_del_context(c);
    }
}

#[test]
fn model_const_interp_rejects_function_declarations_without_changing_the_model() {
    // SAFETY: this test owns the context and keeps all supplied model,
    // declaration, interpretation and value handles live until destruction.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let model = Z3_mk_model(c);
        let function = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"not_a_constant".as_ptr()),
            1,
            &int,
            int,
        );
        let seven = Z3_mk_int(c, 7, int);
        Z3_add_const_interp(c, model, function, seven);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert!(!Z3_model_has_interp(c, model, function));
        assert!((*model).user_const_interps.is_empty());

        let interpretation = Z3_add_func_interp(c, model, function, seven);
        assert!(!interpretation.is_null());
        let eleven = Z3_mk_int(c, 11, int);
        Z3_add_const_interp(c, model, function, eleven);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_model_get_func_interp(c, model, function), interpretation);
        assert_eq!(Z3_func_interp_get_else(c, interpretation), seven);
        assert!((*model).user_const_interps.is_empty());

        Z3_add_const_interp(c, model, ptr::null_mut(), seven);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_func_interp_get_else(c, interpretation), seven);
        Z3_del_context(c);
    }
}

#[test]
fn model_function_interp_reassignment_replaces_the_current_graph() {
    // SAFETY: the context and all its model/declaration/value handles are
    // exclusively owned here and remain live until context destruction.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let model = Z3_mk_model(c);
        let function = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"model_function".as_ptr()),
            1,
            &int,
            int,
        );
        assert!(!function.is_null());
        assert!(!Z3_model_has_interp(c, model, function));
        assert_eq!(Z3_model_get_num_funcs(c, model), 0);
        let seven = Z3_mk_int(c, 7, int);
        let first = Z3_add_func_interp(c, model, function, seven);
        assert!(!first.is_null());
        assert_eq!(Z3_model_get_num_funcs(c, model), 1);
        let listed = Z3_model_get_func_decl(c, model, 0);
        assert!(!listed.is_null());
        assert!(Z3_is_eq_func_decl(c, listed, function));
        assert_eq!(Z3_model_get_func_interp(c, model, listed), first);
        let arguments = Z3_mk_ast_vector(c);
        Z3_ast_vector_push(c, arguments, Z3_mk_int(c, 1, int));
        Z3_func_interp_add_entry(c, first, arguments, Z3_mk_int(c, 42, int));
        assert_eq!(Z3_func_interp_get_num_entries(c, first), 1);
        let initial = Z3_model_get_func_interp(c, model, function);
        assert!(!initial.is_null());
        assert_eq!(Z3_func_interp_get_else(c, initial), seven);
        assert_eq!(Z3_func_interp_get_else(c, first), seven);
        assert!(Z3_model_has_interp(c, model, function));

        let eleven = Z3_mk_int(c, 11, int);
        let replacement = Z3_add_func_interp(c, model, function, eleven);
        assert!(!replacement.is_null());
        assert_eq!(Z3_model_get_num_funcs(c, model), 1);
        let current = Z3_model_get_func_interp(c, model, function);
        assert!(!current.is_null());
        assert_eq!(Z3_func_interp_get_else(c, current), eleven);
        assert_eq!(Z3_func_interp_get_num_entries(c, current), 0);
        assert!(Z3_model_has_interp(c, model, function));
        Z3_del_context(c);
    }
}

#[test]
fn model_inventory_keeps_overloaded_user_declarations_distinct() {
    // SAFETY: the context owns every declaration, model and value handle until
    // the final destruction; all domain arrays remain live during each call.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let boolean = Z3_mk_bool_sort(c);
        let name = Z3_mk_string_symbol(c, c"overloaded_model_member".as_ptr());
        let model = Z3_mk_model(c);
        let constant_int = Z3_mk_func_decl(c, name, 0, ptr::null(), int);
        let constant_bool = Z3_mk_func_decl(c, name, 0, ptr::null(), boolean);
        let seven = Z3_mk_int(c, 7, int);
        let yes = Z3_mk_true(c);
        Z3_add_const_interp(c, model, constant_int, seven);
        Z3_add_const_interp(c, model, constant_bool, yes);
        assert_eq!(Z3_model_get_num_consts(c, model), 2);
        for i in 0..2 {
            let declaration = Z3_model_get_const_decl(c, model, i);
            assert!(!declaration.is_null());
            let value = Z3_model_get_const_interp(c, model, declaration);
            if Z3_is_eq_func_decl(c, declaration, constant_int) {
                assert_eq!(value, seven);
            } else {
                assert!(Z3_is_eq_func_decl(c, declaration, constant_bool));
                assert_eq!(value, yes);
            }
        }
        let function_int = Z3_mk_func_decl(c, name, 1, &int, int);
        let function_bool = Z3_mk_func_decl(c, name, 1, &boolean, int);
        let eleven = Z3_mk_int(c, 11, int);
        let first = Z3_add_func_interp(c, model, function_int, seven);
        let second = Z3_add_func_interp(c, model, function_bool, eleven);
        assert_eq!(Z3_model_get_num_funcs(c, model), 2);
        for i in 0..2 {
            let declaration = Z3_model_get_func_decl(c, model, i);
            assert!(!declaration.is_null());
            let interpretation = Z3_model_get_func_interp(c, model, declaration);
            if Z3_is_eq_func_decl(c, declaration, function_int) {
                assert_eq!(interpretation, first);
            } else {
                assert!(Z3_is_eq_func_decl(c, declaration, function_bool));
                assert_eq!(interpretation, second);
            }
        }
        Z3_del_context(c);
    }
}

#[test]
fn model_inventory_merges_snapshot_and_user_constants_without_duplicates() {
    // SAFETY: this test owns the context, solver, model, declarations and ASTs
    // until context destruction, and passes valid live handles throughout.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"snapshot_x".as_ptr()), int);
        let seven = Z3_mk_int(c, 7, int);
        let solver = Z3_mk_solver(c);
        Z3_solver_assert(c, solver, Z3_mk_eq(c, x, seven));
        assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
        let model = Z3_solver_get_model(c, solver);
        assert!(!model.is_null());
        assert_eq!(Z3_model_get_num_consts(c, model), 1);
        let x_decl = Z3_get_app_decl(c, Z3_to_app(c, x));
        let eleven = Z3_mk_int(c, 11, int);
        Z3_add_const_interp(c, model, x_decl, eleven);
        assert_eq!(Z3_model_get_num_consts(c, model), 1);
        let listed = Z3_model_get_const_decl(c, model, 0);
        assert_eq!(Z3_model_get_const_interp(c, model, listed), eleven);
        let y_decl = Z3_mk_func_decl(
            c,
            Z3_mk_string_symbol(c, c"user_y".as_ptr()),
            0,
            ptr::null(),
            int,
        );
        Z3_add_const_interp(c, model, y_decl, seven);
        assert_eq!(Z3_model_get_num_consts(c, model), 2);
        let listed_y = Z3_model_get_const_decl(c, model, 1);
        assert!(Z3_is_eq_func_decl(c, listed_y, y_decl));
        assert_eq!(Z3_model_get_const_interp(c, model, listed_y), seven);
        Z3_del_context(c);
    }
}

#[test]
fn fixedpoint_assert_and_get_assertions() {
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        let t = Z3_mk_true(c);
        Z3_fixedpoint_assert(c, fp, t);
        let asserts = Z3_fixedpoint_get_assertions(c, fp);
        assert!(!asserts.is_null());
        assert!(
            Z3_ast_vector_size(c, asserts) >= 1,
            "asserted axiom must be retained"
        );
        Z3_del_context(c);
    }
}

#[test]
fn fixedpoint_reason_unknown_is_sound() {
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        // Before any query, reason-unknown is a (possibly empty) non-null string,
        // never a fabricated verdict.
        let r = Z3_fixedpoint_get_reason_unknown(c, fp);
        assert!(!r.is_null());
        Z3_del_context(c);
    }
}

/// Parse `script` through `Z3_fixedpoint_from_string`, run its first
/// query, and return `Z3_fixedpoint_query`'s verdict.
///
/// # Safety
/// Test-local helper; owns its context for the call's duration.
unsafe fn query_via_script(script: &std::ffi::CStr) -> i32 {
    // SAFETY: all handles created and consumed inside this call.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        let q = Z3_fixedpoint_from_string(c, fp, script.as_ptr());
        assert!(
            !q.is_null(),
            "script must parse: err {}",
            Z3_get_error_code(c)
        );
        assert_eq!(Z3_ast_vector_size(c, q), 1);
        let verdict = Z3_fixedpoint_query(c, fp, Z3_ast_vector_get(c, q, 0));
        Z3_del_context(c);
        verdict
    }
}

/// The SMT-LIB2 fixedpoint script dialect end-to-end: reachable and
/// unreachable queries match the z3 CLI's sat/unsat polarity for the
/// same scripts (libz3's own `from_string` segfaults on these inputs,
/// so the CLI is the oracle).
#[test]
fn fixedpoint_from_string_parses_and_queries() {
    // SAFETY: test-scope helper; see above.
    unsafe {
        // R = {0,1,2,3}: (query R) is reachable.
        assert_eq!(
            query_via_script(c"(declare-rel R (Int))(declare-var x Int)(rule (R 0))(rule (=> (and (R x) (< x 3)) (R (+ x 1))))(query R)"),
            Z3_L_TRUE
        );
        // No initiation fact: R is empty, query unreachable.
        assert_eq!(
            query_via_script(c"(declare-rel R (Int))(declare-var x Int)(rule (=> (and (R x) (< x 3)) (R (+ x 1))))(query R)"),
            Z3_L_FALSE
        );
        // Ground query beyond the reachable set (max 3).
        assert_eq!(
            query_via_script(c"(declare-rel R (Int))(declare-var x Int)(rule (R 0))(rule (=> (and (R x) (< x 3)) (R (+ x 1))))(query (R 4))"),
            Z3_L_FALSE
        );
    }
}

/// A malformed or unelaboratable script fails with `Z3_PARSER_ERROR`
/// and a null vector, adding nothing (a later good script still works
/// on the same handle).
#[test]
fn fixedpoint_from_string_rejects_bad_scripts() {
    // SAFETY: test-scope unsafe block; handles owned here.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        assert!(Z3_fixedpoint_from_string(c, fp, c"hello world".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        assert!(Z3_fixedpoint_from_string(c, fp, c"(rule (S 0))".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        let q = Z3_fixedpoint_from_string(
            c,
            fp,
            c"(declare-rel R (Int))(rule (R 0))(query R)".as_ptr(),
        );
        assert!(!q.is_null());
        assert_eq!(
            Z3_fixedpoint_query(c, fp, Z3_ast_vector_get(c, q, 0)),
            Z3_L_TRUE
        );
        Z3_del_context(c);
    }
}

/// `Z3_fixedpoint_from_file` reads and parses a script file; a missing
/// file is `Z3_PARSER_ERROR` + null (z3's shapes).
#[test]
fn fixedpoint_from_file_parses() {
    // SAFETY: test-scope unsafe block; handles owned here.
    unsafe {
        let c = ctx();
        let fp = Z3_mk_fixedpoint(c);
        assert!(!fp.is_null());
        assert!(Z3_fixedpoint_from_file(c, fp, c"/nonexistent/ay-fp-test.smt2".as_ptr()).is_null());
        assert_eq!(Z3_get_error_code(c), Z3_PARSER_ERROR);
        let path = std::env::temp_dir().join("ay_fp_from_file_test.smt2");
        std::fs::write(&path, "(declare-rel R (Int))(rule (R 0))(query R)").expect("write script");
        let cpath = std::ffi::CString::new(path.to_string_lossy().into_owned()).expect("path");
        let q = Z3_fixedpoint_from_file(c, fp, cpath.as_ptr());
        assert!(!q.is_null(), "err {}", Z3_get_error_code(c));
        assert_eq!(
            Z3_fixedpoint_query(c, fp, Z3_ast_vector_get(c, q, 0)),
            Z3_L_TRUE
        );
        let _ = std::fs::remove_file(&path);
        Z3_del_context(c);
    }
}
