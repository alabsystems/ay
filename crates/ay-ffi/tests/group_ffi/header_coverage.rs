// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Integration test for ay_z3_compat.h header coverage (#4990).
//!
//! Exercises all 19 functions that were added to the header in the
//! header-implementation sync. Tests that each function is callable and
//! returns sensible results.

use ay_ffi::z3_compat::*;
use std::ffi::CStr;

/// Test symbol introspection: Z3_get_symbol_kind, Z3_get_symbol_int.
#[test]
fn test_symbol_introspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        // String symbol
        let str_sym = Z3_mk_string_symbol(ctx, c"foo".as_ptr());
        assert_eq!(Z3_get_symbol_kind(ctx, str_sym), 1); // Z3_STRING_SYMBOL

        // Int symbol
        let int_sym = Z3_mk_int_symbol(ctx, 42);
        assert_eq!(Z3_get_symbol_kind(ctx, int_sym), 0); // Z3_INT_SYMBOL
        assert_eq!(Z3_get_symbol_int(ctx, int_sym), 42);

        Z3_del_context(ctx);
    }
}

/// Test sort identity: Z3_get_sort_name, Z3_is_eq_sort, Z3_get_sort_id.
#[test]
fn test_sort_identity() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let bool_sort = Z3_mk_bool_sort(ctx);

        // Sort name
        let name = Z3_get_sort_name(ctx, int_sort);
        assert!(!name.is_null());
        let name_str = Z3_get_symbol_string(ctx, name);
        assert!(!name_str.is_null());
        let name_rs = CStr::from_ptr(name_str).to_string_lossy();
        assert!(
            name_rs.contains("Int") || name_rs.contains("int"),
            "Int sort name should contain 'Int', got: {name_rs}"
        );

        // Sort equality
        let int_sort2 = Z3_mk_int_sort(ctx);
        assert!(Z3_is_eq_sort(ctx, int_sort, int_sort2));
        assert!(!Z3_is_eq_sort(ctx, int_sort, bool_sort));

        // Sort ID is non-zero for valid sorts
        let id = Z3_get_sort_id(ctx, int_sort);
        assert_ne!(id, 0);

        Z3_del_context(ctx);
    }
}

/// Test Z3_mk_power: exponentiation.
#[test]
fn test_mk_power() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let two = Z3_mk_int(ctx, 2, int_sort);
        let three = Z3_mk_int(ctx, 3, int_sort);
        let power = Z3_mk_power(ctx, two, three);
        assert_ne!(power, 0, "Z3_mk_power should return non-null AST");

        Z3_del_context(ctx);
    }
}

/// Test AST inspection: Z3_is_numeral_ast, Z3_get_bool_value.
#[test]
fn test_ast_inspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let five = Z3_mk_int(ctx, 5, int_sort);

        // Numeral check
        assert!(Z3_is_numeral_ast(ctx, five));

        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        assert!(!Z3_is_numeral_ast(ctx, x));

        // Bool value
        let t = Z3_mk_true(ctx);
        let f = Z3_mk_false(ctx);
        assert_eq!(Z3_get_bool_value(ctx, t), Z3_L_TRUE);
        assert_eq!(Z3_get_bool_value(ctx, f), Z3_L_FALSE);

        Z3_del_context(ctx);
    }
}

/// Test numeral extraction: uint, int64, uint64.
#[test]
fn test_numeral_extraction() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let val = Z3_mk_int(ctx, 42, int_sort);

        // Z3_get_numeral_uint
        let mut u: u32 = 0;
        let ok = Z3_get_numeral_uint(ctx, val, &raw mut u);
        assert!(ok);
        assert_eq!(u, 42);

        // Z3_get_numeral_int64
        let mut i64_val: i64 = 0;
        let ok = Z3_get_numeral_int64(ctx, val, &raw mut i64_val);
        assert!(ok);
        assert_eq!(i64_val, 42);

        // Z3_get_numeral_uint64
        let mut u64_val: u64 = 0;
        let ok = Z3_get_numeral_uint64(ctx, val, &raw mut u64_val);
        assert!(ok);
        assert_eq!(u64_val, 42);

        Z3_del_context(ctx);
    }
}

/// Test func_decl introspection: domain_size, decl_kind, func_decl_to_ast,
/// is_eq_func_decl, func_decl_to_string.
#[test]
fn test_func_decl_introspection() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"f".as_ptr());
        let domain = [int_sort];
        let f = Z3_mk_func_decl(ctx, sym, 1, domain.as_ptr(), int_sort);
        assert!(!f.is_null());

        // Domain size
        let dsz = Z3_get_domain_size(ctx, f);
        assert_eq!(dsz, 1);

        // Decl kind (uninterpreted function → Z3_OP_UNINTERPRETED)
        let _kind = Z3_get_decl_kind(ctx, f);

        // func_decl_to_ast: REAL now — a value-canonical tagged handle with
        // kind Z3_FUNC_DECL_AST that round-trips through Z3_to_func_decl
        // (full battery in z3_compat/capi_handle_tests.rs).
        let ast = Z3_func_decl_to_ast(ctx, f);
        assert_ne!(ast, 0);
        assert_eq!(Z3_get_ast_kind(ctx, ast), 5); // Z3_FUNC_DECL_AST
        let back = Z3_to_func_decl(ctx, ast);
        assert!(!back.is_null());
        assert!(Z3_is_eq_func_decl(ctx, back, f));

        // is_eq_func_decl
        assert!(Z3_is_eq_func_decl(ctx, f, f));

        // func_decl_to_string
        let s = Z3_func_decl_to_string(ctx, f);
        assert!(!s.is_null());
        let rs = CStr::from_ptr(s).to_string_lossy();
        assert!(
            rs.contains('f'),
            "func_decl_to_string should contain 'f', got: {rs}"
        );

        Z3_del_context(ctx);
    }
}

/// Test solver extras: Z3_solver_get_num_scopes, Z3_solver_interrupt.
#[test]
fn test_solver_extras() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let solver = Z3_mk_solver(ctx);

        // get_num_scopes — starts at 0
        let n = Z3_solver_get_num_scopes(ctx, solver);
        assert_eq!(n, 0);

        // push increases scope count
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 1);
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 2);

        // pop decreases scope count
        Z3_solver_pop(ctx, solver, 1);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 1);
        Z3_solver_pop(ctx, solver, 1);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 0);

        // Regression (#6740): reset must collapse scope depth to 0
        Z3_solver_push(ctx, solver);
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 2);
        Z3_solver_reset(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 0);
        // Push after reset counts from zero
        Z3_solver_push(ctx, solver);
        assert_eq!(Z3_solver_get_num_scopes(ctx, solver), 1);

        // solver_interrupt (should not crash)
        Z3_solver_interrupt(ctx, solver);

        Z3_del_context(ctx);
    }
}

/// One set-membership check in a fresh context (one AY solver per context;
/// `Z3_solver_reset` clears the term arena, so cases are isolated by context).
/// `which`: 0 = add(5,empty), 1 = del(5,full), 2 = add(5,empty) (for elem 3).
unsafe fn set_member_check(elem: i32, which: i32) -> std::ffi::c_int {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let e = Z3_mk_int(ctx, elem, int_sort);
        let set = if which == 1 {
            Z3_mk_set_del(ctx, Z3_mk_full_set(ctx, int_sort), five)
        } else {
            Z3_mk_set_add(ctx, Z3_mk_empty_set(ctx, int_sort), five)
        };
        let s = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, s, Z3_mk_set_member(ctx, e, set));
        let r = Z3_solver_check(ctx, s);
        Z3_del_context(ctx);
        r
    }
}

/// Sets via (Array elem Bool): Z3_mk_set_sort/empty/full/add/del/member.
/// Soundness comes from AY's own solver verdicts (#capi_breadth).
#[test]
fn test_sets_capi() {
    unsafe {
        // Sort kind + constructors are well-formed.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let int_sort = Z3_mk_int_sort(ctx);
        let set_sort = Z3_mk_set_sort(ctx, int_sort);
        assert!(!set_sort.is_null());
        assert_eq!(Z3_get_sort_kind(ctx, set_sort), 5); // Z3_ARRAY_SORT
        assert_ne!(Z3_mk_empty_set(ctx, int_sort), 0);
        assert_ne!(Z3_mk_full_set(ctx, int_sort), 0);
        Z3_del_context(ctx);

        // Verdicts, each in its own context.
        assert_eq!(set_member_check(5, 0), Z3_L_TRUE); // 5 in {5}
        assert_eq!(set_member_check(5, 1), Z3_L_FALSE); // 5 in (del 5 full)
        assert_eq!(set_member_check(3, 2), Z3_L_FALSE); // 3 in {5}
    }
}

/// One regex-membership check in a fresh context. `kind`: 0=concat ab,
/// 1=star a, 2=plus a, 3=union ab. Checks `(str.in_re word RE)`.
unsafe fn regex_member_check(word: &CStr, kind: i32) -> std::ffi::c_int {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let ra = Z3_mk_seq_to_re(ctx, Z3_mk_string(ctx, c"a".as_ptr()));
        let rb = Z3_mk_seq_to_re(ctx, Z3_mk_string(ctx, c"b".as_ptr()));
        let re = match kind {
            0 => {
                let args = [ra, rb];
                Z3_mk_re_concat(ctx, 2, args.as_ptr())
            }
            1 => Z3_mk_re_star(ctx, ra),
            2 => Z3_mk_re_plus(ctx, ra),
            _ => {
                let args = [ra, rb];
                Z3_mk_re_union(ctx, 2, args.as_ptr())
            }
        };
        assert_ne!(re, 0);
        let s = Z3_mk_solver(ctx);
        Z3_solver_assert(
            ctx,
            s,
            Z3_mk_seq_in_re(ctx, Z3_mk_string(ctx, word.as_ptr()), re),
        );
        let r = Z3_solver_check(ctx, s);
        Z3_del_context(ctx);
        r
    }
}

/// Regex bridge: Z3_mk_seq_to_re/in_re, Z3_mk_re_star/plus/union/concat.
/// Soundness comes from AY's own solver verdicts (#capi_breadth).
#[test]
fn test_regex_capi() {
    unsafe {
        assert_eq!(regex_member_check(c"ab", 0), Z3_L_TRUE); // (a)
        assert_eq!(regex_member_check(c"ba", 0), Z3_L_FALSE); // (b)
        assert_eq!(regex_member_check(c"aaa", 1), Z3_L_TRUE); // (c) star
        assert_eq!(regex_member_check(c"", 2), Z3_L_FALSE); // (d) plus, >=1
        assert_eq!(regex_member_check(c"b", 3), Z3_L_TRUE); // (e) union

        // n==0 union/concat -> honest 0 + Z3_INVALID_ARG.
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        assert_eq!(Z3_mk_re_union(ctx, 0, std::ptr::null()), 0);
        assert_eq!(Z3_mk_re_concat(ctx, 0, std::ptr::null()), 0);
        Z3_del_context(ctx);
    }
}

/// String-literal accessors + version/global-param surface (#capi_breadth).
#[test]
fn test_string_accessors_capi() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let hello = Z3_mk_string(ctx, c"hello".as_ptr());
        assert!(Z3_is_string(ctx, hello));
        let got = Z3_get_string(ctx, hello);
        assert!(!got.is_null());
        assert_eq!(CStr::from_ptr(got).to_string_lossy(), "hello");
        assert_eq!(Z3_get_string_length(ctx, hello), 5);

        // Non-literal string term (str.++ x hello) is not a literal.
        let str_sort = Z3_mk_string_sort(ctx);
        let x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, c"x".as_ptr()), str_sort);
        let cat_args = [x, hello];
        let cat = Z3_mk_seq_concat(ctx, 2, cat_args.as_ptr());
        assert!(!Z3_is_string(ctx, cat));
        assert!(Z3_get_string(ctx, cat).is_null());
        assert_eq!(Z3_get_string_length(ctx, cat), 0);

        // Int numeral is not a string.
        let int_sort = Z3_mk_int_sort(ctx);
        let five = Z3_mk_int(ctx, 5, int_sort);
        assert!(!Z3_is_string(ctx, five));

        // Version string non-empty; global params are sound no-ops.
        let ver = Z3_get_full_version();
        assert!(!ver.is_null());
        assert!(!CStr::from_ptr(ver).to_bytes().is_empty());
        Z3_global_param_set(c"smt.random_seed".as_ptr(), c"1".as_ptr());
        Z3_global_param_reset_all();

        Z3_del_context(ctx);
    }
}

/// Test model extras: Z3_model_has_interp.
#[test]
fn test_model_has_interp() {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);

        let int_sort = Z3_mk_int_sort(ctx);
        let sym = Z3_mk_string_symbol(ctx, c"x".as_ptr());
        let x = Z3_mk_const(ctx, sym, int_sort);
        let five = Z3_mk_int(ctx, 5, int_sort);
        let eq = Z3_mk_eq(ctx, x, five);

        let solver = Z3_mk_solver(ctx);
        Z3_solver_assert(ctx, solver, eq);
        let result = Z3_solver_check(ctx, solver);
        assert_eq!(result, Z3_L_TRUE);

        let model = Z3_solver_get_model(ctx, solver);
        assert!(!model.is_null());

        // x should have an interpretation in the model
        let decl = Z3_get_app_decl(ctx, x);
        if !decl.is_null() {
            let _has = Z3_model_has_interp(ctx, model, decl);
        }

        Z3_del_context(ctx);
    }
}
