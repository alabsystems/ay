// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[test]
fn sequence_power_c_api_constructs_and_solves_string_repetition() {
    // SAFETY: all handles are allocated by this context on this thread.
    unsafe {
        let config = Z3_mk_config();
        let context = Z3_mk_context(config);
        Z3_del_config(config);
        let int_sort = Z3_mk_int_sort(context);
        let three = Z3_mk_int(context, 3, int_sort);
        let base = Z3_mk_string(context, c"ab".as_ptr());
        let repeated = Z3_mk_seq_power(context, base, three);
        assert_ne!(repeated, 0);
        assert_eq!(
            Z3_get_decl_kind(
                context,
                Z3_get_app_decl(context, Z3_to_app(context, repeated))
            ),
            Z3_OP_SEQ_POWER
        );
        let length = Z3_mk_seq_length(context, repeated);
        assert_eq!(
            Z3_get_decl_kind(
                context,
                Z3_get_app_decl(context, Z3_to_app(context, length))
            ),
            Z3_OP_SEQ_LENGTH
        );
        let expected = Z3_mk_string(context, c"ababab".as_ptr());
        let equality = Z3_mk_eq(context, repeated, expected);
        let negation = Z3_mk_not(context, equality);
        let solver = Z3_mk_solver(context);
        Z3_solver_assert(context, solver, negation);
        assert_eq!(Z3_solver_check(context, solver), Z3_L_FALSE);
        assert_eq!(Z3_mk_seq_power(context, three, three), 0);
        assert_eq!(Z3_get_error_code(context), Z3_SORT_ERROR);
        Z3_del_context(context);
    }
}

#[test]
fn sequence_power_symbolic_count_solves_membership_and_length() {
    for (target, lower_bound, expected) in [
        (c"ababab", Some(1000), Z3_L_FALSE),
        (c"abba", None, Z3_L_FALSE),
        (c"ababab", None, Z3_L_TRUE),
    ] {
        // SAFETY: each iteration owns a fresh context and all of its handles.
        unsafe {
            let config = Z3_mk_config();
            let context = Z3_mk_context(config);
            Z3_del_config(config);
            let int_sort = Z3_mk_int_sort(context);
            let name = Z3_mk_string_symbol(context, c"n".as_ptr());
            let count = Z3_mk_const(context, name, int_sort);
            let base = Z3_mk_string(context, c"ab".as_ptr());
            let power = Z3_mk_seq_power(context, base, count);
            let word = Z3_mk_string(context, target.as_ptr());
            let equality = Z3_mk_eq(context, power, word);
            let solver = Z3_mk_solver(context);
            Z3_solver_assert(context, solver, equality);
            if let Some(lower_bound) = lower_bound {
                let minimum = Z3_mk_int(context, lower_bound, int_sort);
                let bound = Z3_mk_ge(context, count, minimum);
                Z3_solver_assert(context, solver, bound);
            }
            assert_eq!(Z3_solver_check(context, solver), expected);
            if expected == Z3_L_TRUE {
                let model = Z3_solver_get_model(context, solver);
                let mut value = 0;
                assert!(Z3_model_eval(context, model, power, true, &mut value));
                let text = Z3_get_string(context, value);
                assert!(!text.is_null());
                assert_eq!(std::ffi::CStr::from_ptr(text), c"ababab");
            }
            Z3_del_context(context);
        }
    }
}
