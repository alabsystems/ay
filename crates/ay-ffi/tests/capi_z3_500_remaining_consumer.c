// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Valid-call probes for public Z3 5.0.0 declarations that were not exercised
// by the original AY C-consumer families.  This source includes only the stock
// header and is compiled unchanged against the pinned Z3 5.0.0 library and AY.

#ifndef _GNU_SOURCE
#define _GNU_SOURCE 1
#endif

#include "z3.h"

#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define AY_MAX_CALLABILITY_MARKERS 805

static const char *ay_called[AY_MAX_CALLABILITY_MARKERS];
static size_t ay_called_count;

static void ay_mark_call(const char *name) {
    for (size_t i = 0; i < ay_called_count; ++i) {
        if (strcmp(ay_called[i], name) == 0) {
            return;
        }
    }
    if (ay_called_count >= AY_MAX_CALLABILITY_MARKERS) {
        fputs("callability marker capacity exceeded\n", stderr);
        abort();
    }
    ay_called[ay_called_count++] = name;
}

#define AY_CALL(function, arguments) (ay_mark_call(#function), function arguments)

static int ay_compare_called(const void *left, const void *right) {
    const char *const *lhs = left;
    const char *const *rhs = right;
    return strcmp(*lhs, *rhs);
}

static void ay_print_callability(void) {
    qsort(ay_called, ay_called_count, sizeof(ay_called[0]), ay_compare_called);
    for (size_t i = 0; i < ay_called_count; ++i) {
        printf("AY-CALL %s\n", ay_called[i]);
    }
}

static int ay_verify_loaded_library(const char *expected) {
    if (expected && strcmp(expected, "--static") == 0) {
        return 1;
    }
    Dl_info info;
    if (!expected || dladdr((const void *)Z3_get_full_version, &info) == 0 ||
        !info.dli_fname) {
        return 0;
    }
    char *actual_path = realpath(info.dli_fname, NULL);
    char *expected_path = realpath(expected, NULL);
    int matches = actual_path && expected_path &&
                  strcmp(actual_path, expected_path) == 0;
    free(actual_path);
    free(expected_path);
    return matches;
}

#define CHECK(value)                                                           \
    do {                                                                       \
        if (!(value)) {                                                        \
            fprintf(stderr, "check failed at %s:%d: %s\n", __FILE__, __LINE__, \
                    #value);                                                   \
            return 1;                                                          \
        }                                                                      \
    } while (0)

static void ignore_error(Z3_context c, Z3_error_code error) {
    (void)c;
    (void)error;
}

static int quantifier_and_container_family(Z3_context c) {
    Z3_sort ints = AY_CALL(Z3_mk_int_sort, (c));
    Z3_sort bound_sorts[1] = {ints};
    Z3_symbol bound_names[1] = {AY_CALL(Z3_mk_string_symbol, (c, "x"))};
    Z3_symbol generic_names[1] = {AY_CALL(Z3_mk_string_symbol, (c, "y"))};
    Z3_symbol extended_names[1] = {AY_CALL(Z3_mk_string_symbol, (c, "z"))};
    Z3_ast bound = AY_CALL(Z3_mk_bound, (c, 0, ints));
    Z3_ast body = AY_CALL(Z3_mk_eq, (c, bound, bound));
    Z3_ast no_patterns[1] = {body};
    Z3_symbol qid = AY_CALL(Z3_mk_string_symbol, (c, "q"));
    Z3_symbol skid = AY_CALL(Z3_mk_string_symbol, (c, "sk"));

    Z3_ast forall_q = AY_CALL(Z3_mk_forall, (c, 3, 0, NULL, 1, bound_sorts,
                                   bound_names, body));
    CHECK(forall_q);
    // Exact Z3 5.0.0 returns the caller-supplied priority hint unchanged.
    CHECK(AY_CALL(Z3_get_quantifier_weight, (c, forall_q)) == 3);
    Z3_ast exists_q = AY_CALL(Z3_mk_exists, (c, 4, 0, NULL, 1, bound_sorts,
                                   bound_names, body));
    Z3_ast generic_q = AY_CALL(Z3_mk_quantifier, (c, true, 5, 0, NULL, 1,
                                        bound_sorts, generic_names, body));
    Z3_ast extended_q = AY_CALL(Z3_mk_quantifier_ex, (
        c, false, 6, qid, skid, 0, NULL, 1, no_patterns, 1, bound_sorts, extended_names,
        body));

    CHECK(forall_q && exists_q && generic_q && extended_q);
    CHECK(AY_CALL(Z3_is_quantifier_forall, (c, forall_q)));
    CHECK(AY_CALL(Z3_is_quantifier_exists, (c, exists_q)));
    CHECK(AY_CALL(Z3_get_quantifier_num_bound, (c, forall_q)) == 1);
    CHECK(AY_CALL(Z3_get_quantifier_bound_name, (c, forall_q, 0)));
    CHECK(AY_CALL(Z3_get_quantifier_num_no_patterns, (c, forall_q)) == 0);
    CHECK(AY_CALL(Z3_get_quantifier_num_no_patterns, (c, extended_q)) == 1);
    CHECK(AY_CALL(Z3_get_quantifier_no_pattern_ast, (c, extended_q, 0)));

    Z3_ast one = AY_CALL(Z3_mk_int, (c, 1, ints));
    Z3_ast substituted = AY_CALL(Z3_substitute_vars, (c, bound, 1, &one));
    CHECK(substituted && AY_CALL(Z3_is_eq_ast, (c, substituted, one)));

    Z3_func_decl f = AY_CALL(Z3_mk_func_decl, (c, AY_CALL(Z3_mk_string_symbol, (c, "f")), 1,
                                     &ints, ints));
    Z3_ast x = AY_CALL(Z3_mk_const, (c, AY_CALL(Z3_mk_string_symbol, (c, "x0")), ints));
    Z3_ast fx = AY_CALL(Z3_mk_app, (c, f, 1, &x));
    Z3_pattern pattern = AY_CALL(Z3_mk_pattern, (c, 1, &fx));
    Z3_app x_app = AY_CALL(Z3_to_app, (c, x));
    Z3_ast const_q = AY_CALL(Z3_mk_quantifier_const, (
        c, true, 7, 1, &x_app, 1, &pattern, AY_CALL(Z3_mk_eq, (c, fx, x))));
    CHECK(pattern && AY_CALL(Z3_pattern_to_string, (c, pattern)));
    CHECK(const_q && AY_CALL(Z3_is_quantifier_forall, (c, const_q)));

    Z3_ast string = AY_CALL(Z3_mk_string, (c, "abc"));
    CHECK(string && AY_CALL(Z3_is_string, (c, string)));
    CHECK(AY_CALL(Z3_get_string, (c, string)));
    CHECK(strcmp(AY_CALL(Z3_get_string, (c, string)), "abc") == 0);

    Z3_sort set_sort = AY_CALL(Z3_mk_set_sort, (c, ints));
    Z3_ast empty = AY_CALL(Z3_mk_empty_set, (c, ints));
    Z3_ast with_one = AY_CALL(Z3_mk_set_add, (c, empty, one));
    Z3_ast without_one = AY_CALL(Z3_mk_set_del, (c, with_one, one));
    CHECK(set_sort && with_one && without_one);
    CHECK(AY_CALL(Z3_mk_set_subset, (c, without_one, with_one)));
    return 0;
}

static int datatype_family(Z3_context c) {
    Z3_sort ints = AY_CALL(Z3_mk_int_sort, (c));
    Z3_symbol enum_names[2] = {AY_CALL(Z3_mk_string_symbol, (c, "red")),
                               AY_CALL(Z3_mk_string_symbol, (c, "blue"))};
    Z3_func_decl enum_values[2] = {NULL, NULL};
    Z3_func_decl enum_testers[2] = {NULL, NULL};
    Z3_sort colors = AY_CALL(Z3_mk_enumeration_sort, (
        c, AY_CALL(Z3_mk_string_symbol, (c, "Color500")), 2, enum_names, enum_values,
        enum_testers));
    CHECK(colors && enum_values[0] && enum_values[1]);
    CHECK(enum_testers[0] && enum_testers[1]);

    Z3_func_decl nil = NULL;
    Z3_func_decl is_nil = NULL;
    Z3_func_decl cons = NULL;
    Z3_func_decl is_cons = NULL;
    Z3_func_decl head = NULL;
    Z3_func_decl tail = NULL;
    Z3_sort list = AY_CALL(Z3_mk_list_sort, (c, AY_CALL(Z3_mk_string_symbol, (c, "IntList500")),
                                   ints, &nil, &is_nil, &cons, &is_cons, &head,
                                   &tail));
    CHECK(list && nil && is_nil && cons && is_cons && head && tail);
    CHECK(AY_CALL(Z3_is_recursive_datatype_sort, (c, list)));

    Z3_ast nil_value = AY_CALL(Z3_mk_app, (c, nil, 0, NULL));
    Z3_ast one = AY_CALL(Z3_mk_int, (c, 1, ints));
    Z3_ast two = AY_CALL(Z3_mk_int, (c, 2, ints));
    Z3_ast cons_args[2] = {one, nil_value};
    Z3_ast cons_value = AY_CALL(Z3_mk_app, (c, cons, 2, cons_args));
    Z3_ast updated = AY_CALL(Z3_datatype_update_field, (c, head, cons_value, two));
    CHECK(nil_value && cons_value && updated);

    Z3_symbol field_names[1] = {AY_CALL(Z3_mk_string_symbol, (c, "value"))};
    Z3_sort field_sorts[1] = {ints};
    unsigned sort_refs[1] = {0};
    Z3_constructor constructor = AY_CALL(Z3_mk_constructor, (
        c, AY_CALL(Z3_mk_string_symbol, (c, "box")), AY_CALL(Z3_mk_string_symbol, (c, "is-box")),
        1, field_names, field_sorts, sort_refs));
    CHECK(constructor);
    CHECK(AY_CALL(Z3_constructor_num_fields, (c, constructor)) == 1);
    AY_CALL(Z3_del_constructor, (c, constructor));

    Z3_sort forward = AY_CALL(Z3_mk_datatype_sort, (
        c, AY_CALL(Z3_mk_string_symbol, (c, "Forward500")), 0, NULL));
    CHECK(forward);
    return 0;
}

static int goal_tactic_probe_family(Z3_context c) {
    Z3_goal goal = AY_CALL(Z3_mk_goal, (c, false, false, false));
    CHECK(goal);
    AY_CALL(Z3_goal_inc_ref, (c, goal));
    AY_CALL(Z3_goal_assert, (c, goal, AY_CALL(Z3_mk_true, (c))));
    CHECK(AY_CALL(Z3_goal_to_dimacs_string, (c, goal, false)));

    Z3_tactic tactic = AY_CALL(Z3_tactic_skip, (c));
    CHECK(tactic);
    AY_CALL(Z3_tactic_inc_ref, (c, tactic));
    Z3_apply_result result = AY_CALL(Z3_tactic_apply, (c, tactic, goal));
    CHECK(result);
    AY_CALL(Z3_apply_result_inc_ref, (c, result));
    CHECK(AY_CALL(Z3_apply_result_get_num_subgoals, (c, result)) == 1);
    CHECK(AY_CALL(Z3_apply_result_get_subgoal, (c, result, 0)));
    CHECK(AY_CALL(Z3_apply_result_to_string, (c, result)));
    AY_CALL(Z3_apply_result_dec_ref, (c, result));
    AY_CALL(Z3_tactic_dec_ref, (c, tactic));

    Z3_probe size = AY_CALL(Z3_mk_probe, (c, "size"));
    CHECK(size);
    AY_CALL(Z3_probe_inc_ref, (c, size));
    Z3_probe less = AY_CALL(Z3_probe_lt, (c, size, size));
    CHECK(less);
    AY_CALL(Z3_probe_inc_ref, (c, less));
    Z3_probe greater_equal = AY_CALL(Z3_probe_ge, (c, size, size));
    CHECK(greater_equal);
    AY_CALL(Z3_probe_inc_ref, (c, greater_equal));
    CHECK(AY_CALL(Z3_probe_apply, (c, less, goal)) == 0.0);
    CHECK(AY_CALL(Z3_probe_apply, (c, greater_equal, goal)) == 1.0);
    AY_CALL(Z3_probe_dec_ref, (c, greater_equal));
    AY_CALL(Z3_probe_dec_ref, (c, less));
    AY_CALL(Z3_probe_dec_ref, (c, size));

    CHECK(AY_CALL(Z3_simplify_get_help, (c)));
    Z3_param_descrs simplify_descrs = AY_CALL(Z3_simplify_get_param_descrs, (c));
    CHECK(simplify_descrs);
    AY_CALL(Z3_param_descrs_inc_ref, (c, simplify_descrs));
    Z3_params empty_params = AY_CALL(Z3_mk_params, (c));
    CHECK(empty_params);
    AY_CALL(Z3_params_inc_ref, (c, empty_params));
    AY_CALL(Z3_params_validate, (c, empty_params, simplify_descrs));
    AY_CALL(Z3_params_dec_ref, (c, empty_params));
    AY_CALL(Z3_param_descrs_dec_ref, (c, simplify_descrs));

    AY_CALL(Z3_goal_dec_ref, (c, goal));
    return 0;
}

static int solver_and_model_family(Z3_context c) {
    Z3_sort ints = AY_CALL(Z3_mk_int_sort, (c));
    Z3_ast x = AY_CALL(Z3_mk_const, (c, AY_CALL(Z3_mk_string_symbol, (c, "model-x")), ints));
    Z3_ast one = AY_CALL(Z3_mk_int, (c, 1, ints));
    Z3_ast two = AY_CALL(Z3_mk_int, (c, 2, ints));

    Z3_solver simple = AY_CALL(Z3_mk_simple_solver, (c));
    CHECK(simple);
    AY_CALL(Z3_solver_inc_ref, (c, simple));
    Z3_solver logic =
        AY_CALL(Z3_mk_solver_for_logic, (c, AY_CALL(Z3_mk_string_symbol, (c, "QF_LIA"))));
    CHECK(logic);
    AY_CALL(Z3_solver_inc_ref, (c, logic));

    Z3_params params = AY_CALL(Z3_mk_params, (c));
    CHECK(params);
    AY_CALL(Z3_params_inc_ref, (c, params));
    AY_CALL(Z3_params_set_double, (c, params, AY_CALL(Z3_mk_string_symbol, (c, "random_freq")),
                         0.01));
    AY_CALL(Z3_solver_set_params, (c, logic, params));
    AY_CALL(Z3_solver_set_initial_value, (c, logic, x, one));
    AY_CALL(Z3_solver_assert, (c, logic, AY_CALL(Z3_mk_eq, (c, x, one))));
    CHECK(AY_CALL(Z3_solver_check, (c, logic)) == Z3_L_TRUE);
    Z3_model solved_model = AY_CALL(Z3_solver_get_model, (c, logic));
    CHECK(solved_model);
    AY_CALL(Z3_model_inc_ref, (c, solved_model));

    AY_CALL(Z3_solver_interrupt, (c, simple));

    Z3_model manual_model = AY_CALL(Z3_mk_model, (c));
    CHECK(manual_model);
    AY_CALL(Z3_model_inc_ref, (c, manual_model));
    Z3_func_decl f = AY_CALL(Z3_mk_func_decl, (c, AY_CALL(Z3_mk_string_symbol, (c, "mf")), 1,
                                     &ints, ints));
    Z3_func_interp interp = AY_CALL(Z3_add_func_interp, (c, manual_model, f, one));
    CHECK(interp);
    AY_CALL(Z3_func_interp_inc_ref, (c, interp));
    Z3_ast_vector args = AY_CALL(Z3_mk_ast_vector, (c));
    CHECK(args);
    AY_CALL(Z3_ast_vector_inc_ref, (c, args));
    AY_CALL(Z3_ast_vector_push, (c, args, one));
    AY_CALL(Z3_func_interp_add_entry, (c, interp, args, two));
    AY_CALL(Z3_func_interp_set_else, (c, interp, two));
    CHECK(AY_CALL(Z3_model_get_func_interp, (c, manual_model, f)));
    AY_CALL(Z3_ast_vector_dec_ref, (c, args));
    AY_CALL(Z3_func_interp_dec_ref, (c, interp));

    Z3_goal goal = AY_CALL(Z3_mk_goal, (c, false, false, false));
    CHECK(goal);
    AY_CALL(Z3_goal_inc_ref, (c, goal));
    Z3_model converted = AY_CALL(Z3_goal_convert_model, (c, goal, manual_model));
    CHECK(converted);
    AY_CALL(Z3_model_inc_ref, (c, converted));
    AY_CALL(Z3_model_dec_ref, (c, converted));
    AY_CALL(Z3_goal_dec_ref, (c, goal));

    Z3_ast x_eq_one = AY_CALL(Z3_mk_eq, (c, x, one));
    Z3_app x_app = AY_CALL(Z3_to_app, (c, x));
    Z3_ast projected = AY_CALL(Z3_qe_model_project, (c, solved_model, 1, &x_app,
                                           x_eq_one));
    CHECK(projected);
    Z3_ast_map witnesses = AY_CALL(Z3_mk_ast_map, (c));
    CHECK(witnesses);
    AY_CALL(Z3_ast_map_inc_ref, (c, witnesses));
    CHECK(AY_CALL(Z3_qe_model_project_skolem, (c, solved_model, 1, &x_app, x_eq_one,
                                     witnesses)));
    CHECK(AY_CALL(Z3_qe_model_project_with_witness, (c, solved_model, 1, &x_app,
                                           x_eq_one, witnesses)));
    AY_CALL(Z3_ast_map_dec_ref, (c, witnesses));

    Z3_ast_vector vars = AY_CALL(Z3_mk_ast_vector, (c));
    CHECK(vars);
    AY_CALL(Z3_ast_vector_inc_ref, (c, vars));
    AY_CALL(Z3_ast_vector_push, (c, vars, x));
    CHECK(AY_CALL(Z3_qe_lite, (c, vars, x_eq_one)));
    AY_CALL(Z3_ast_vector_dec_ref, (c, vars));

    AY_CALL(Z3_model_dec_ref, (c, manual_model));
    AY_CALL(Z3_model_dec_ref, (c, solved_model));
    AY_CALL(Z3_params_dec_ref, (c, params));
    AY_CALL(Z3_solver_dec_ref, (c, logic));
    AY_CALL(Z3_solver_dec_ref, (c, simple));
    return 0;
}

static int algebraic_and_rendering_family(Z3_context c) {
    Z3_sort real = AY_CALL(Z3_mk_real_sort, (c));
    Z3_ast zero = AY_CALL(Z3_mk_numeral, (c, "0", real));
    Z3_ast one = AY_CALL(Z3_mk_numeral, (c, "1", real));
    CHECK(zero && one);
    CHECK(AY_CALL(Z3_algebraic_is_value, (c, zero)));
    CHECK(AY_CALL(Z3_algebraic_is_zero, (c, zero)));
    CHECK(AY_CALL(Z3_algebraic_eval, (c, zero, 0, NULL)) == 0);

    Z3_ast assumptions[1] = {AY_CALL(Z3_mk_true, (c))};
    Z3_string benchmark = AY_CALL(Z3_benchmark_to_smtlib_string, (
        c, "z3-500", "QF_LRA", "sat", "", 1, assumptions,
        AY_CALL(Z3_mk_eq, (c, one, one))));
    CHECK(benchmark && strstr(benchmark, "QF_LRA"));

    AY_CALL(Z3_set_ast_print_mode, (c, Z3_PRINT_SMTLIB2_COMPLIANT));
    CHECK(AY_CALL(Z3_ast_to_string, (c, one)));
    AY_CALL(Z3_set_ast_print_mode, (c, Z3_PRINT_SMTLIB2_COMPLIANT));
    return 0;
}

int main(int argc, char **argv) {
    CHECK(argc == 2 && ay_verify_loaded_library(argv[1]));
    Z3_config config = AY_CALL(Z3_mk_config, ());
    CHECK(config);
    Z3_context context = AY_CALL(Z3_mk_context, (config));
    AY_CALL(Z3_del_config, (config));
    CHECK(context);
    AY_CALL(Z3_set_error_handler, (context, ignore_error));

    CHECK(quantifier_and_container_family(context) == 0);
    CHECK(datatype_family(context) == 0);
    CHECK(goal_tactic_probe_family(context) == 0);
    CHECK(solver_and_model_family(context) == 0);
    CHECK(algebraic_and_rendering_family(context) == 0);

    AY_CALL(Z3_del_context, (context));
    ay_print_callability();
    puts("exact Z3 5.0.0 remaining safe-call probes passed");
    return 0;
}
