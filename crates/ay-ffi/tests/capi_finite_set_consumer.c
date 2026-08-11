// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay_z3_compat.h"
#endif

#include <stdio.h>
#include <string.h>

#define STATIC_ASSERT(name, expr) typedef char static_assert_##name[(expr) ? 1 : -1]
#define CHECK(expr)                                                            \
    do {                                                                       \
        if (!(expr)) {                                                         \
            fprintf(stderr, "finite-set check failed: %s\n", #expr);          \
            ok = 0;                                                            \
        }                                                                      \
    } while (0)

STATIC_ASSERT(finite_empty, Z3_OP_FINITE_SET_EMPTY == 49152);
STATIC_ASSERT(finite_singleton, Z3_OP_FINITE_SET_SINGLETON == 49153);
STATIC_ASSERT(finite_union, Z3_OP_FINITE_SET_UNION == 49154);
STATIC_ASSERT(finite_intersect, Z3_OP_FINITE_SET_INTERSECT == 49155);
STATIC_ASSERT(finite_difference, Z3_OP_FINITE_SET_DIFFERENCE == 49156);
STATIC_ASSERT(finite_in, Z3_OP_FINITE_SET_IN == 49157);
STATIC_ASSERT(finite_size, Z3_OP_FINITE_SET_SIZE == 49158);
STATIC_ASSERT(finite_subset, Z3_OP_FINITE_SET_SUBSET == 49159);
STATIC_ASSERT(finite_map, Z3_OP_FINITE_SET_MAP == 49160);
STATIC_ASSERT(finite_filter, Z3_OP_FINITE_SET_FILTER == 49161);
STATIC_ASSERT(finite_range, Z3_OP_FINITE_SET_RANGE == 49162);
STATIC_ASSERT(finite_ext, Z3_OP_FINITE_SET_EXT == 49163);
STATIC_ASSERT(finite_inverse, Z3_OP_FINITE_SET_MAP_INVERSE == 49164);
STATIC_ASSERT(internal_tail, Z3_OP_INTERNAL == 49165);
STATIC_ASSERT(recursive_tail, Z3_OP_RECURSIVE == 49166);
STATIC_ASSERT(uninterpreted_tail, Z3_OP_UNINTERPRETED == 49167);

static int check_app(Z3_context c, Z3_ast ast, unsigned kind) {
    if (ast == 0) {
        return 0;
    }
    Z3_func_decl decl = Z3_get_app_decl(c, Z3_to_app(c, ast));
    return decl != NULL && Z3_get_decl_kind(c, decl) == kind;
}

int main(void) {
    Z3_config cfg = Z3_mk_config();
    if (cfg == NULL) {
        fputs("finite-set consumer could not create a configuration\n", stderr);
        return 1;
    }
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    if (c == NULL) {
        fputs("finite-set consumer could not create a context\n", stderr);
        return 1;
    }
    Z3_sort integer = Z3_mk_int_sort(c);
    Z3_sort finite = Z3_mk_finite_set_sort(c, integer);
    Z3_ast one = Z3_mk_int(c, 1, integer);
    Z3_ast three = Z3_mk_int(c, 3, integer);
    Z3_ast seven = Z3_mk_int(c, 7, integer);
    Z3_ast empty = Z3_mk_finite_set_empty(c, finite);
    Z3_ast singleton = Z3_mk_finite_set_singleton(c, one);
    Z3_ast union_ = Z3_mk_finite_set_union(c, singleton, empty);
    Z3_ast intersect = Z3_mk_finite_set_intersect(c, singleton, empty);
    Z3_ast difference = Z3_mk_finite_set_difference(c, singleton, empty);
    Z3_ast member = Z3_mk_finite_set_member(c, one, singleton);
    Z3_ast size = Z3_mk_finite_set_size(c, singleton);
    Z3_ast subset = Z3_mk_finite_set_subset(c, empty, singleton);
    Z3_ast function = Z3_mk_const_array(c, integer, seven);
    Z3_ast map = Z3_mk_finite_set_map(c, function, singleton);
    Z3_ast predicate = Z3_mk_const_array(c, integer, Z3_mk_true(c));
    Z3_ast filter = Z3_mk_finite_set_filter(c, predicate, singleton);
    Z3_ast range = Z3_mk_finite_set_range(c, one, three);
    Z3_sort nested = Z3_mk_finite_set_sort(c, finite);
    Z3_ast nested_source = Z3_mk_finite_set_singleton(c, empty);

    Z3_symbol function_symbol = Z3_mk_string_symbol(c, "finite_identity");
    Z3_sort function_domain[] = {finite};
    Z3_func_decl finite_identity =
        Z3_mk_func_decl(c, function_symbol, 1, function_domain, finite);
    Z3_ast function_array = Z3_mk_as_array(c, finite_identity);
    Z3_ast mapped_function =
        Z3_mk_finite_set_map(c, function_array, nested_source);
    Z3_symbol predicate_symbol = Z3_mk_string_symbol(c, "finite_predicate");
    Z3_func_decl finite_predicate = Z3_mk_func_decl(
        c, predicate_symbol, 1, function_domain, Z3_mk_bool_sort(c));
    Z3_ast predicate_array = Z3_mk_as_array(c, finite_predicate);
    Z3_ast filtered_function =
        Z3_mk_finite_set_filter(c, predicate_array, nested_source);

    Z3_symbol bound_name = Z3_mk_string_symbol(c, "x");
    Z3_sort bound_sorts[] = {finite};
    Z3_symbol bound_names[] = {bound_name};
    Z3_ast bound = Z3_mk_bound(c, 0, finite);
    Z3_ast lambda =
        Z3_mk_lambda(c, 1, bound_sorts, bound_names, bound);
    Z3_ast mapped_lambda = Z3_mk_finite_set_map(c, lambda, nested_source);
    Z3_ast predicate_lambda =
        Z3_mk_lambda(c, 1, bound_sorts, bound_names, Z3_mk_true(c));
    Z3_ast filtered_lambda =
        Z3_mk_finite_set_filter(c, predicate_lambda, nested_source);

    Z3_symbol bound_const_name = Z3_mk_string_symbol(c, "bound_set");
    Z3_ast bound_const = Z3_mk_const(c, bound_const_name, finite);
    Z3_app bound_apps[] = {Z3_to_app(c, bound_const)};
    Z3_ast lambda_const =
        Z3_mk_lambda_const(c, 1, bound_apps, bound_const);

    Z3_ast finite_indexed_array = Z3_mk_const_array(c, finite, one);
    Z3_ast array_default = Z3_mk_array_default(c, finite_indexed_array);
    Z3_ast array_ext =
        Z3_mk_array_ext(c, finite_indexed_array, finite_indexed_array);

    const char* parsed_script =
        "(declare-const parsed_s (FiniteSet Int))"
        "(declare-fun parsed_f ((FiniteSet Int)) (FiniteSet Int))"
        "(assert (= parsed_s (as set.empty (FiniteSet Int))))"
        "(assert (= (parsed_f (as set.empty (FiniteSet Int)))"
        "           (as set.empty (FiniteSet Int))))";
    Z3_ast_vector parsed =
        Z3_parse_smtlib2_string(c, parsed_script, 0, NULL, NULL, 0, NULL, NULL);
    Z3_ast_vector_inc_ref(c, parsed);
    Z3_ast parsed_assertion =
        Z3_ast_vector_size(c, parsed) == 2 ? Z3_ast_vector_get(c, parsed, 0) : 0;
    Z3_ast parsed_function_assertion =
        Z3_ast_vector_size(c, parsed) == 2 ? Z3_ast_vector_get(c, parsed, 1) : 0;
    Z3_app parsed_assertion_app =
        parsed_assertion != 0 ? Z3_to_app(c, parsed_assertion) : (Z3_app)0;
    Z3_ast parsed_empty =
        parsed_assertion_app != (Z3_app)0
                && Z3_get_app_num_args(c, parsed_assertion_app) == 2
            ? Z3_get_app_arg(c, parsed_assertion_app, 1)
            : 0;
    Z3_app parsed_function_assertion_app =
        parsed_function_assertion != 0
            ? Z3_to_app(c, parsed_function_assertion)
            : (Z3_app)0;
    Z3_ast parsed_function_app =
        parsed_function_assertion_app != (Z3_app)0
                && Z3_get_app_num_args(c, parsed_function_assertion_app) == 2
            ? Z3_get_app_arg(c, parsed_function_assertion_app, 0)
            : 0;
    Z3_func_decl parsed_function_decl =
        parsed_function_app != 0
            ? Z3_get_app_decl(c, Z3_to_app(c, parsed_function_app))
            : NULL;
    int ok = finite != NULL;

    CHECK(Z3_is_finite_set_sort(c, finite));
    CHECK(Z3_is_eq_sort(c, Z3_get_finite_set_sort_basis(c, finite), integer));
    CHECK(Z3_get_sort_kind(c, finite) == Z3_UNKNOWN_SORT);
    CHECK(strcmp(Z3_sort_to_string(c, finite), "(FiniteSet Int)") == 0);
    CHECK(check_app(c, empty, Z3_OP_FINITE_SET_EMPTY));
    CHECK(check_app(c, singleton, Z3_OP_FINITE_SET_SINGLETON));
    CHECK(check_app(c, union_, Z3_OP_FINITE_SET_UNION));
    CHECK(check_app(c, intersect, Z3_OP_FINITE_SET_INTERSECT));
    CHECK(check_app(c, difference, Z3_OP_FINITE_SET_DIFFERENCE));
    CHECK(check_app(c, member, Z3_OP_FINITE_SET_IN));
    CHECK(check_app(c, size, Z3_OP_FINITE_SET_SIZE));
    CHECK(check_app(c, subset, Z3_OP_FINITE_SET_SUBSET));
    CHECK(check_app(c, map, Z3_OP_FINITE_SET_MAP));
    CHECK(check_app(c, filter, Z3_OP_FINITE_SET_FILTER));
    CHECK(check_app(c, range, Z3_OP_FINITE_SET_RANGE));
    CHECK(check_app(c, mapped_function, Z3_OP_FINITE_SET_MAP));
    CHECK(check_app(c, filtered_function, Z3_OP_FINITE_SET_FILTER));
    CHECK(check_app(c, mapped_lambda, Z3_OP_FINITE_SET_MAP));
    CHECK(check_app(c, filtered_lambda, Z3_OP_FINITE_SET_FILTER));
    CHECK(strcmp(Z3_ast_to_string(c, empty),
                 "(as set.empty (FiniteSet Int))") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, function_array)),
                 "(Array (FiniteSet Int) (FiniteSet Int))") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, mapped_function)),
                 "(FiniteSet (FiniteSet Int))") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, predicate_array)),
                 "(Array (FiniteSet Int) Bool)") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, lambda)),
                 "(Array (FiniteSet Int) (FiniteSet Int))") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, lambda_const)),
                 "(Array (FiniteSet Int) (FiniteSet Int))") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, predicate_lambda)),
                 "(Array (FiniteSet Int) Bool)") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, nested),
                 "(FiniteSet (FiniteSet Int))") == 0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, array_default)), "Int") ==
          0);
    CHECK(strcmp(Z3_sort_to_string(c, Z3_get_sort(c, array_ext)),
                 "(FiniteSet Int)") == 0);
    CHECK(parsed_assertion != 0);
    CHECK(strcmp(Z3_ast_to_string(c, parsed_assertion),
                 "(= parsed_s (as set.empty (FiniteSet Int)))") == 0);
    CHECK(parsed_empty != 0);
    CHECK(Z3_is_eq_sort(c, Z3_get_sort(c, parsed_empty), finite));
    CHECK(check_app(c, parsed_empty, Z3_OP_FINITE_SET_EMPTY));
    CHECK(parsed_function_app != 0);
    CHECK(strcmp(Z3_ast_to_string(c, parsed_function_app),
                 "(parsed_f (as set.empty (FiniteSet Int)))") == 0);
    CHECK(parsed_function_decl != NULL);
    CHECK(Z3_get_domain_size(c, parsed_function_decl) == 1);
    CHECK(Z3_is_eq_sort(c, Z3_get_domain(c, parsed_function_decl, 0), finite));
    CHECK(Z3_is_eq_sort(c, Z3_get_range(c, parsed_function_decl), finite));

    Z3_func_decl empty_decl = Z3_get_app_decl(c, Z3_to_app(c, empty));
    CHECK(Z3_get_decl_num_parameters(c, empty_decl) == 1);
    CHECK(Z3_get_decl_parameter_kind(c, empty_decl, 0) == Z3_PARAMETER_SORT);
    CHECK(Z3_is_eq_sort(c, Z3_get_decl_sort_parameter(c, empty_decl, 0),
                        finite));

    Z3_ast_vector_dec_ref(c, parsed);
    Z3_del_context(c);
    if (!ok) {
        fputs("finite-set consumer failed\n", stderr);
        return 1;
    }
    puts("finite-set consumer tests passed");
    return 0;
}
