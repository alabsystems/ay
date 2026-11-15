// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static void ad_hold_decl(Z3_context c, Z3_func_decl decl) {
    if (decl) HOLD(c, Z3_func_decl_to_ast(c, decl));
}

static int ad_decl_named(Z3_context c, Z3_func_decl decl, const char *expected) {
    if (!decl) return 0;
    Z3_symbol name = Z3_get_decl_name(c, decl);
    if (Z3_get_symbol_kind(c, name) != Z3_STRING_SYMBOL) return 0;
    const char *actual = Z3_get_symbol_string(c, name);
    return actual && strcmp(actual, expected) == 0;
}

static int ad_simplified_bool(Z3_context c, Z3_ast term, Z3_lbool expected) {
    if (!term) return 0;
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    if (!value) return 0;
    int correct = Z3_get_bool_value(c, value) == expected;
    Z3_dec_ref(c, value);
    return correct && Z3_get_error_code(c) == Z3_OK;
}

static int ad_simplified_same(Z3_context c, Z3_ast term, Z3_ast expected) {
    if (!term || !expected) return 0;
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    if (!value) return 0;
    int correct = Z3_is_eq_ast(c, value, expected);
    Z3_dec_ref(c, value);
    return correct && Z3_get_error_code(c) == Z3_OK;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("datatypes.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_symbol field_names[2] = {
        Z3_mk_string_symbol(c, "contract_list_head"), Z3_mk_string_symbol(c, "contract_list_tail")
    };
    Z3_sort field_sorts[2] = {integer, NULL};
    unsigned sort_refs[2] = {0, 0};
    Z3_constructor nil_container = Z3_mk_constructor(c,
        Z3_mk_string_symbol(c, "contract_list_nil"), Z3_mk_string_symbol(c, "contract_list_is_nil"),
        0, NULL, NULL, NULL);
    Z3_constructor cons_container = Z3_mk_constructor(c,
        Z3_mk_string_symbol(c, "contract_list_cons"), Z3_mk_string_symbol(c, "contract_list_is_cons"),
        2, field_names, field_sorts, sort_refs);
    CHECK("datatypes.constructor-containers", integer && nil_container && cons_container &&
          Z3_constructor_num_fields(c, nil_container) == 0 &&
          Z3_constructor_num_fields(c, cons_container) == 2);
    /* A null field sort with sort_refs[i] == 0 refers to this datatype. */
    Z3_constructor containers[2] = {nil_container, cons_container};
    Z3_sort list = Z3_mk_datatype(c, Z3_mk_string_symbol(c, "contract_int_list"), 2, containers);
    HOLD_SORT(c, list);
    CHECK("datatypes.recursive-sort", list && Z3_get_sort_kind(c, list) == Z3_DATATYPE_SORT &&
          Z3_is_recursive_datatype_sort(c, list) && Z3_get_datatype_sort_num_constructors(c, list) == 2);
    Z3_func_decl nil_decl = NULL, is_nil_decl = NULL;
    Z3_query_constructor(c, nil_container, 0, &nil_decl, &is_nil_decl, NULL);
    ad_hold_decl(c, nil_decl); ad_hold_decl(c, is_nil_decl);
    Z3_func_decl cons_decl = NULL, is_cons_decl = NULL, accessors[2] = {NULL, NULL};
    Z3_query_constructor(c, cons_container, 2, &cons_decl, &is_cons_decl, accessors);
    ad_hold_decl(c, cons_decl); ad_hold_decl(c, is_cons_decl);
    ad_hold_decl(c, accessors[0]); ad_hold_decl(c, accessors[1]);
    CHECK("datatypes.queried-declarations", nil_decl && is_nil_decl && cons_decl && is_cons_decl &&
          accessors[0] && accessors[1] && ad_decl_named(c, nil_decl, "contract_list_nil") &&
          ad_decl_named(c, cons_decl, "contract_list_cons") &&
          ad_decl_named(c, accessors[0], "contract_list_head") &&
          ad_decl_named(c, accessors[1], "contract_list_tail"));
    Z3_del_constructor(c, nil_container);
    Z3_del_constructor(c, cons_container);
    CHECK("datatypes.reflection-after-container-release",
          Z3_is_eq_func_decl(c, nil_decl, Z3_get_datatype_sort_constructor(c, list, 0)) &&
          Z3_is_eq_func_decl(c, cons_decl, Z3_get_datatype_sort_constructor(c, list, 1)) &&
          Z3_is_eq_func_decl(c, is_nil_decl, Z3_get_datatype_sort_recognizer(c, list, 0)) &&
          Z3_is_eq_func_decl(c, is_cons_decl, Z3_get_datatype_sort_recognizer(c, list, 1)) &&
          Z3_is_eq_func_decl(c, accessors[0], Z3_get_datatype_sort_constructor_accessor(c, list, 1, 0)) &&
          Z3_is_eq_func_decl(c, accessors[1], Z3_get_datatype_sort_constructor_accessor(c, list, 1, 1)));
    CHECK("datatypes.declaration-sorts", Z3_get_domain_size(c, nil_decl) == 0 &&
          Z3_get_domain_size(c, cons_decl) == 2 &&
          Z3_is_eq_sort(c, Z3_get_range(c, cons_decl), list) &&
          Z3_is_eq_sort(c, Z3_get_domain(c, cons_decl, 0), integer) &&
          Z3_is_eq_sort(c, Z3_get_domain(c, cons_decl, 1), list) &&
          Z3_is_eq_sort(c, Z3_get_range(c, accessors[0]), integer) &&
          Z3_is_eq_sort(c, Z3_get_range(c, accessors[1]), list));
    Z3_ast seven = Z3_mk_int(c, 7, integer); HOLD(c, seven);
    Z3_ast nine = Z3_mk_int(c, 9, integer); HOLD(c, nine);
    Z3_ast nil = Z3_mk_app(c, nil_decl, 0, NULL); HOLD(c, nil);
    Z3_ast seven_args[2] = {seven, nil};
    Z3_ast cons_seven = Z3_mk_app(c, cons_decl, 2, seven_args); HOLD(c, cons_seven);
    Z3_ast nine_args[2] = {nine, nil};
    Z3_ast cons_nine = Z3_mk_app(c, cons_decl, 2, nine_args); HOLD(c, cons_nine);
    Z3_ast is_nil_nil = Z3_mk_app(c, is_nil_decl, 1, &nil); HOLD(c, is_nil_nil);
    Z3_ast is_cons_nil = Z3_mk_app(c, is_cons_decl, 1, &nil); HOLD(c, is_cons_nil);
    Z3_ast is_nil_cons = Z3_mk_app(c, is_nil_decl, 1, &cons_seven); HOLD(c, is_nil_cons);
    Z3_ast is_cons_cons = Z3_mk_app(c, is_cons_decl, 1, &cons_seven); HOLD(c, is_cons_cons);
    CHECK("datatypes.constructor-testers", nil && cons_seven && cons_nine &&
          ad_simplified_bool(c, is_nil_nil, Z3_L_TRUE) &&
          ad_simplified_bool(c, is_cons_nil, Z3_L_FALSE) &&
          ad_simplified_bool(c, is_nil_cons, Z3_L_FALSE) &&
          ad_simplified_bool(c, is_cons_cons, Z3_L_TRUE));
    Z3_ast head = Z3_mk_app(c, accessors[0], 1, &cons_seven); HOLD(c, head);
    Z3_ast tail = Z3_mk_app(c, accessors[1], 1, &cons_seven); HOLD(c, tail);
    CHECK("datatypes.constructor-accessors", ad_simplified_int(c, head, 7) &&
          ad_simplified_same(c, tail, nil));
    Z3_ast nested_args[2] = {nine, cons_seven};
    Z3_ast nested = Z3_mk_app(c, cons_decl, 2, nested_args); HOLD(c, nested);
    Z3_ast nested_tail = Z3_mk_app(c, accessors[1], 1, &nested); HOLD(c, nested_tail);
    Z3_ast nested_head = Z3_mk_app(c, accessors[0], 1, &nested_tail); HOLD(c, nested_head);
    CHECK("datatypes.recursive-accessors", ad_simplified_same(c, nested_tail, cons_seven) &&
          ad_simplified_int(c, nested_head, 7));
    Z3_solver solver = Z3_mk_solver(c); if (solver) Z3_solver_inc_ref(c, solver);
    Z3_ast nil_is_cons = Z3_mk_eq(c, nil, cons_seven); HOLD(c, nil_is_cons);
    Z3_ast different_heads_equal = Z3_mk_eq(c, cons_seven, cons_nine); HOLD(c, different_heads_equal);
    CHECK("datatypes.disjoint-constructors", ad_unsatisfiable(c, solver, nil_is_cons));
    CHECK("datatypes.injective-constructor", ad_unsatisfiable(c, solver, different_heads_equal));
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "contract_list_x"), list); HOLD(c, x);
    Z3_ast occurs_args[2] = {seven, x};
    Z3_ast containing_x = Z3_mk_app(c, cons_decl, 2, occurs_args); HOLD(c, containing_x);
    Z3_ast cycle = Z3_mk_eq(c, x, containing_x); HOLD(c, cycle);
    CHECK("datatypes.occurs-check", ad_unsatisfiable(c, solver, cycle));
    Z3_ast x_is_cons_seven = Z3_mk_eq(c, x, cons_seven); HOLD(c, x_is_cons_seven);
    Z3_ast x_is_nil = Z3_mk_eq(c, x, nil); HOLD(c, x_is_nil);
    Z3_ast x_head = Z3_mk_app(c, accessors[0], 1, &x); HOLD(c, x_head);
    Z3_ast x_tail = Z3_mk_app(c, accessors[1], 1, &x); HOLD(c, x_tail);
    Z3_ast x_tail_is_nil = Z3_mk_eq(c, x_tail, nil); HOLD(c, x_tail_is_nil);
    Z3_ast x_is_cons = Z3_mk_app(c, is_cons_decl, 1, &x); HOLD(c, x_is_cons);
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, x_is_cons_seven);
    CHECK("datatypes.concrete-model-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model model = Z3_solver_get_model(c, solver); if (model) Z3_model_inc_ref(c, model);
    CHECK("datatypes.model-observations", model && ad_model_int(c, model, x_head, 7) &&
          ad_model_bool(c, model, x_tail_is_nil, Z3_L_TRUE) &&
          ad_model_bool(c, model, x_is_cons, Z3_L_TRUE) &&
          ad_model_bool(c, model, x_is_nil, Z3_L_FALSE));
    Z3_solver_assert(c, solver, x_is_nil);
    CHECK("datatypes.retained-model-after-contradiction", Z3_solver_check(c, solver) == Z3_L_FALSE &&
          ad_model_int(c, model, x_head, 7));
    unsigned retained_id = Z3_get_ast_id(c, cons_seven);
    Z3_solver_dec_ref(c, solver);
    CHECK("datatypes.retained-model-after-solver-release", Z3_get_ast_id(c, cons_seven) == retained_id &&
          ad_simplified_int(c, head, 7) && ad_model_int(c, model, x_head, 7) &&
          ad_model_bool(c, model, x_tail_is_nil, Z3_L_TRUE) &&
          Z3_get_error_code(c) == Z3_OK && contract_last_error == Z3_OK);
    Z3_model_dec_ref(c, model);
    Z3_del_context(c);
    return 0;
}
