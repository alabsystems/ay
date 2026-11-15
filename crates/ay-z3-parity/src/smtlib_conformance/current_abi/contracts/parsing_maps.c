// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("parsing.maps.context-created", c != NULL);
    Z3_sort integer = parsing_sort(c, Z3_mk_int_sort(c));
    Z3_sort opaque = parsing_sort(c, Z3_mk_uninterpreted_sort(c, Z3_mk_string_symbol(c, "ActualOpaque")));
    CHECK("parsing.maps.sorts-created", integer && opaque);
    Z3_func_decl x_decl = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "actual_x"), 0, NULL, integer);
    if (x_decl) parsing_hold(c, Z3_func_decl_to_ast(c, x_decl));
    Z3_sort domain[1] = {integer};
    Z3_func_decl f_decl = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "actual_f"), 1, domain, integer);
    if (f_decl) parsing_hold(c, Z3_func_decl_to_ast(c, f_decl));
    CHECK("parsing.maps.declarations-created", x_decl && f_decl);
    Z3_ast x = parsing_hold(c, Z3_mk_app(c, x_decl, 0, NULL));
    Z3_ast seven = parsing_hold(c, Z3_mk_int(c, 7, integer));
    CHECK("parsing.maps.external-terms-created", x && seven);
    Z3_ast expected_x7 = parsing_hold(c, Z3_mk_eq(c, x, seven));
    CHECK("parsing.maps.external-symbols-created", integer && opaque && x_decl && f_decl && x && seven && expected_x7);
    Z3_symbol sort_names[2] = {Z3_mk_string_symbol(c, "AliasInt"), Z3_mk_string_symbol(c, "AliasOpaque")};
    Z3_sort sorts[2] = {integer, opaque};
    Z3_symbol decl_names[2] = {Z3_mk_string_symbol(c, "supplied_x"), Z3_mk_string_symbol(c, "supplied_f")};
    Z3_func_decl decls[2] = {x_decl, f_decl};
    const char *input =
        "(declare-const local AliasInt)\n"
        "(declare-const u AliasOpaque)\n"
        "(assert (= supplied_x 7))\n"
        "(push 1)\n(assert false)\n(pop 1)\n"
        "(assert (= (supplied_f supplied_x) local))\n"
        "(assert (= u u))\n";
    Z3_ast_vector parsed = Z3_parse_smtlib2_string(c, input, 2, sort_names, sorts, 2, decl_names, decls);
    Z3_error_code parse_error = Z3_get_error_code(c);
    if (parsed) Z3_ast_vector_inc_ref(c, parsed);
    CHECK("parsing.maps.active-assertion-scope", parsed && parse_error == Z3_OK && Z3_ast_vector_size(c, parsed) == 3);
    Z3_ast first = parsing_hold(c, Z3_ast_vector_get(c, parsed, 0));
    Z3_ast second = parsing_hold(c, Z3_ast_vector_get(c, parsed, 1));
    Z3_ast third = parsing_hold(c, Z3_ast_vector_get(c, parsed, 2));
    CHECK("parsing.maps.declaration-alias-identity", first && second && third && Z3_is_eq_ast(c, first, expected_x7) &&
          Z3_get_app_num_args(c, Z3_to_app(c, second)) == 2);
    Z3_ast application = parsing_hold(c, Z3_get_app_arg(c, Z3_to_app(c, second), 0));
    Z3_ast local = parsing_hold(c, Z3_get_app_arg(c, Z3_to_app(c, second), 1));
    Z3_ast opaque_value = parsing_hold(c, Z3_get_app_arg(c, Z3_to_app(c, third), 0));
    CHECK("parsing.maps.function-and-sort-map", application && local && opaque_value &&
          Z3_is_eq_func_decl(c, Z3_get_app_decl(c, Z3_to_app(c, application)), f_decl) &&
          Z3_is_eq_ast(c, Z3_get_app_arg(c, Z3_to_app(c, application), 0), x) &&
          Z3_is_eq_sort(c, Z3_get_sort(c, local), integer) && Z3_is_eq_sort(c, Z3_get_sort(c, opaque_value), opaque));
    Z3_solver solver = Z3_mk_solver(c); if (solver) Z3_solver_inc_ref(c, solver);
    CHECK("parsing.maps.solver-created", solver != NULL);
    for (unsigned index = 0; index < 3; ++index) Z3_solver_assert(c, solver, Z3_ast_vector_get(c, parsed, index));
    CHECK("parsing.maps.mapped-assertions-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model model = Z3_solver_get_model(c, solver); if (model) Z3_model_inc_ref(c, model);
    Z3_ast value = NULL;
    int evaluated = model && Z3_model_eval(c, model, x, false, &value);
    if (evaluated) value = parsing_hold(c, value);
    CHECK("parsing.maps.model-uses-external-declaration", evaluated && parsing_integer_is(c, value, 7) && !parsing_integer_is(c, value, 8));
    Z3_ast negation = parsing_hold(c, Z3_mk_not(c, first));
    CHECK("parsing.maps.returned-assertions-have-semantic-force", negation && parsing_solver_is(c, first, Z3_L_TRUE));
    Z3_solver_assert(c, solver, negation);
    CHECK("parsing.maps.complementary-assertion-refused", Z3_solver_check(c, solver) == Z3_L_FALSE);
    contract_last_error = Z3_OK;
    /* The default parser admits Boolean/integer coercions. An array and a
       Boolean have incompatible sorts even under those parser extensions. */
    Z3_ast_vector bad = Z3_parse_smtlib2_string(c, "(assert (= ((as const (Array Int Int)) 0) true))", 0, NULL, NULL, 0, NULL, NULL);
    Z3_error_code bad_error = Z3_get_error_code(c);
    Z3_error_code callback_error = contract_last_error;
    if (bad) Z3_ast_vector_inc_ref(c, bad);
    CHECK("parsing.maps.sort-error-refused", bad && bad_error == Z3_PARSER_ERROR && callback_error == Z3_PARSER_ERROR && Z3_ast_vector_size(c, bad) == 0);
    contract_last_error = Z3_OK;
    Z3_ast_vector foreign = Z3_parse_smtlib2_string(c, "(assert (= local 7))", 0, NULL, NULL, 0, NULL, NULL);
    Z3_error_code foreign_error = Z3_get_error_code(c);
    if (foreign) Z3_ast_vector_inc_ref(c, foreign);
    CHECK("parsing.maps.declarations-do-not-leak-between-calls", foreign && foreign_error == Z3_PARSER_ERROR && contract_last_error == Z3_PARSER_ERROR);
    Z3_ast_vector recovered = Z3_parse_smtlib2_string(c, "(assert true)", 0, NULL, NULL, 0, NULL, NULL);
    Z3_error_code recovered_error = Z3_get_error_code(c);
    if (recovered) Z3_ast_vector_inc_ref(c, recovered);
    CHECK("parsing.maps.valid-parse-recovers", recovered && recovered_error == Z3_OK && Z3_ast_vector_size(c, recovered) == 1 &&
          Z3_get_bool_value(c, Z3_ast_vector_get(c, recovered, 0)) == Z3_L_TRUE);
    Z3_ast_vector_dec_ref(c, recovered); Z3_ast_vector_dec_ref(c, foreign); Z3_ast_vector_dec_ref(c, bad);
    Z3_solver_dec_ref(c, solver);
    Z3_ast retained_value = NULL;
    int retained_evaluated = Z3_model_eval(c, model, x, false, &retained_value);
    if (retained_evaluated) retained_value = parsing_hold(c, retained_value);
    CHECK("parsing.maps.retained-vector-after-errors-and-solver-release", Z3_ast_vector_size(c, parsed) == 3 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, parsed, 0), expected_x7) && retained_evaluated && parsing_integer_is(c, retained_value, 7));
    Z3_model_dec_ref(c, model);
    Z3_ast_vector_dec_ref(c, parsed);
    parsing_release(c); Z3_del_context(c);
    return 0;
}
