// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("substitution.rewriting.context-created", c != NULL);
    Z3_sort integer = parsing_sort(c, Z3_mk_int_sort(c));
    CHECK("substitution.rewriting.sort-created", integer != NULL);
    Z3_ast x = parsing_hold(c, Z3_mk_const(c, Z3_mk_string_symbol(c, "rewrite_x"), integer));
    Z3_ast y = parsing_hold(c, Z3_mk_const(c, Z3_mk_string_symbol(c, "rewrite_y"), integer));
    Z3_ast one = parsing_hold(c, Z3_mk_int(c, 1, integer));
    Z3_ast two = parsing_hold(c, Z3_mk_int(c, 2, integer));
    Z3_ast seven = parsing_hold(c, Z3_mk_int(c, 7, integer));
    CHECK("substitution.rewriting.atoms-created", x && y && one && two && seven);
    Z3_ast args[2] = {x, y};
    Z3_ast difference = parsing_hold(c, Z3_mk_sub(c, 2, args));
    CHECK("substitution.rewriting.setup", integer && x && y && one && two && seven && difference);
    Z3_ast new_args[2] = {seven, two};
    Z3_ast updated = parsing_hold(c, Z3_update_term(c, difference, 2, new_args));
    CHECK("substitution.rewriting.update-arguments-preserves-operator", updated &&
          Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, updated))) == Z3_OP_SUB &&
          parsing_integer_is(c, updated, 5) && !parsing_integer_is(c, updated, -5));
    CHECK("substitution.rewriting.original-term-unchanged", Z3_is_eq_ast(c, Z3_get_app_arg(c, Z3_to_app(c, difference), 0), x) &&
          Z3_is_eq_ast(c, Z3_get_app_arg(c, Z3_to_app(c, difference), 1), y));
    Z3_ast identical = parsing_hold(c, Z3_update_term(c, difference, 2, args));
    CHECK("substitution.rewriting.identical-update-preserves-identity", identical && Z3_is_eq_ast(c, identical, difference));
    /* api_ast.cpp checks arity and returns the original term with Z3_IOB. */
    contract_last_error = Z3_OK;
    Z3_ast rejected = Z3_update_term(c, difference, 1, new_args);
    Z3_error_code update_error = Z3_get_error_code(c);
    Z3_error_code callback_error = contract_last_error;
    rejected = parsing_hold(c, rejected);
    CHECK("substitution.rewriting.wrong-arity-refused", rejected && update_error == Z3_IOB && callback_error == Z3_IOB &&
          Z3_is_eq_ast(c, rejected, difference));
    Z3_ast recovered = parsing_hold(c, Z3_update_term(c, difference, 2, new_args));
    CHECK("substitution.rewriting.valid-update-recovers", recovered && Z3_get_error_code(c) == Z3_OK && parsing_integer_is(c, recovered, 5));
    Z3_ast plus_x_args[2] = {x, one}, plus_y_args[2] = {y, two};
    Z3_ast plus_x = parsing_hold(c, Z3_mk_add(c, 2, plus_x_args));
    Z3_ast plus_y = parsing_hold(c, Z3_mk_add(c, 2, plus_y_args));
    CHECK("substitution.rewriting.factors-created", plus_x && plus_y);
    Z3_ast factors[2] = {plus_x, plus_y};
    Z3_ast polynomial = parsing_hold(c, Z3_mk_mul(c, 2, factors));
    Z3_params factored_parameters = Z3_mk_params(c);
    if (factored_parameters) Z3_params_inc_ref(c, factored_parameters);
    Z3_params expanded_parameters = Z3_mk_params(c);
    if (expanded_parameters) Z3_params_inc_ref(c, expanded_parameters);
    CHECK("substitution.rewriting.parameters-created", polynomial && factored_parameters && expanded_parameters);
    Z3_symbol som = Z3_mk_string_symbol(c, "som");
    Z3_params_set_bool(c, factored_parameters, som, false);
    Z3_params_set_bool(c, expanded_parameters, som, true);
    Z3_ast factored = parsing_hold(c, Z3_simplify_ex(c, polynomial, factored_parameters));
    Z3_ast expanded = parsing_hold(c, Z3_simplify_ex(c, polynomial, expanded_parameters));
    Z3_params_dec_ref(c, expanded_parameters); Z3_params_dec_ref(c, factored_parameters);
    CHECK("substitution.rewriting.sum-of-monomials-parameter-effect", factored && expanded &&
          Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, factored))) == Z3_OP_MUL &&
          Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, expanded))) == Z3_OP_ADD &&
          !Z3_is_eq_ast(c, factored, expanded));
    int values_correct = 1;
    Z3_ast from[2] = {x, y};
    for (int xv = -2; xv <= 2; ++xv) for (int yv = -2; yv <= 2; ++yv) {
        Z3_ast values[2] = {parsing_hold(c, Z3_mk_int(c, xv, integer)), parsing_hold(c, Z3_mk_int(c, yv, integer))};
        if (!values[0] || !values[1]) { values_correct = 0; continue; }
        Z3_ast first = parsing_hold(c, Z3_substitute(c, factored, 2, from, values));
        Z3_ast second = parsing_hold(c, Z3_substitute(c, expanded, 2, from, values));
        int expected = (xv + 1) * (yv + 2);
        values_correct &= parsing_integer_is(c, first, expected) && parsing_integer_is(c, second, expected);
    }
    CHECK("substitution.rewriting.parameter-results-preserve-25-values", values_correct);
    Z3_ast same = parsing_hold(c, Z3_mk_eq(c, factored, expanded));
    CHECK("substitution.rewriting.equivalence-created", same != NULL);
    Z3_ast different = parsing_hold(c, Z3_mk_not(c, same));
    CHECK("substitution.rewriting.symbolic-parameter-equivalence", different && parsing_solver_is(c, different, Z3_L_FALSE));
    Z3_ast five = parsing_hold(c, Z3_mk_int(c, 5, integer));
    CHECK("substitution.rewriting.ground-value-created", five != NULL);
    Z3_ast equal_ground = parsing_hold(c, Z3_mk_eq(c, updated, five));
    CHECK("substitution.rewriting.ground-equality-created", equal_ground != NULL);
    Z3_ast truth = parsing_hold(c, Z3_simplify(c, equal_ground));
    CHECK("substitution.rewriting.default-ground-simplification", truth && Z3_get_bool_value(c, truth) == Z3_L_TRUE);
    parsing_release(c); Z3_del_context(c);
    return 0;
}
