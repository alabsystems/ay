// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline int opt_model_integer(Z3_context c, Z3_model model, Z3_ast term, int *result) {
    Z3_ast value = NULL;
    if (!model || !term || !Z3_model_eval(c, model, term, false, &value) || !value) return 0;
    HOLD(c, value);
    int correct = Z3_get_numeral_int(c, value, result);
    Z3_dec_ref(c, value);
    return correct;
}

static inline int opt_priority(Z3_context c, Z3_optimize o, const char *priority) {
    Z3_params p = Z3_mk_params(c);
    if (!p) return 0;
    Z3_params_inc_ref(c, p);
    Z3_params_set_symbol(c, p, Z3_mk_string_symbol(c, "priority"),
                         Z3_mk_string_symbol(c, priority));
    Z3_optimize_set_params(c, o, p);
    int correct = Z3_get_error_code(c) == Z3_OK;
    Z3_params_dec_ref(c, p);
    return correct;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("optimize.priorities.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_sort boolean = Z3_mk_bool_sort(c); HOLD_SORT(c, boolean);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "priority_x"), integer); HOLD(c, x);
    Z3_ast y = Z3_mk_const(c, Z3_mk_string_symbol(c, "priority_y"), integer); HOLD(c, y);
    Z3_ast zero = opt_integer(c, integer, 0), two = opt_integer(c, integer, 2);
    Z3_ast terms[2] = {x, y};
    Z3_ast sum = Z3_mk_add(c, 2, terms); HOLD(c, sum);
    Z3_ast cap = Z3_mk_le(c, sum, two); HOLD(c, cap);
    CHECK("optimize.priorities.setup", integer && boolean && x && y && zero && two && sum && cap);
    Z3_optimize first = opt_create(c), reversed = opt_create(c), pareto = opt_create(c);
    CHECK("optimize.priorities.independent-owners", first && reversed && pareto &&
          opt_priority(c, first, "lex") && opt_priority(c, reversed, "lex") &&
          opt_priority(c, pareto, "pareto") &&
          opt_range(c, first, x, zero, two) && opt_range(c, first, y, zero, two) &&
          opt_range(c, reversed, x, zero, two) && opt_range(c, reversed, y, zero, two) &&
          opt_range(c, pareto, x, zero, two) && opt_range(c, pareto, y, zero, two));
    Z3_optimize_assert(c, first, cap); Z3_optimize_assert(c, reversed, cap); Z3_optimize_assert(c, pareto, cap);
    unsigned first_x = Z3_optimize_maximize(c, first, x), first_y = Z3_optimize_maximize(c, first, y);
    unsigned reverse_y = Z3_optimize_maximize(c, reversed, y), reverse_x = Z3_optimize_maximize(c, reversed, x);
    unsigned pareto_x = Z3_optimize_maximize(c, pareto, x), pareto_y = Z3_optimize_maximize(c, pareto, y);
    CHECK("optimize.priorities.lex-first-objective", Z3_optimize_check(c, first, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, first, first_x, 2, 1) && opt_bounds_are(c, first, first_y, 0, 1));
    Z3_model first_model = opt_model(c, first);
    CHECK("optimize.priorities.lex-reversed-objectives", Z3_optimize_check(c, reversed, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, reversed, reverse_y, 2, 1) && opt_bounds_are(c, reversed, reverse_x, 0, 1) &&
          opt_model_rational_is(c, first_model, x, 2, 1) && opt_model_rational_is(c, first_model, y, 0, 1));
    unsigned seen = 0;
    int frontier_valid = 1;
    for (unsigned point = 0; point < 3; ++point) {
        if (Z3_optimize_check(c, pareto, 0, NULL) != Z3_L_TRUE) { frontier_valid = 0; break; }
        Z3_model model = opt_model(c, pareto);
        int xv = -1, yv = -1;
        int valid = opt_model_integer(c, model, x, &xv) && opt_model_integer(c, model, y, &yv) &&
            xv >= 0 && xv <= 2 && yv >= 0 && yv <= 2 && xv + yv == 2 &&
            !(seen & (1u << xv)) && opt_bounds_are(c, pareto, pareto_x, xv, 1) &&
            opt_bounds_are(c, pareto, pareto_y, yv, 1);
        if (model) Z3_model_dec_ref(c, model);
        if (!valid) { frontier_valid = 0; break; }
        seen |= 1u << xv;
    }
    CHECK("optimize.priorities.complete-finite-pareto-front", frontier_valid && seen == 7);
    CHECK("optimize.priorities.pareto-exhaustion", Z3_optimize_check(c, pareto, 0, NULL) == Z3_L_FALSE);
    Z3_ast p = Z3_mk_const(c, Z3_mk_string_symbol(c, "soft_p"), boolean); HOLD(c, p);
    Z3_ast q = Z3_mk_const(c, Z3_mk_string_symbol(c, "soft_q"), boolean); HOLD(c, q);
    Z3_ast xor_pq = Z3_mk_xor(c, p, q); HOLD(c, xor_pq);
    Z3_optimize soft = opt_create(c);
    CHECK("optimize.priorities.soft-setup", p && q && xor_pq && soft && opt_priority(c, soft, "lex"));
    Z3_optimize_assert(c, soft, xor_pq);
    Z3_symbol primary = Z3_mk_string_symbol(c, "primary"), secondary = Z3_mk_string_symbol(c, "secondary");
    unsigned hp = Z3_optimize_assert_soft(c, soft, p, "1/2", primary);
    unsigned hq = Z3_optimize_assert_soft(c, soft, q, "3/2", primary);
    unsigned hs = Z3_optimize_assert_soft(c, soft, p, "2", secondary);
    CHECK("optimize.priorities.soft-group-handles", hp == 0 && hq == hp && hs == 1 &&
          Z3_get_error_code(c) == Z3_OK);
    CHECK("optimize.priorities.rational-soft-group-priority", Z3_optimize_check(c, soft, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, soft, hp, 1, 2) && opt_bounds_are(c, soft, hs, 2, 1));
    Z3_model soft_model = opt_model(c, soft);
    Z3_ast_vector soft_objectives = opt_objectives(c, soft);
    CHECK("optimize.priorities.soft-model-and-objectives", soft_model && soft_objectives &&
          Z3_ast_vector_size(c, soft_objectives) == 2 &&
          opt_model_bool_is(c, soft_model, p, Z3_L_FALSE) && opt_model_bool_is(c, soft_model, q, Z3_L_TRUE) &&
          opt_model_rational_is(c, soft_model, Z3_ast_vector_get(c, soft_objectives, 0), 1, 2) &&
          opt_model_rational_is(c, soft_model, Z3_ast_vector_get(c, soft_objectives, 1), 2, 1));
    Z3_ast_vector_dec_ref(c, soft_objectives); Z3_model_dec_ref(c, soft_model);
    Z3_optimize_dec_ref(c, soft); Z3_dec_ref(c, xor_pq); Z3_dec_ref(c, q); Z3_dec_ref(c, p);
    Z3_model_dec_ref(c, first_model);
    Z3_optimize_dec_ref(c, pareto); Z3_optimize_dec_ref(c, reversed); Z3_optimize_dec_ref(c, first);
    Z3_dec_ref(c, cap); Z3_dec_ref(c, sum); Z3_dec_ref(c, two); Z3_dec_ref(c, zero);
    Z3_dec_ref(c, y); Z3_dec_ref(c, x);
    Z3_dec_ref(c, Z3_sort_to_ast(c, boolean)); Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    return 0;
}
