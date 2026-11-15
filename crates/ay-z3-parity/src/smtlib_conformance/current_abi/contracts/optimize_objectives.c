// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("optimize.objectives.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "opt_x"), integer); HOLD(c, x);
    Z3_ast y = Z3_mk_const(c, Z3_mk_string_symbol(c, "opt_y"), integer); HOLD(c, y);
    Z3_ast zero = opt_integer(c, integer, 0), one = opt_integer(c, integer, 1);
    Z3_ast two = opt_integer(c, integer, 2), four = opt_integer(c, integer, 4);
    Z3_ast eight = opt_integer(c, integer, 8);
    Z3_optimize o = opt_create(c);
    CHECK("optimize.objectives.setup", integer && x && y && zero && one && two && four && eight && o &&
          opt_range(c, o, x, zero, four) && opt_range(c, o, y, two, eight));
    /* Balance an additional object reference before using the retained owner. */
    Z3_optimize_inc_ref(c, o);
    Z3_optimize_dec_ref(c, o);
    unsigned hx = Z3_optimize_maximize(c, o, x);
    unsigned hy = Z3_optimize_minimize(c, o, y);
    CHECK("optimize.objectives.distinct-handles", hx == 0 && hy == 1 && Z3_get_error_code(c) == Z3_OK);
    CHECK("optimize.objectives.finite-optimum", Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, o, hx, 4, 1) && opt_bounds_are(c, o, hy, 2, 1));
    Z3_model old = opt_model(c, o);
    CHECK("optimize.objectives.exact-model", old && opt_model_rational_is(c, old, x, 4, 1) &&
          opt_model_rational_is(c, old, y, 2, 1) && !opt_model_rational_is(c, old, x, 3, 1));
    Z3_ast_vector objectives = opt_objectives(c, o);
    Z3_ast_vector assertions = opt_assertions(c, o);
    CHECK("optimize.objectives.normalized-objectives", objectives &&
          Z3_ast_vector_size(c, objectives) == 2 &&
          opt_model_rational_is(c, old, Z3_ast_vector_get(c, objectives, hx), -4, 1) &&
          opt_model_rational_is(c, old, Z3_ast_vector_get(c, objectives, hy), 2, 1));
    CHECK("optimize.objectives.assertion-snapshot", assertions && Z3_ast_vector_size(c, assertions) == 4 &&
          opt_model_bool_is(c, old, Z3_ast_vector_get(c, assertions, 0), Z3_L_TRUE) &&
          opt_model_bool_is(c, old, Z3_ast_vector_get(c, assertions, 1), Z3_L_TRUE) &&
          opt_model_bool_is(c, old, Z3_ast_vector_get(c, assertions, 2), Z3_L_TRUE) &&
          opt_model_bool_is(c, old, Z3_ast_vector_get(c, assertions, 3), Z3_L_TRUE));
    Z3_optimize_dec_ref(c, o);
    CHECK("optimize.objectives.retained-after-owner-release", opt_model_rational_is(c, old, x, 4, 1) &&
          Z3_ast_vector_size(c, objectives) == 2 && Z3_ast_vector_size(c, assertions) == 4 &&
          opt_model_rational_is(c, old, Z3_ast_vector_get(c, objectives, hx), -4, 1));
    Z3_optimize fresh = opt_create(c);
    Z3_ast_vector fresh_objectives = fresh ? opt_objectives(c, fresh) : NULL;
    Z3_ast_vector fresh_assertions = fresh ? opt_assertions(c, fresh) : NULL;
    CHECK("optimize.objectives.recreated-owner-is-empty", fresh && fresh_objectives && fresh_assertions &&
          Z3_ast_vector_size(c, fresh_objectives) == 0 && Z3_ast_vector_size(c, fresh_assertions) == 0 &&
          Z3_optimize_check(c, fresh, 0, NULL) == Z3_L_TRUE);
    Z3_ast x1 = Z3_mk_eq(c, x, one); HOLD(c, x1);
    Z3_optimize_assert(c, fresh, x1);
    unsigned hf = Z3_optimize_minimize(c, fresh, x);
    CHECK("optimize.objectives.recreated-owner-independent", hf == 0 &&
          Z3_optimize_check(c, fresh, 0, NULL) == Z3_L_TRUE && opt_bounds_are(c, fresh, hf, 1, 1) &&
          opt_model_rational_is(c, old, x, 4, 1));
    Z3_dec_ref(c, x1);
    Z3_ast_vector_dec_ref(c, fresh_assertions); Z3_ast_vector_dec_ref(c, fresh_objectives);
    Z3_optimize_dec_ref(c, fresh);
    Z3_ast_vector_dec_ref(c, assertions); Z3_ast_vector_dec_ref(c, objectives);
    Z3_model_dec_ref(c, old);
    Z3_dec_ref(c, eight); Z3_dec_ref(c, four); Z3_dec_ref(c, two);
    Z3_dec_ref(c, one); Z3_dec_ref(c, zero); Z3_dec_ref(c, y); Z3_dec_ref(c, x);
    Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    return 0;
}
