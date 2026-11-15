// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("optimize.scopes.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "scope_x"), integer); HOLD(c, x);
    Z3_ast zero = opt_integer(c, integer, 0), two = opt_integer(c, integer, 2);
    Z3_ast three = opt_integer(c, integer, 3), five = opt_integer(c, integer, 5);
    Z3_optimize o = opt_create(c);
    CHECK("optimize.scopes.setup", integer && x && zero && two && three && five && o &&
          opt_range(c, o, x, zero, five));
    unsigned base = Z3_optimize_maximize(c, o, x);
    CHECK("optimize.scopes.base-optimum", base == 0 &&
          Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE && opt_bounds_are(c, o, base, 5, 1));
    Z3_optimize_push(c, o);
    Z3_ast x_le_two = Z3_mk_le(c, x, two); HOLD(c, x_le_two);
    Z3_optimize_assert(c, o, x_le_two);
    unsigned scoped = Z3_optimize_minimize(c, o, x);
    Z3_ast_vector objectives = opt_objectives(c, o);
    Z3_ast_vector assertions = opt_assertions(c, o);
    CHECK("optimize.scopes.scoped-objective-and-assertion", scoped == 1 && objectives && assertions &&
          Z3_ast_vector_size(c, objectives) == 2 && Z3_ast_vector_size(c, assertions) == 3 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, assertions, 2), x_le_two) &&
          Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, o, base, 2, 1) && opt_bounds_are(c, o, scoped, 2, 1));
    Z3_model scoped_model = opt_model(c, o);
    Z3_ast x_ge_three = Z3_mk_ge(c, x, three); HOLD(c, x_ge_three);
    Z3_ast assumptions[1] = {x_ge_three};
    CHECK("optimize.scopes.assumption-contradiction", Z3_optimize_check(c, o, 1, assumptions) == Z3_L_FALSE);
    Z3_ast_vector core = Z3_optimize_get_unsat_core(c, o);
    if (core) Z3_ast_vector_inc_ref(c, core);
    CHECK("optimize.scopes.exact-assumption-core", core && Z3_ast_vector_size(c, core) == 1 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, core, 0), x_ge_three));
    CHECK("optimize.scopes.assumptions-do-not-persist", Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, o, base, 2, 1) && opt_model_rational_is(c, scoped_model, x, 2, 1));
    Z3_optimize_push(c, o);
    Z3_ast contradiction = Z3_mk_false(c); HOLD(c, contradiction);
    Z3_optimize_assert(c, o, contradiction);
    CHECK("optimize.scopes.nested-contradiction", Z3_optimize_check(c, o, 0, NULL) == Z3_L_FALSE);
    Z3_optimize_pop(c, o);
    CHECK("optimize.scopes.inner-pop-restores-optimum", Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE &&
          opt_bounds_are(c, o, base, 2, 1));
    Z3_optimize_pop(c, o);
    Z3_ast_vector restored_objectives = opt_objectives(c, o);
    Z3_ast_vector restored_assertions = opt_assertions(c, o);
    CHECK("optimize.scopes.outer-pop-removes-objective", restored_objectives && restored_assertions &&
          Z3_ast_vector_size(c, restored_objectives) == 1 && Z3_ast_vector_size(c, restored_assertions) == 2 &&
          Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE && opt_bounds_are(c, o, base, 5, 1));
    CHECK("optimize.scopes.retained-snapshots", Z3_ast_vector_size(c, objectives) == 2 &&
          Z3_ast_vector_size(c, assertions) == 3 && Z3_ast_vector_size(c, core) == 1 &&
          Z3_is_eq_ast(c, Z3_ast_vector_get(c, assertions, 2), x_le_two) &&
          opt_model_rational_is(c, scoped_model, x, 2, 1));
    Z3_ast_vector_dec_ref(c, restored_assertions); Z3_ast_vector_dec_ref(c, restored_objectives);
    Z3_ast_vector_dec_ref(c, core); Z3_model_dec_ref(c, scoped_model);
    Z3_ast_vector_dec_ref(c, assertions); Z3_ast_vector_dec_ref(c, objectives);
    Z3_dec_ref(c, contradiction); Z3_dec_ref(c, x_ge_three); Z3_dec_ref(c, x_le_two);
    Z3_optimize_dec_ref(c, o);
    Z3_dec_ref(c, five); Z3_dec_ref(c, three); Z3_dec_ref(c, two); Z3_dec_ref(c, zero);
    Z3_dec_ref(c, x); Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    return 0;
}
