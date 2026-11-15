// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static int model_value_is(Z3_context c, Z3_model model, Z3_ast term, int expected) {
    Z3_ast value = NULL;
    if (!Z3_model_eval(c, model, term, false, &value) || !value) return 0;
    HOLD(c, value);
    int actual = 0;
    int correct = Z3_get_numeral_int(c, value, &actual) && actual == expected;
    Z3_dec_ref(c, value);
    return correct;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("model.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "contract_x"), integer); HOLD(c, x);
    Z3_ast seven = Z3_mk_int(c, 7, integer); HOLD(c, seven);
    Z3_ast nine = Z3_mk_int(c, 9, integer); HOLD(c, nine);
    Z3_ast x7 = Z3_mk_eq(c, x, seven); HOLD(c, x7);
    Z3_ast x9 = Z3_mk_eq(c, x, nine); HOLD(c, x9);
    Z3_solver solver = Z3_mk_solver(c); if (solver) Z3_solver_inc_ref(c, solver);
    CHECK("model.terms-and-solver", integer && x && seven && nine && x7 && x9 && solver);
    Z3_solver_assert(c, solver, x7);
    CHECK("model.initial-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model old = Z3_solver_get_model(c, solver); if (old) Z3_model_inc_ref(c, old);
    CHECK("model.eval-exact-integer", old && model_value_is(c, old, x, 7));
    Z3_func_decl x_decl = Z3_get_app_decl(c, Z3_to_app(c, x));
    Z3_ast interpretation = Z3_model_get_const_interp(c, old, x_decl); HOLD(c, interpretation);
    int interpreted = 0;
    CHECK("model.constant-interpretation", x_decl && interpretation &&
          Z3_model_has_interp(c, old, x_decl) && Z3_model_get_num_consts(c, old) == 1 &&
          Z3_is_eq_func_decl(c, Z3_model_get_const_decl(c, old, 0), x_decl) &&
          Z3_get_numeral_int(c, interpretation, &interpreted) && interpreted == 7);
    Z3_solver_push(c, solver);
    Z3_solver_assert(c, solver, x9);
    CHECK("model.retained-after-unsat", Z3_solver_check(c, solver) == Z3_L_FALSE &&
          model_value_is(c, old, x, 7));
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, x9);
    CHECK("model.changed-solver-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model fresh = Z3_solver_get_model(c, solver); if (fresh) Z3_model_inc_ref(c, fresh);
    CHECK("model.independent-retained-models", fresh && model_value_is(c, fresh, x, 9) &&
          model_value_is(c, old, x, 7));
    Z3_context destination = contract_context();
    CHECK("model.destination-created", destination != NULL);
    Z3_model translated = Z3_model_translate(c, old, destination);
    if (translated) Z3_model_inc_ref(destination, translated);
    Z3_ast translated_x = Z3_translate(c, x, destination); HOLD(destination, translated_x);
    CHECK("model.translation-created", translated && translated_x);
    Z3_model_dec_ref(c, fresh);
    Z3_model_dec_ref(c, old);
    Z3_solver_dec_ref(c, solver);
    Z3_dec_ref(c, interpretation);
    Z3_dec_ref(c, x9); Z3_dec_ref(c, x7);
    Z3_dec_ref(c, nine); Z3_dec_ref(c, seven); Z3_dec_ref(c, x);
    Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    CHECK("model.translation-survives-source-destruction",
          model_value_is(destination, translated, translated_x, 7));
    Z3_model_dec_ref(destination, translated);
    Z3_dec_ref(destination, translated_x);
    Z3_del_context(destination);
    return 0;
}
