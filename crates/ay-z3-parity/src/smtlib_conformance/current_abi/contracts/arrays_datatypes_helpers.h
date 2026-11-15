// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline int ad_simplified_int(Z3_context c, Z3_ast term, int expected) {
    if (!term) return 0;
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    if (!value) return 0;
    int actual = 0;
    int correct = Z3_get_numeral_int(c, value, &actual) && actual == expected;
    Z3_dec_ref(c, value);
    return correct && Z3_get_error_code(c) == Z3_OK;
}

static inline int ad_unsatisfiable(Z3_context c, Z3_solver solver, Z3_ast formula) {
    if (!solver || !formula) return 0;
    Z3_solver_reset(c, solver);
    Z3_solver_assert(c, solver, formula);
    return Z3_solver_check(c, solver) == Z3_L_FALSE && Z3_get_error_code(c) == Z3_OK;
}

static inline int ad_model_int(Z3_context c, Z3_model model, Z3_ast term, int expected) {
    if (!model || !term) return 0;
    Z3_ast value = NULL;
    if (!Z3_model_eval(c, model, term, false, &value) || !value) return 0;
    HOLD(c, value);
    int actual = 0;
    int correct = Z3_get_numeral_int(c, value, &actual) && actual == expected;
    Z3_dec_ref(c, value);
    return correct && Z3_get_error_code(c) == Z3_OK;
}

static inline int ad_model_bool(Z3_context c, Z3_model model, Z3_ast term, Z3_lbool expected) {
    if (!model || !term) return 0;
    Z3_ast value = NULL;
    if (!Z3_model_eval(c, model, term, false, &value) || !value) return 0;
    HOLD(c, value);
    int correct = Z3_get_bool_value(c, value) == expected;
    Z3_dec_ref(c, value);
    return correct && Z3_get_error_code(c) == Z3_OK;
}
