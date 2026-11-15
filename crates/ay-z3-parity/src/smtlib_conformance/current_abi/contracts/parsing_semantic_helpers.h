// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static Z3_ast parsing_roots[512];
static unsigned parsing_root_count = 0;

static Z3_ast parsing_hold(Z3_context c, Z3_ast term) {
    if (!term || parsing_root_count == 512) return NULL;
    Z3_inc_ref(c, term);
    parsing_roots[parsing_root_count++] = term;
    return term;
}

static Z3_sort parsing_sort(Z3_context c, Z3_sort sort) {
    return sort && parsing_hold(c, Z3_sort_to_ast(c, sort)) ? sort : NULL;
}

static void parsing_release(Z3_context c) {
    while (parsing_root_count) Z3_dec_ref(c, parsing_roots[--parsing_root_count]);
}

static int parsing_integer_is(Z3_context c, Z3_ast term, int expected) {
    if (!term) return 0;
    Z3_ast simplified = parsing_hold(c, Z3_simplify(c, term));
    int actual = 0;
    return simplified && Z3_get_numeral_int(c, simplified, &actual) && actual == expected;
}

static int parsing_solver_is(Z3_context c, Z3_ast formula, Z3_lbool expected) {
    if (!formula) return 0;
    Z3_solver solver = Z3_mk_solver(c);
    if (!solver) return 0;
    Z3_solver_inc_ref(c, solver);
    Z3_solver_assert(c, solver, formula);
    int correct = Z3_solver_check(c, solver) == expected && Z3_get_error_code(c) == Z3_OK;
    Z3_solver_dec_ref(c, solver);
    return correct;
}
