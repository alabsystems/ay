// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#include <stdint.h>

static Z3_ast bv_unsigned(Z3_context c, Z3_sort sort, unsigned value) {
    Z3_ast term = Z3_mk_unsigned_int64(c, (uint64_t)value, sort);
    HOLD(c, term);
    return term;
}

/* Only widths 3 and 4 and values below 2^width are passed by these fixtures. */
static int bv_signed(unsigned value, unsigned width) {
    unsigned sign = 1u << (width - 1u);
    return value < sign ? (int)value : (int)value - (int)(2u * sign);
}

/* Retain a just-created expression before the next API call can collect it. */
static int bv_value_is(Z3_context c, Z3_ast term, uint64_t expected) {
    if (!term) return 0;
    HOLD(c, term);
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    uint64_t actual = 0;
    int correct = value && Z3_get_numeral_uint64(c, value, &actual) && actual == expected;
    if (value) Z3_dec_ref(c, value);
    Z3_dec_ref(c, term);
    return correct;
}

static int bv_truth_is(Z3_context c, Z3_ast term, int expected) {
    if (!term) return 0;
    HOLD(c, term);
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    int correct = value && Z3_get_bool_value(c, value) == (expected ? Z3_L_TRUE : Z3_L_FALSE);
    if (value) Z3_dec_ref(c, value);
    Z3_dec_ref(c, term);
    return correct;
}

static int bv_unsat(Z3_context c, Z3_ast contradiction) {
    if (!contradiction) return 0;
    HOLD(c, contradiction);
    Z3_solver solver = Z3_mk_solver(c);
    if (solver) Z3_solver_inc_ref(c, solver);
    int correct = 0;
    if (solver) {
        Z3_solver_assert(c, solver, contradiction);
        correct = Z3_solver_check(c, solver) == Z3_L_FALSE && Z3_get_error_code(c) == Z3_OK;
        Z3_solver_dec_ref(c, solver);
    }
    Z3_dec_ref(c, contradiction);
    return correct;
}
