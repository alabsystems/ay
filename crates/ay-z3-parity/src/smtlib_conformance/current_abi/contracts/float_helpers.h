// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#include <stdint.h>

/* Each caller supplies a live sort; every returned numeral is retained. All
   C double inputs below are exactly representable binary rationals. */
static Z3_ast fp_number(Z3_context c, Z3_sort sort, double value) {
    Z3_ast term = Z3_mk_fpa_numeral_double(c, value, sort); HOLD(c, term);
    return term;
}

/* These observers retain a fresh argument before performing another AST
   allocation. Passing an already retained term adds one balanced reference. */
static int fp_truth(Z3_context c, Z3_ast term, Z3_lbool expected) {
    if (!term) return 0;
    HOLD(c, term);
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    int correct = value && Z3_get_bool_value(c, value) == expected;
    if (value) Z3_dec_ref(c, value);
    Z3_dec_ref(c, term);
    return correct && Z3_get_error_code(c) == Z3_OK;
}

static int fp_exact(Z3_context c, Z3_ast term, Z3_ast expected) {
    if (!term || !expected) return 0;
    HOLD(c, term);
    int correct = fp_truth(c, Z3_mk_eq(c, term, expected), Z3_L_TRUE);
    Z3_dec_ref(c, term);
    return correct;
}

static int fp_bits(Z3_context c, Z3_ast term, uint64_t expected) {
    if (!term) return 0;
    HOLD(c, term);
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    uint64_t actual = 0;
    int correct = value && Z3_get_numeral_uint64(c, value, &actual) && actual == expected;
    if (value) Z3_dec_ref(c, value);
    Z3_dec_ref(c, term);
    return correct && Z3_get_error_code(c) == Z3_OK;
}
