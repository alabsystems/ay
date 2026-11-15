// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/* These helpers only inspect exact finite values; no printed model oracle. */
#include <stdint.h>

static inline Z3_optimize opt_create(Z3_context c) {
    Z3_optimize o = Z3_mk_optimize(c);
    if (o) Z3_optimize_inc_ref(c, o);
    return o;
}

static inline Z3_ast opt_integer(Z3_context c, Z3_sort sort, int value) {
    Z3_ast result = Z3_mk_int(c, value, sort);
    HOLD(c, result);
    return result;
}

static inline Z3_ast_vector opt_objectives(Z3_context c, Z3_optimize o) {
    Z3_ast_vector result = Z3_optimize_get_objectives(c, o);
    if (result) Z3_ast_vector_inc_ref(c, result);
    return result;
}

static inline int opt_rational_is(Z3_context c, Z3_ast term, int64_t numerator, int64_t denominator) {
    if (!term) return 0;
    int64_t actual_numerator = 0, actual_denominator = 0;
    return Z3_get_numeral_rational_int64(c, term, &actual_numerator, &actual_denominator) &&
        actual_numerator == numerator && actual_denominator == denominator;
}

static inline int opt_vector_bound_is(Z3_context c, Z3_ast_vector vector,
                               int64_t numerator, int64_t denominator) {
    return vector && Z3_ast_vector_size(c, vector) == 3 &&
        opt_rational_is(c, Z3_ast_vector_get(c, vector, 0), 0, 1) &&
        opt_rational_is(c, Z3_ast_vector_get(c, vector, 1), numerator, denominator) &&
        opt_rational_is(c, Z3_ast_vector_get(c, vector, 2), 0, 1);
}

static inline int opt_bounds_are(Z3_context c, Z3_optimize o, unsigned handle,
                          int64_t numerator, int64_t denominator) {
    Z3_ast lower = Z3_optimize_get_lower(c, o, handle); HOLD(c, lower);
    Z3_ast upper = Z3_optimize_get_upper(c, o, handle); HOLD(c, upper);
    Z3_ast_vector lower_vector = Z3_optimize_get_lower_as_vector(c, o, handle);
    if (lower_vector) Z3_ast_vector_inc_ref(c, lower_vector);
    Z3_ast_vector upper_vector = Z3_optimize_get_upper_as_vector(c, o, handle);
    if (upper_vector) Z3_ast_vector_inc_ref(c, upper_vector);
    int correct = opt_rational_is(c, lower, numerator, denominator) &&
        opt_rational_is(c, upper, numerator, denominator) &&
        opt_vector_bound_is(c, lower_vector, numerator, denominator) &&
        opt_vector_bound_is(c, upper_vector, numerator, denominator);
    if (upper_vector) Z3_ast_vector_dec_ref(c, upper_vector);
    if (lower_vector) Z3_ast_vector_dec_ref(c, lower_vector);
    if (upper) Z3_dec_ref(c, upper);
    if (lower) Z3_dec_ref(c, lower);
    return correct;
}

static inline int opt_range(Z3_context c, Z3_optimize o, Z3_ast term, Z3_ast low, Z3_ast high) {
    Z3_ast lower = Z3_mk_ge(c, term, low); HOLD(c, lower);
    Z3_ast upper = Z3_mk_le(c, term, high); HOLD(c, upper);
    if (!lower || !upper) return 0;
    Z3_optimize_assert(c, o, lower);
    Z3_optimize_assert(c, o, upper);
    int correct = Z3_get_error_code(c) == Z3_OK;
    Z3_dec_ref(c, upper);
    Z3_dec_ref(c, lower);
    return correct;
}
