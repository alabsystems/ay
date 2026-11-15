// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#include <limits.h>

static inline int opt_index_error(Z3_context c) {
    if (Z3_get_error_code(c) != Z3_EXCEPTION || contract_last_error != Z3_EXCEPTION) return 0;
    const char *message = Z3_get_error_msg(c, Z3_EXCEPTION);
    return message && strcmp(message, "index out of bounds") == 0;
}

static inline int opt_invalid_handle(Z3_context c, Z3_optimize o, unsigned handle) {
    contract_last_error = Z3_OK;
    if (Z3_optimize_get_lower(c, o, handle) || !opt_index_error(c)) return 0;
    contract_last_error = Z3_OK;
    if (Z3_optimize_get_upper(c, o, handle) || !opt_index_error(c)) return 0;
    contract_last_error = Z3_OK;
    if (Z3_optimize_get_lower_as_vector(c, o, handle) || !opt_index_error(c)) return 0;
    contract_last_error = Z3_OK;
    return !Z3_optimize_get_upper_as_vector(c, o, handle) && opt_index_error(c);
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("optimize.errors.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "error_x"), integer); HOLD(c, x);
    Z3_ast zero = opt_integer(c, integer, 0), one = opt_integer(c, integer, 1);
    Z3_ast four = opt_integer(c, integer, 4);
    Z3_ast truth = Z3_mk_true(c); HOLD(c, truth);
    Z3_optimize o = opt_create(c);
    CHECK("optimize.errors.setup", integer && x && zero && one && four && truth && o);
    CHECK("optimize.errors.empty-handles-refused", opt_invalid_handle(c, o, 0) &&
          opt_invalid_handle(c, o, UINT_MAX));
    Z3_optimize_push(c, o);
    CHECK("optimize.errors.scoped-setup", opt_range(c, o, x, zero, four));
    unsigned original = Z3_optimize_maximize(c, o, x);
    CHECK("optimize.errors.valid-objective-after-error", original == 0 &&
          Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE && Z3_get_error_code(c) == Z3_OK &&
          opt_bounds_are(c, o, original, 4, 1));
    CHECK("optimize.errors.out-of-range-handles-refused", opt_invalid_handle(c, o, original + 1) &&
          opt_invalid_handle(c, o, UINT_MAX));
    contract_last_error = Z3_OK;
    (void)Z3_optimize_assert_soft(c, o, truth, NULL, Z3_mk_string_symbol(c, "invalid-weight"));
    CHECK("optimize.errors.null-weight-refused", Z3_get_error_code(c) == Z3_INVALID_ARG &&
          contract_last_error == Z3_INVALID_ARG);
    CHECK("optimize.errors.valid-check-recovers", Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE &&
          Z3_get_error_code(c) == Z3_OK && opt_bounds_are(c, o, original, 4, 1));
    Z3_optimize_pop(c, o);
    Z3_ast_vector objectives = opt_objectives(c, o), assertions = opt_assertions(c, o);
    CHECK("optimize.errors.pop-all-is-empty", objectives && assertions &&
          Z3_ast_vector_size(c, objectives) == 0 && Z3_ast_vector_size(c, assertions) == 0 &&
          Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE);
    CHECK("optimize.errors.removed-handle-refused", opt_invalid_handle(c, o, original));
    CHECK("optimize.errors.replacement-setup", opt_range(c, o, x, zero, one));
    unsigned replacement = Z3_optimize_minimize(c, o, x);
    CHECK("optimize.errors.reused-index-has-new-value", replacement == original &&
          Z3_optimize_check(c, o, 0, NULL) == Z3_L_TRUE && opt_bounds_are(c, o, replacement, 0, 1));
    Z3_ast_vector_dec_ref(c, assertions); Z3_ast_vector_dec_ref(c, objectives);
    Z3_optimize_dec_ref(c, o);
    Z3_dec_ref(c, truth); Z3_dec_ref(c, four); Z3_dec_ref(c, one); Z3_dec_ref(c, zero);
    Z3_dec_ref(c, x); Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    return 0;
}
