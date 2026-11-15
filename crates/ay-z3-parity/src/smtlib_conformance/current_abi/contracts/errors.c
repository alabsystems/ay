// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("errors.context-created", c != NULL);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    Z3_ast seven = Z3_mk_int(c, 7, integer); HOLD(c, seven);
    CHECK("errors.valid-setup", integer && seven && Z3_get_error_code(c) == Z3_OK);
    contract_last_error = Z3_OK;
    /* Pinned 5.3.3 throws from AST construction before check_sorts, so its
       API exception handler reports Z3_EXCEPTION. Do not consume a return
       value from the failed call: this input violates the sort precondition. */
    (void)Z3_mk_not(c, seven);
    CHECK("errors.invalid-sort-reported",
          contract_last_error == Z3_EXCEPTION && Z3_get_error_code(c) == Z3_EXCEPTION);
    const char *message = Z3_get_error_msg(c, Z3_EXCEPTION);
    CHECK("errors.message-present", message &&
          strncmp(message, "Sort mismatch at argument #1", sizeof("Sort mismatch at argument #1") - 1) == 0 &&
          strstr(message, "supplied sort is Int") != NULL);
    Z3_ast truth = Z3_mk_true(c); HOLD(c, truth);
    Z3_ast negative = Z3_mk_not(c, truth); HOLD(c, negative);
    CHECK("errors.valid-call-recovers", truth && negative && Z3_get_error_code(c) == Z3_OK &&
          Z3_get_bool_value(c, truth) == Z3_L_TRUE &&
          Z3_get_sort_kind(c, Z3_get_sort(c, negative)) == Z3_BOOL_SORT);
    Z3_set_error(c, Z3_INVALID_ARG);
    CHECK("errors.explicit-error-state", Z3_get_error_code(c) == Z3_INVALID_ARG);
    Z3_set_error(c, Z3_OK);
    CHECK("errors.explicit-error-clear", Z3_get_error_code(c) == Z3_OK);
    Z3_dec_ref(c, negative); Z3_dec_ref(c, truth); Z3_dec_ref(c, seven);
    Z3_dec_ref(c, Z3_sort_to_ast(c, integer));
    Z3_del_context(c);
    return 0;
}
