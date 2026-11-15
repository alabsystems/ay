// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_ast sequence_integer(Z3_context c, Z3_sort sort, int value) {
    return sequence_hold(c, Z3_mk_int(c, value, sort));
}

static inline Z3_ast sequence_string(Z3_context c, const char* text) {
    return sequence_hold(c, Z3_mk_string(c, text));
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("string.errors.context-created", c != NULL);
    Z3_ast text = sequence_string(c, "ab");
    Z3_sort integer = sequence_hold_sort(c, Z3_mk_int_sort(c));
    Z3_ast number = sequence_integer(c, integer, 7);
    CHECK("string.errors.setup", text && integer && number);
    unsigned buffer[3] = {101, 102, 103};
    contract_last_error = Z3_OK;
    Z3_get_string_contents(c, text, 3, buffer);
    CHECK("string.errors.wrong-content-length-refused", contract_last_error == Z3_INVALID_ARG &&
          Z3_get_error_code(c) == Z3_INVALID_ARG && buffer[0] == 101 && buffer[1] == 102 && buffer[2] == 103);
    contract_last_error = Z3_OK;
    Z3_get_string_contents(c, text, 2, buffer);
    CHECK("string.errors.content-call-recovers", Z3_get_error_code(c) == Z3_OK && contract_last_error == Z3_OK &&
          buffer[0] == 'a' && buffer[1] == 'b' && buffer[2] == 103);
    contract_last_error = Z3_OK;
    (void)Z3_get_lstring(c, text, NULL);
    CHECK("string.errors.null-length-refused", contract_last_error == Z3_INVALID_ARG && Z3_get_error_code(c) == Z3_INVALID_ARG);
    contract_last_error = Z3_OK;
    Z3_ast invalid = Z3_mk_lstring(c, 1, NULL);
    CHECK("string.errors.null-nonempty-buffer-refused", !invalid && contract_last_error == Z3_INVALID_ARG && Z3_get_error_code(c) == Z3_INVALID_ARG);
    Z3_ast empty = sequence_hold(c, Z3_mk_lstring(c, 0, NULL));
    CHECK("string.errors.empty-null-buffer-accepted", empty && Z3_get_error_code(c) == Z3_OK && Z3_get_string_length(c, empty) == 0);
    contract_last_error = Z3_OK;
    unsigned length = Z3_get_string_length(c, number);
    CHECK("string.errors.nonstring-length-refused", length == 0 && contract_last_error == Z3_INVALID_ARG && Z3_get_error_code(c) == Z3_INVALID_ARG);
    contract_last_error = Z3_OK;
    Z3_sort basis = Z3_get_seq_sort_basis(c, integer);
    CHECK("string.errors.nonsequence-basis-refused", !basis && contract_last_error == Z3_INVALID_ARG && Z3_get_error_code(c) == Z3_INVALID_ARG);
    CHECK("string.errors.valid-call-after-errors", Z3_get_string_length(c, text) == 2 && Z3_get_error_code(c) == Z3_OK);
    sequence_release(c);
    Z3_del_context(c);
    return 0;
}
