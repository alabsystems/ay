// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_ast sequence_integer(Z3_context c, Z3_sort sort, int value) {
    return sequence_hold(c, Z3_mk_int(c, value, sort));
}

static inline Z3_ast sequence_string(Z3_context c, const char* text) {
    return sequence_hold(c, Z3_mk_string(c, text));
}

static inline int sequence_integer_is(Z3_context c, Z3_ast term, int expected) {
    if (!term) return 0;
    Z3_ast value = sequence_hold(c, Z3_simplify(c, term));
    int integer = 0;
    return value && Z3_get_numeral_int(c, value, &integer) && integer == expected;
}

static inline int sequence_boolean_is(Z3_context c, Z3_ast term, Z3_lbool expected) {
    if (!term) return 0;
    Z3_ast value = sequence_hold(c, Z3_simplify(c, term));
    return value && Z3_get_bool_value(c, value) == expected;
}

static inline int sequence_equal_is(Z3_context c, Z3_ast left, Z3_ast right, Z3_lbool expected) {
    if (!left || !right) return 0;
    Z3_ast equality = sequence_hold(c, Z3_mk_eq(c, left, right));
    return sequence_boolean_is(c, equality, expected);
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("string.operations.context-created", c != NULL);
    Z3_sort integer = sequence_hold_sort(c, Z3_mk_int_sort(c));
    Z3_sort string = sequence_hold_sort(c, Z3_mk_string_sort(c));
    Z3_ast zero = sequence_integer(c, integer, 0), one = sequence_integer(c, integer, 1);
    Z3_ast two = sequence_integer(c, integer, 2), three = sequence_integer(c, integer, 3);
    Z3_ast five = sequence_integer(c, integer, 5), minus_one = sequence_integer(c, integer, -1);
    Z3_ast ab = sequence_string(c, "ab"), cd = sequence_string(c, "cd"), word = sequence_string(c, "abab");
    Z3_ast empty = sequence_hold(c, Z3_mk_seq_empty(c, string));
    CHECK("string.operations.setup", integer && string && zero && one && two && three && five && minus_one && ab && cd && word && empty);
    Z3_ast parts[3] = {ab, empty, cd};
    Z3_ast joined = sequence_hold(c, Z3_mk_seq_concat(c, 3, parts));
    Z3_ast abcd = sequence_string(c, "abcd"), bc = sequence_string(c, "bc"), d = sequence_string(c, "d");
    CHECK("string.operations.concat-and-empty", sequence_equal_is(c, joined, abcd, Z3_L_TRUE) &&
          sequence_equal_is(c, joined, word, Z3_L_FALSE));
    Z3_ast length = sequence_hold(c, Z3_mk_seq_length(c, joined));
    CHECK("string.operations.length", sequence_integer_is(c, length, 4) && !sequence_integer_is(c, length, 3));
    Z3_ast middle = sequence_hold(c, Z3_mk_seq_extract(c, joined, one, two));
    Z3_ast tail = sequence_hold(c, Z3_mk_seq_extract(c, joined, three, five));
    CHECK("string.operations.extract-and-clamped-tail", sequence_equal_is(c, middle, bc, Z3_L_TRUE) && sequence_equal_is(c, tail, d, Z3_L_TRUE));
    Z3_ast negative = sequence_hold(c, Z3_mk_seq_extract(c, joined, minus_one, two));
    Z3_ast beyond = sequence_hold(c, Z3_mk_seq_extract(c, joined, five, two));
    CHECK("string.operations.extract-outside-is-empty", sequence_equal_is(c, negative, empty, Z3_L_TRUE) && sequence_equal_is(c, beyond, empty, Z3_L_TRUE));
    Z3_ast at_one = sequence_hold(c, Z3_mk_seq_at(c, joined, one));
    Z3_ast at_beyond = sequence_hold(c, Z3_mk_seq_at(c, joined, five));
    Z3_ast b = sequence_string(c, "b");
    CHECK("string.operations.at-singleton-and-outside", sequence_equal_is(c, at_one, b, Z3_L_TRUE) && sequence_equal_is(c, at_beyond, empty, Z3_L_TRUE));
    Z3_ast index0 = sequence_hold(c, Z3_mk_seq_index(c, word, ab, zero));
    Z3_ast index1 = sequence_hold(c, Z3_mk_seq_index(c, word, ab, one));
    Z3_ast absent = sequence_hold(c, Z3_mk_seq_index(c, word, cd, zero));
    Z3_ast last = sequence_hold(c, Z3_mk_seq_last_index(c, word, ab));
    CHECK("string.operations.index-offset-and-absence", sequence_integer_is(c, index0, 0) && sequence_integer_is(c, index1, 2) && sequence_integer_is(c, absent, -1) && sequence_integer_is(c, last, 2));
    Z3_ast prefix = sequence_hold(c, Z3_mk_seq_prefix(c, ab, joined));
    Z3_ast suffix = sequence_hold(c, Z3_mk_seq_suffix(c, cd, joined));
    Z3_ast contains = sequence_hold(c, Z3_mk_seq_contains(c, joined, bc));
    Z3_ast wrong_prefix = sequence_hold(c, Z3_mk_seq_prefix(c, cd, joined));
    Z3_ast wrong_contains = sequence_hold(c, Z3_mk_seq_contains(c, joined, word));
    CHECK("string.operations.prefix-suffix-contains", sequence_boolean_is(c, prefix, Z3_L_TRUE) && sequence_boolean_is(c, suffix, Z3_L_TRUE) && sequence_boolean_is(c, contains, Z3_L_TRUE) && sequence_boolean_is(c, wrong_prefix, Z3_L_FALSE) && sequence_boolean_is(c, wrong_contains, Z3_L_FALSE));
    Z3_ast replacement = sequence_string(c, "X");
    Z3_ast replaced = sequence_hold(c, Z3_mk_seq_replace(c, word, ab, replacement));
    Z3_ast expected = sequence_string(c, "Xab");
    Z3_ast wrong = sequence_string(c, "XX");
    CHECK("string.operations.replace-first-only", sequence_equal_is(c, replaced, expected, Z3_L_TRUE) && sequence_equal_is(c, replaced, wrong, Z3_L_FALSE));
    Z3_ast code = sequence_integer(c, integer, 0x100);
    Z3_ast from_code = sequence_hold(c, Z3_mk_string_from_code(c, code));
    Z3_ast to_code = sequence_hold(c, Z3_mk_string_to_code(c, from_code));
    Z3_ast multiple_code = sequence_hold(c, Z3_mk_string_to_code(c, ab));
    Z3_ast negative_code = sequence_hold(c, Z3_mk_string_from_code(c, minus_one));
    CHECK("string.operations.codepoint-roundtrip-and-domain", sequence_integer_is(c, to_code, 0x100) && sequence_integer_is(c, multiple_code, -1) && sequence_equal_is(c, negative_code, empty, Z3_L_TRUE));
    sequence_release(c);
    Z3_del_context(c);
    return 0;
}
