// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static inline Z3_ast sequence_string(Z3_context c, const char* text) {
    return sequence_hold(c, Z3_mk_string(c, text));
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
    CHECK("string.codec.context-created", c != NULL);
    Z3_sort string = sequence_hold_sort(c, Z3_mk_string_sort(c));
    CHECK("string.codec.string-sort", string && Z3_is_string_sort(c, string) && Z3_is_seq_sort(c, string));
    Z3_ast ascii = sequence_string(c, "abc");
    CHECK("string.codec.ascii-roundtrip", ascii && Z3_is_string(c, ascii) &&
          Z3_get_string_length(c, ascii) == 3 && strcmp(Z3_get_string(c, ascii), "abc") == 0);

    const unsigned unicode_points[3] = {0x61, 0x100, 0x1f600};
    Z3_ast unicode = sequence_hold(c, Z3_mk_u32string(c, 3, unicode_points));
    Z3_ast escaped = sequence_string(c, "a\\u{100}\\u{1f600}");
    unsigned contents[3] = {0, 0, 0};
    CHECK("string.codec.unicode-escape-construction", unicode && escaped &&
          Z3_get_string_length(c, unicode) == 3 && sequence_equal_is(c, unicode, escaped, Z3_L_TRUE));
    Z3_get_string_contents(c, unicode, 3, contents);
    CHECK("string.codec.codepoint-extraction", Z3_get_error_code(c) == Z3_OK &&
          memcmp(contents, unicode_points, sizeof(contents)) == 0 &&
          strcmp(Z3_get_string(c, unicode), "a\\u{100}\\u{1f600}") == 0);

    /* These C entry points map bytes, not UTF-8 code points. */
    const char utf8_bytes[3] = {(char)0xc3, (char)0xa9, 0};
    const unsigned byte_points[2] = {0xc3, 0xa9};
    Z3_ast utf8 = sequence_string(c, utf8_bytes);
    Z3_ast utf8_length = sequence_hold(c, Z3_mk_lstring(c, 2, utf8_bytes));
    const unsigned accent_point[1] = {0xe9};
    Z3_ast accent = sequence_hold(c, Z3_mk_u32string(c, 1, accent_point));
    unsigned bytes_out[2] = {0, 0};
    if (utf8) Z3_get_string_contents(c, utf8, 2, bytes_out);
    CHECK("string.codec.utf8-bytes-are-not-decoded", utf8 && utf8_length && accent &&
          Z3_get_error_code(c) == Z3_OK && memcmp(bytes_out, byte_points, sizeof(bytes_out)) == 0 &&
          Z3_get_string_length(c, utf8) == 2 && Z3_get_string_length(c, accent) == 1 &&
          sequence_equal_is(c, utf8, utf8_length, Z3_L_TRUE) && sequence_equal_is(c, utf8, accent, Z3_L_FALSE));
    unsigned encoded_length = 0;
    const char* encoded = Z3_get_lstring(c, utf8, &encoded_length);
    CHECK("string.codec.length-string-byte-extraction", encoded && encoded_length == 2 &&
          memcmp(encoded, utf8_bytes, 2) == 0);

    const char with_zero[3] = {'A', 0, 'B'};
    const unsigned zero_points[3] = {'A', 0, 'B'};
    Z3_ast zero = sequence_hold(c, Z3_mk_lstring(c, 3, with_zero));
    Z3_ast terminated = sequence_string(c, with_zero);
    unsigned zero_out[3] = {99, 99, 99};
    if (zero) Z3_get_string_contents(c, zero, 3, zero_out);
    CHECK("string.codec.embedded-nul-versus-c-terminator", zero && terminated &&
          Z3_get_error_code(c) == Z3_OK && Z3_get_string_length(c, zero) == 3 &&
          Z3_get_string_length(c, terminated) == 1 && memcmp(zero_out, zero_points, sizeof(zero_out)) == 0 &&
          sequence_equal_is(c, zero, terminated, Z3_L_FALSE));
    encoded = Z3_get_lstring(c, zero, &encoded_length);
    CHECK("string.codec.nul-is-escaped-on-extraction", encoded && encoded_length == 7 &&
          memcmp(encoded, "A\\u{0}B", 7) == 0);

    Z3_ast literal_escape = sequence_hold(c, Z3_mk_lstring(c, 5, "\\u{0}"));
    Z3_ast decoded_zero = sequence_string(c, "\\u{0}");
    CHECK("string.codec.length-constructor-does-not-unescape", literal_escape && decoded_zero &&
          Z3_get_string_length(c, literal_escape) == 5 && Z3_get_string_length(c, decoded_zero) == 1 &&
          sequence_equal_is(c, literal_escape, decoded_zero, Z3_L_FALSE));
    encoded = Z3_get_lstring(c, unicode, &encoded_length);
    CHECK("string.codec.wide-codepoints-are-escaped", encoded && encoded_length == 17 &&
          memcmp(encoded, "a\\u{100}\\u{1f600}", 17) == 0);
    for (unsigned i = 0; i < 256; ++i) {
        char text[32];
        snprintf(text, sizeof(text), "temporary-%u", i);
        Z3_ast churn = Z3_mk_string(c, text);
        if (!churn) return 2;
        Z3_inc_ref(c, churn);
        Z3_dec_ref(c, churn);
    }
    Z3_get_string_contents(c, unicode, 3, contents);
    CHECK("string.codec.retained-literals-survive-churn", Z3_get_error_code(c) == Z3_OK &&
          memcmp(contents, unicode_points, sizeof(contents)) == 0 &&
          Z3_get_string_length(c, zero) == 3);
    sequence_release(c);
    Z3_del_context(c);
    return 0;
}
