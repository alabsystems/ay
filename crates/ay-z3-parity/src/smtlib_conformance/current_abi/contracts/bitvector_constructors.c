// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("bitvector.constructors.context-created", c != NULL);
    Z3_sort four = Z3_mk_bv_sort(c, 4); HOLD_SORT(c, four);
    Z3_sort three = Z3_mk_bv_sort(c, 3); HOLD_SORT(c, three);
    Z3_sort six = Z3_mk_bv_sort(c, 6); HOLD_SORT(c, six);
    CHECK("bitvector.constructors.sort-widths", four && three && six &&
          Z3_get_sort_kind(c, four) == Z3_BV_SORT && Z3_get_bv_sort_size(c, four) == 4 &&
          Z3_get_bv_sort_size(c, three) == 3 && Z3_get_bv_sort_size(c, six) == 6);
    int numerals = 1, extracts = 1, extensions = 1, repetitions = 1;
    for (unsigned value = 0; value < 16; ++value) {
        Z3_ast term = bv_unsigned(c, four, value);
        bool bits[4];
        for (unsigned bit = 0; bit < 4; ++bit) bits[bit] = ((value >> bit) & 1u) != 0;
        Z3_ast bit_term = Z3_mk_bv_numeral(c, 4, bits); HOLD(c, bit_term);
        char decimal[16];
        (void)snprintf(decimal, sizeof(decimal), "%u", value);
        Z3_ast decimal_term = Z3_mk_numeral(c, decimal, four); HOLD(c, decimal_term);
        numerals &= term && bit_term && decimal_term && bv_value_is(c, term, value) &&
            bv_truth_is(c, Z3_mk_eq(c, term, bit_term), 1) &&
            bv_truth_is(c, Z3_mk_eq(c, term, decimal_term), 1) &&
            !bv_value_is(c, term, value ^ 1u);
        extracts &= bv_value_is(c, Z3_mk_extract(c, 3, 1, term), value >> 1) &&
            bv_value_is(c, Z3_mk_extract(c, 0, 0, term), value & 1u);
        unsigned signed_extended = (unsigned)bv_signed(value, 4) & 255u;
        extensions &= bv_value_is(c, Z3_mk_zero_ext(c, 4, term), value) &&
            bv_value_is(c, Z3_mk_sign_ext(c, 4, term), signed_extended);
        repetitions &= bv_value_is(c, Z3_mk_repeat(c, 2, term), value * 17u);
        if (decimal_term) Z3_dec_ref(c, decimal_term);
        if (bit_term) Z3_dec_ref(c, bit_term);
        if (term) Z3_dec_ref(c, term);
    }
    CHECK("bitvector.constructors.all-four-bit-numerals", numerals);
    CHECK("bitvector.constructors.all-four-bit-extracts", extracts);
    CHECK("bitvector.constructors.all-four-bit-extensions", extensions);
    CHECK("bitvector.constructors.all-four-bit-repetitions", repetitions);
    int concatenations = 1;
    for (unsigned a = 0; a < 8; ++a) for (unsigned b = 0; b < 8; ++b) {
        Z3_ast high = bv_unsigned(c, three, a), low = bv_unsigned(c, three, b);
        concatenations &= bv_value_is(c, Z3_mk_concat(c, high, low), (a << 3) | b);
        Z3_dec_ref(c, low); Z3_dec_ref(c, high);
    }
    CHECK("bitvector.constructors.all-three-bit-concatenations", concatenations);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_join_x"), six); HOLD(c, x);
    Z3_ast high = Z3_mk_extract(c, 5, 3, x); HOLD(c, high);
    Z3_ast low = Z3_mk_extract(c, 2, 0, x); HOLD(c, low);
    Z3_ast joined = Z3_mk_concat(c, high, low); HOLD(c, joined);
    Z3_ast same = Z3_mk_eq(c, joined, x); HOLD(c, same);
    CHECK("bitvector.constructors.symbolic-split-join", x && high && low && joined && same &&
          bv_unsat(c, Z3_mk_not(c, same)));
    Z3_dec_ref(c, same); Z3_dec_ref(c, joined); Z3_dec_ref(c, low); Z3_dec_ref(c, high); Z3_dec_ref(c, x);
    Z3_dec_ref(c, Z3_sort_to_ast(c, six)); Z3_dec_ref(c, Z3_sort_to_ast(c, three));
    Z3_dec_ref(c, Z3_sort_to_ast(c, four));
    Z3_del_context(c);
    return 0;
}
