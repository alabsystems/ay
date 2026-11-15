// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static int bv_integer_is(Z3_context c, Z3_ast term, int64_t expected) {
    if (!term) return 0;
    HOLD(c, term);
    Z3_ast value = Z3_simplify(c, term); HOLD(c, value);
    int64_t actual = 0;
    int correct = value && Z3_get_numeral_int64(c, value, &actual) && actual == expected;
    if (value) Z3_dec_ref(c, value);
    Z3_dec_ref(c, term);
    return correct;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("bitvector.overflow.context-created", c != NULL);
    Z3_sort three = Z3_mk_bv_sort(c, 3); HOLD_SORT(c, three);
    Z3_sort integer = Z3_mk_int_sort(c); HOLD_SORT(c, integer);
    CHECK("bitvector.overflow.sorts-created", three && integer);
    int unsigned_add = 1, signed_add = 1, subtraction = 1, multiplication = 1, negation_division = 1, conversions = 1;
    for (unsigned a = 0; a < 8; ++a) {
        Z3_ast left = bv_unsigned(c, three, a);
        int sa = bv_signed(a, 3);
        conversions &= bv_integer_is(c, Z3_mk_bv2int(c, left, false), (int64_t)a) &&
            bv_integer_is(c, Z3_mk_bv2int(c, left, true), (int64_t)sa);
        negation_division &= bv_truth_is(c, Z3_mk_bvneg_no_overflow(c, left), sa != -4);
        for (unsigned b = 0; b < 8; ++b) {
            Z3_ast right = bv_unsigned(c, three, b);
            int sb = bv_signed(b, 3), sum = sa + sb, difference = sa - sb, product = sa * sb;
            unsigned_add &= bv_truth_is(c, Z3_mk_bvadd_no_overflow(c, left, right, false), a + b <= 7u);
            signed_add &= bv_truth_is(c, Z3_mk_bvadd_no_overflow(c, left, right, true), sum <= 3) &&
                bv_truth_is(c, Z3_mk_bvadd_no_underflow(c, left, right), sum >= -4);
            subtraction &= bv_truth_is(c, Z3_mk_bvsub_no_overflow(c, left, right), difference <= 3) &&
                bv_truth_is(c, Z3_mk_bvsub_no_underflow(c, left, right, true), difference >= -4) &&
                bv_truth_is(c, Z3_mk_bvsub_no_underflow(c, left, right, false), a >= b);
            multiplication &= bv_truth_is(c, Z3_mk_bvmul_no_overflow(c, left, right, false), a * b <= 7u) &&
                bv_truth_is(c, Z3_mk_bvmul_no_overflow(c, left, right, true), product <= 3) &&
                bv_truth_is(c, Z3_mk_bvmul_no_underflow(c, left, right), product >= -4);
            negation_division &= bv_truth_is(c, Z3_mk_bvsdiv_no_overflow(c, left, right), !(sa == -4 && sb == -1));
            Z3_dec_ref(c, right);
        }
        Z3_dec_ref(c, left);
    }
    CHECK("bitvector.overflow.all-three-bit-unsigned-add", unsigned_add);
    CHECK("bitvector.overflow.all-three-bit-signed-add", signed_add);
    CHECK("bitvector.overflow.all-three-bit-subtraction", subtraction);
    CHECK("bitvector.overflow.all-three-bit-multiplication", multiplication);
    CHECK("bitvector.overflow.all-three-bit-negation-and-division", negation_division);
    CHECK("bitvector.overflow.all-three-bit-signed-unsigned-conversion", conversions);
    int reductions = 1;
    for (int value = -17; value <= 17; ++value) {
        Z3_ast number = Z3_mk_int(c, value, integer); HOLD(c, number);
        reductions &= bv_value_is(c, Z3_mk_int2bv(c, 3, number), (unsigned)value & 7u);
        Z3_dec_ref(c, number);
    }
    CHECK("bitvector.overflow.integer-to-bv-modular-reduction", reductions);
    Z3_sort wide = Z3_mk_bv_sort(c, 65); HOLD_SORT(c, wide);
    Z3_sort sixty_four = Z3_mk_bv_sort(c, 64); HOLD_SORT(c, sixty_four);
    Z3_ast beyond = Z3_mk_numeral(c, "18446744073709551616", wide); HOLD(c, beyond);
    Z3_ast maximum = Z3_mk_numeral(c, "18446744073709551615", sixty_four); HOLD(c, maximum);
    uint64_t out_unsigned = 0;
    int64_t out_signed = 0;
    CHECK("bitvector.overflow.numeral-conversion-boundaries", beyond && maximum &&
          Z3_get_numeral_uint64(c, maximum, &out_unsigned) && out_unsigned == UINT64_MAX &&
          !Z3_get_numeral_int64(c, maximum, &out_signed) &&
          !Z3_get_numeral_uint64(c, beyond, &out_unsigned) && Z3_get_error_code(c) == Z3_OK);
    const char *decimal = Z3_get_numeral_string(c, beyond);
    CHECK("bitvector.overflow.exact-large-decimal", decimal && strcmp(decimal, "18446744073709551616") == 0);
    const char *binary = Z3_get_numeral_binary_string(c, beyond);
    CHECK("bitvector.overflow.exact-large-binary", binary &&
          strcmp(binary, "10000000000000000000000000000000000000000000000000000000000000000") == 0);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_carry_x"), three); HOLD(c, x);
    Z3_ast y = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_carry_y"), three); HOLD(c, y);
    Z3_ast extended_x = Z3_mk_zero_ext(c, 1, x); HOLD(c, extended_x);
    Z3_ast extended_y = Z3_mk_zero_ext(c, 1, y); HOLD(c, extended_y);
    Z3_ast sum = Z3_mk_bvadd(c, extended_x, extended_y); HOLD(c, sum);
    Z3_ast carry = Z3_mk_extract(c, 3, 3, sum); HOLD(c, carry);
    Z3_sort bit = Z3_mk_bv_sort(c, 1); HOLD_SORT(c, bit);
    Z3_ast zero = bv_unsigned(c, bit, 0);
    Z3_ast no_carry = Z3_mk_eq(c, carry, zero); HOLD(c, no_carry);
    Z3_ast predicate = Z3_mk_bvadd_no_overflow(c, x, y, false); HOLD(c, predicate);
    Z3_ast same = Z3_mk_eq(c, no_carry, predicate); HOLD(c, same);
    CHECK("bitvector.overflow.symbolic-carry-equivalence", same && bv_unsat(c, Z3_mk_not(c, same)));
    Z3_dec_ref(c, same); Z3_dec_ref(c, predicate); Z3_dec_ref(c, no_carry); Z3_dec_ref(c, zero);
    Z3_dec_ref(c, Z3_sort_to_ast(c, bit));
    Z3_dec_ref(c, carry); Z3_dec_ref(c, sum); Z3_dec_ref(c, extended_y); Z3_dec_ref(c, extended_x);
    Z3_dec_ref(c, y); Z3_dec_ref(c, x);
    Z3_dec_ref(c, maximum); Z3_dec_ref(c, beyond);
    Z3_dec_ref(c, Z3_sort_to_ast(c, sixty_four)); Z3_dec_ref(c, Z3_sort_to_ast(c, wide));
    Z3_dec_ref(c, Z3_sort_to_ast(c, integer)); Z3_dec_ref(c, Z3_sort_to_ast(c, three));
    Z3_del_context(c);
    return 0;
}
