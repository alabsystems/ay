// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/* FP(3,3) has six IEEE bits, with subnormal quantum 2^-4. The pinned
   double constructor clamps exponents below the normal range instead of
   converting them to these subnormal encodings. Construct the exact inputs
   independently so the arithmetic checks exercise actual halfway cases. */
static Z3_ast rounding_subnormal(Z3_context c, Z3_sort sort, unsigned bits) {
    Z3_sort encoding = Z3_mk_bv_sort(c, 6); HOLD_SORT(c, encoding);
    if (!encoding) return NULL;
    Z3_ast numeral = Z3_mk_unsigned_int64(c, bits, encoding); HOLD(c, numeral);
    if (!numeral) return NULL;
    Z3_ast value = Z3_mk_fpa_to_fp_bv(c, numeral, sort); HOLD(c, value);
    return value;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("float.rounding.context-created", c != NULL);
    Z3_sort small = Z3_mk_fpa_sort(c, 3, 3); HOLD_SORT(c, small);
    Z3_sort rm_sort = Z3_mk_fpa_rounding_mode_sort(c); HOLD_SORT(c, rm_sort);
    Z3_ast modes[5];
    modes[0] = Z3_mk_fpa_rne(c); HOLD(c, modes[0]);
    modes[1] = Z3_mk_fpa_rna(c); HOLD(c, modes[1]);
    modes[2] = Z3_mk_fpa_rtp(c); HOLD(c, modes[2]);
    modes[3] = Z3_mk_fpa_rtn(c); HOLD(c, modes[3]);
    modes[4] = Z3_mk_fpa_rtz(c); HOLD(c, modes[4]);
    int distinct = small && rm_sort;
    for (unsigned i = 0; i < 5; ++i) {
        distinct &= modes[i] && Z3_is_eq_sort(c, Z3_get_sort(c, modes[i]), rm_sort);
        for (unsigned j = 0; j < i; ++j) distinct &= modes[i] && modes[j] && !Z3_is_eq_ast(c, modes[i], modes[j]);
    }
    CHECK("float.rounding.five-distinct-modes", distinct);
    /* In FP(3,3), 1.125 is exactly halfway between 1 and 1.25. */
    Z3_ast one = fp_number(c, small, 1.0);
    Z3_ast negative_one = fp_number(c, small, -1.0);
    Z3_ast eighth = rounding_subnormal(c, small, 2);
    Z3_ast negative_eighth = rounding_subnormal(c, small, 34);
    Z3_ast quarter_up = fp_number(c, small, 1.25);
    Z3_ast negative_quarter_up = fp_number(c, small, -1.25);
    Z3_ast positive_expected[5] = {one, quarter_up, quarter_up, one, one};
    Z3_ast negative_expected[5] = {negative_one, negative_quarter_up, negative_one, negative_quarter_up, negative_one};
    int positive = one && negative_one && eighth && negative_eighth && quarter_up && negative_quarter_up;
    int negative = positive;
    if (positive) for (unsigned i = 0; i < 5; ++i) {
        positive &= fp_exact(c, Z3_mk_fpa_add(c, modes[i], one, eighth), positive_expected[i]);
        negative &= fp_exact(c, Z3_mk_fpa_add(c, modes[i], negative_one, negative_eighth), negative_expected[i]);
    }
    CHECK("float.rounding.positive-halfway", positive);
    CHECK("float.rounding.negative-halfway", negative);
    Z3_ast two = fp_number(c, small, 2.0);
    Z3_ast three = fp_number(c, small, 3.0);
    Z3_ast four = fp_number(c, small, 4.0);
    Z3_ast six = fp_number(c, small, 6.0);
    Z3_ast one_half = fp_number(c, small, 1.5);
    CHECK("float.rounding.exact-arithmetic", two && three && four && six && one_half &&
          fp_exact(c, Z3_mk_fpa_sub(c, modes[0], three, one), two) &&
          fp_exact(c, Z3_mk_fpa_mul(c, modes[0], two, three), six) &&
          fp_exact(c, Z3_mk_fpa_div(c, modes[0], three, two), one_half) &&
          fp_exact(c, Z3_mk_fpa_sqrt(c, modes[0], four), two));
    Z3_ast min_subnormal = rounding_subnormal(c, small, 1);
    Z3_ast positive_zero = Z3_mk_fpa_zero(c, small, false); HOLD(c, positive_zero);
    /* Binary32 keeps the exact fused residual normal: (1+a)(1-a)-1=-a*a,
       a=2^-23. Rounding the multiplication first loses that residual. */
    Z3_sort fused_sort = Z3_mk_fpa_sort_single(c); HOLD_SORT(c, fused_sort);
    CHECK("float.rounding.fused-sort-created", fused_sort != NULL);
    Z3_ast fused_left = fp_number(c, fused_sort, 1.0 + 0x1p-23);
    Z3_ast fused_right = fp_number(c, fused_sort, 1.0 - 0x1p-23);
    Z3_ast fused_minus_one = fp_number(c, fused_sort, -1.0);
    Z3_ast fused_exact = fp_number(c, fused_sort, -0x1p-46);
    Z3_ast fused_zero = Z3_mk_fpa_zero(c, fused_sort, false); HOLD(c, fused_zero);
    CHECK("float.rounding.fused-operands-created", fused_left && fused_right && fused_minus_one && fused_exact && fused_zero);
    Z3_ast rounded_product = Z3_mk_fpa_mul(c, modes[0], fused_left, fused_right); HOLD(c, rounded_product);
    CHECK("float.rounding.fused-versus-separate", min_subnormal && positive_zero && rounded_product &&
          fp_exact(c, Z3_mk_fpa_fma(c, modes[0], fused_left, fused_right, fused_minus_one), fused_exact) &&
          fp_exact(c, Z3_mk_fpa_add(c, modes[0], rounded_product, fused_minus_one), fused_zero));
    Z3_ast negative_zero = Z3_mk_fpa_zero(c, small, true); HOLD(c, negative_zero);
    CHECK("float.rounding.cancellation-zero-sign", negative_zero && fp_exact(c, Z3_mk_fpa_add(c, modes[0], one, negative_one), positive_zero) &&
          fp_exact(c, Z3_mk_fpa_add(c, modes[3], one, negative_one), negative_zero) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, negative_zero), 32));
    Z3_ast maximum = fp_number(c, small, 14.0);
    Z3_ast infinity = Z3_mk_fpa_inf(c, small, false); HOLD(c, infinity);
    CHECK("float.rounding.overflow-direction", maximum && infinity && fp_exact(c, Z3_mk_fpa_mul(c, modes[0], maximum, two), infinity) &&
          fp_exact(c, Z3_mk_fpa_mul(c, modes[4], maximum, two), maximum));
    CHECK("float.rounding.underflow-halfway", fp_exact(c, Z3_mk_fpa_div(c, modes[0], min_subnormal, two), positive_zero) &&
          fp_exact(c, Z3_mk_fpa_div(c, modes[1], min_subnormal, two), min_subnormal));
    Z3_ast two_half = fp_number(c, small, 2.5);
    Z3_ast negative_two_half = fp_number(c, small, -2.5);
    Z3_ast negative_two = fp_number(c, small, -2.0);
    Z3_ast negative_three = fp_number(c, small, -3.0);
    Z3_ast integral_positive[5] = {two, three, three, two, two};
    Z3_ast integral_negative[5] = {negative_two, negative_three, negative_two, negative_three, negative_two};
    int integral = two_half && negative_two_half && negative_two && negative_three;
    if (integral) for (unsigned i = 0; i < 5; ++i) {
        integral &= fp_exact(c, Z3_mk_fpa_round_to_integral(c, modes[i], two_half), integral_positive[i]) &&
            fp_exact(c, Z3_mk_fpa_round_to_integral(c, modes[i], negative_two_half), integral_negative[i]);
    }
    CHECK("float.rounding.integral-ties-and-directions", integral &&
          Z3_get_error_code(c) == Z3_OK && contract_last_error == Z3_OK);
    Z3_del_context(c);
    return 0;
}
