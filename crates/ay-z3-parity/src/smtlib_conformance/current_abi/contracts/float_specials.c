// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("float.specials.context-created", c != NULL);
    Z3_sort single = Z3_mk_fpa_sort_single(c); HOLD_SORT(c, single);
    Z3_sort explicit_single = Z3_mk_fpa_sort(c, 8, 24); HOLD_SORT(c, explicit_single);
    Z3_sort wide = Z3_mk_fpa_sort_double(c); HOLD_SORT(c, wide);
    Z3_sort rm_sort = Z3_mk_fpa_rounding_mode_sort(c); HOLD_SORT(c, rm_sort);
    CHECK("float.specials.sort-reflection", single && explicit_single && wide && rm_sort &&
          Z3_is_eq_sort(c, single, explicit_single) && !Z3_is_eq_sort(c, single, wide) &&
          Z3_get_sort_kind(c, single) == Z3_FLOATING_POINT_SORT &&
          Z3_fpa_get_ebits(c, single) == 8 && Z3_fpa_get_sbits(c, single) == 24 &&
          Z3_fpa_get_ebits(c, wide) == 11 && Z3_fpa_get_sbits(c, wide) == 53 &&
          Z3_get_sort_kind(c, rm_sort) == Z3_ROUNDING_MODE_SORT);
    Z3_ast positive_zero = Z3_mk_fpa_zero(c, single, false); HOLD(c, positive_zero);
    Z3_ast negative_zero = Z3_mk_fpa_zero(c, single, true); HOLD(c, negative_zero);
    Z3_ast positive_inf = Z3_mk_fpa_inf(c, single, false); HOLD(c, positive_inf);
    Z3_ast negative_inf = Z3_mk_fpa_inf(c, single, true); HOLD(c, negative_inf);
    Z3_ast nan = Z3_mk_fpa_nan(c, single); HOLD(c, nan);
    Z3_ast one = fp_number(c, single, 1.0);
    CHECK("float.specials.values-created", positive_zero && negative_zero && positive_inf &&
          negative_inf && nan && one && Z3_is_eq_sort(c, Z3_get_sort(c, nan), single));
    CHECK("float.specials.signed-zero-bits", fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, positive_zero), 0) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, negative_zero), UINT64_C(0x80000000)));
    CHECK("float.specials.signed-zero-equality", fp_truth(c, Z3_mk_fpa_eq(c, positive_zero, negative_zero), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_eq(c, positive_zero, negative_zero), Z3_L_FALSE));
    CHECK("float.specials.zero-classification", Z3_fpa_is_numeral(c, positive_zero) &&
          Z3_fpa_is_numeral_zero(c, positive_zero) && Z3_fpa_is_numeral_zero(c, negative_zero) &&
          Z3_fpa_is_numeral_positive(c, positive_zero) && Z3_fpa_is_numeral_negative(c, negative_zero) &&
          fp_truth(c, Z3_mk_fpa_is_zero(c, negative_zero), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_fpa_is_negative(c, negative_zero), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_fpa_is_positive(c, negative_zero), Z3_L_FALSE));
    CHECK("float.specials.infinity-order", Z3_fpa_is_numeral_inf(c, positive_inf) &&
          Z3_fpa_is_numeral_inf(c, negative_inf) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, positive_inf), UINT64_C(0x7f800000)) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, negative_inf), UINT64_C(0xff800000)) &&
          fp_truth(c, Z3_mk_fpa_is_infinite(c, positive_inf), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_fpa_lt(c, negative_inf, one), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_fpa_gt(c, positive_inf, one), Z3_L_TRUE));
    CHECK("float.specials.nan-equality", Z3_fpa_is_numeral_nan(c, nan) &&
          fp_truth(c, Z3_mk_fpa_is_nan(c, nan), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_fpa_eq(c, nan, nan), Z3_L_FALSE) &&
          fp_truth(c, Z3_mk_eq(c, nan, nan), Z3_L_TRUE));
    CHECK("float.specials.nan-unordered", fp_truth(c, Z3_mk_fpa_lt(c, nan, one), Z3_L_FALSE) &&
          fp_truth(c, Z3_mk_fpa_leq(c, nan, one), Z3_L_FALSE) &&
          fp_truth(c, Z3_mk_fpa_geq(c, nan, one), Z3_L_FALSE) &&
          fp_truth(c, Z3_mk_fpa_gt(c, nan, one), Z3_L_FALSE));
    Z3_ast normal = fp_number(c, single, 0x1p-126);
    /* The pinned double constructor clamps an underflowing double exponent;
       use the matching single constructor for this exact single subnormal. */
    Z3_ast subnormal = Z3_mk_fpa_numeral_float(c, 0x1p-149f, single); HOLD(c, subnormal);
    CHECK("float.specials.normal-subnormal-boundary", normal && subnormal &&
          Z3_fpa_is_numeral_normal(c, normal) && !Z3_fpa_is_numeral_subnormal(c, normal) &&
          Z3_fpa_is_numeral_subnormal(c, subnormal) && !Z3_fpa_is_numeral_normal(c, subnormal) &&
          fp_truth(c, Z3_mk_fpa_is_normal(c, normal), Z3_L_TRUE) &&
          fp_truth(c, Z3_mk_fpa_is_subnormal(c, subnormal), Z3_L_TRUE) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, normal), UINT64_C(0x00800000)) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, subnormal), 1));
    CHECK("float.specials.negation-absolute-value", fp_exact(c, Z3_mk_fpa_neg(c, positive_zero), negative_zero) &&
          fp_exact(c, Z3_mk_fpa_abs(c, negative_zero), positive_zero) &&
          fp_exact(c, Z3_mk_fpa_neg(c, positive_inf), negative_inf) &&
          Z3_get_error_code(c) == Z3_OK && contract_last_error == Z3_OK);
    Z3_del_context(c);
    return 0;
}
