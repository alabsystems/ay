// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

static Z3_ast fp_model_value(Z3_context c, Z3_model model, Z3_ast term) {
    if (!model || !term) return NULL;
    Z3_ast value = NULL;
    if (!Z3_model_eval(c, model, term, false, &value) || !value) return NULL;
    HOLD(c, value);
    return value;
}

static int fp_model_nan(Z3_context c, Z3_model model, Z3_ast term) {
    Z3_ast value = fp_model_value(c, model, term);
    if (!value) return 0;
    int correct = Z3_fpa_is_numeral_nan(c, value);
    Z3_dec_ref(c, value);
    return correct;
}

static int fp_model_truth(Z3_context c, Z3_model model, Z3_ast term, Z3_lbool expected) {
    Z3_ast value = fp_model_value(c, model, term);
    if (!value) return 0;
    int correct = Z3_get_bool_value(c, value) == expected;
    Z3_dec_ref(c, value);
    return correct;
}

static int fp_model_negative_zero(Z3_context c, Z3_model model, Z3_ast term) {
    Z3_ast value = fp_model_value(c, model, term);
    if (!value) return 0;
    int correct = Z3_fpa_is_numeral_zero(c, value) && Z3_fpa_is_numeral_negative(c, value) &&
        fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, value), UINT64_C(0x80000000));
    Z3_dec_ref(c, value);
    return correct;
}

int main(void) {
    Z3_context c = contract_context();
    CHECK("float.conversions.context-created", c != NULL);
    Z3_sort single = Z3_mk_fpa_sort_single(c); HOLD_SORT(c, single);
    Z3_sort wide = Z3_mk_fpa_sort_double(c); HOLD_SORT(c, wide);
    Z3_sort real = Z3_mk_real_sort(c); HOLD_SORT(c, real);
    Z3_sort byte = Z3_mk_bv_sort(c, 8); HOLD_SORT(c, byte);
    Z3_sort word = Z3_mk_bv_sort(c, 32); HOLD_SORT(c, word);
    Z3_ast rne = Z3_mk_fpa_rne(c); HOLD(c, rne);
    Z3_ast rtp = Z3_mk_fpa_rtp(c); HOLD(c, rtp);
    Z3_ast rtn = Z3_mk_fpa_rtn(c); HOLD(c, rtn);
    Z3_ast rtz = Z3_mk_fpa_rtz(c); HOLD(c, rtz);
    CHECK("float.conversions.sorts-and-modes", single && wide && real && byte && word && rne && rtp && rtn && rtz);
    Z3_ast one_half = fp_number(c, single, 1.5);
    Z3_ast raw_one_half = Z3_mk_unsigned_int64(c, UINT64_C(0x3fc00000), word); HOLD(c, raw_one_half);
    CHECK("float.conversions.ieee-reinterpretation", one_half && raw_one_half &&
          fp_exact(c, Z3_mk_fpa_to_fp_bv(c, raw_one_half, single), one_half) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, one_half), UINT64_C(0x3fc00000)));
    Z3_ast fraction = Z3_mk_numeral(c, "3/2", real); HOLD(c, fraction);
    CHECK("float.conversions.exact-real-roundtrip", fraction &&
          fp_exact(c, Z3_mk_fpa_to_fp_real(c, rne, fraction, single), one_half) &&
          fp_exact(c, Z3_mk_fpa_to_real(c, one_half), fraction));
    /* 1+2^-24 is exact in binary64 and halfway between binary32 1 and its
       successor. No C host rounding is used to obtain this real numeral. */
    Z3_ast midpoint = Z3_mk_numeral(c, "1.000000059604644775390625", real); HOLD(c, midpoint);
    Z3_ast exact_wide = midpoint ? Z3_mk_fpa_to_fp_real(c, rne, midpoint, wide) : NULL; HOLD(c, exact_wide);
    Z3_ast narrowed_even = exact_wide ? Z3_mk_fpa_to_fp_float(c, rne, exact_wide, single) : NULL; HOLD(c, narrowed_even);
    Z3_ast narrowed_up = exact_wide ? Z3_mk_fpa_to_fp_float(c, rtp, exact_wide, single) : NULL; HOLD(c, narrowed_up);
    CHECK("float.conversions.narrowing-halfway", narrowed_even && narrowed_up &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, narrowed_even), UINT64_C(0x3f800000)) &&
          fp_bits(c, Z3_mk_fpa_to_ieee_bv(c, narrowed_up), UINT64_C(0x3f800001)));
    Z3_ast all_ones = Z3_mk_unsigned_int(c, 255, byte); HOLD(c, all_ones);
    Z3_ast minus_one = fp_number(c, single, -1.0);
    Z3_ast two_fifty_five = fp_number(c, single, 255.0);
    CHECK("float.conversions.signed-unsigned-bv", all_ones && minus_one && two_fifty_five &&
          fp_exact(c, Z3_mk_fpa_to_fp_signed(c, rne, all_ones, single), minus_one) &&
          fp_exact(c, Z3_mk_fpa_to_fp_unsigned(c, rne, all_ones, single), two_fifty_five));
    Z3_ast negative_fraction = fp_number(c, single, -2.75);
    Z3_ast positive_fraction = fp_number(c, single, 2.75);
    CHECK("float.conversions.rounded-integer-directions", negative_fraction && positive_fraction &&
          fp_bits(c, Z3_mk_fpa_to_sbv(c, rtz, negative_fraction, 8), 254) &&
          fp_bits(c, Z3_mk_fpa_to_sbv(c, rtn, negative_fraction, 8), 253) &&
          fp_bits(c, Z3_mk_fpa_to_ubv(c, rtz, positive_fraction, 8), 2) &&
          fp_bits(c, Z3_mk_fpa_to_ubv(c, rtp, positive_fraction, 8), 3));
    Z3_ast minimum_signed = fp_number(c, single, -128.0);
    Z3_ast maximum_signed = fp_number(c, single, 127.0);
    CHECK("float.conversions.in-range-integer-boundaries", minimum_signed && maximum_signed &&
          fp_bits(c, Z3_mk_fpa_to_sbv(c, rne, minimum_signed, 8), 128) &&
          fp_bits(c, Z3_mk_fpa_to_sbv(c, rne, maximum_signed, 8), 127) &&
          fp_bits(c, Z3_mk_fpa_to_ubv(c, rne, two_fifty_five, 8), 255));
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "contract_float_x"), single); HOLD(c, x);
    Z3_ast is_nan = x ? Z3_mk_fpa_is_nan(c, x) : NULL; HOLD(c, is_nan);
    Z3_ast ieee_self_equal = x ? Z3_mk_fpa_eq(c, x, x) : NULL; HOLD(c, ieee_self_equal);
    Z3_ast smt_self_equal = x ? Z3_mk_eq(c, x, x) : NULL; HOLD(c, smt_self_equal);
    Z3_solver solver = Z3_mk_solver(c); if (solver) Z3_solver_inc_ref(c, solver);
    CHECK("float.conversions.solver-created", x && is_nan && ieee_self_equal && smt_self_equal && solver);
    Z3_solver_assert(c, solver, is_nan);
    CHECK("float.conversions.nan-model-satisfiable", Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model nan_model = Z3_solver_get_model(c, solver); if (nan_model) Z3_model_inc_ref(c, nan_model);
    CHECK("float.conversions.model-distinguishes-equalities", nan_model && fp_model_nan(c, nan_model, x) &&
          fp_model_truth(c, nan_model, ieee_self_equal, Z3_L_FALSE) &&
          fp_model_truth(c, nan_model, smt_self_equal, Z3_L_TRUE));
    Z3_solver_push(c, solver);
    Z3_solver_assert(c, solver, ieee_self_equal);
    CHECK("float.conversions.nan-self-equality-unsatisfiable", Z3_solver_check(c, solver) == Z3_L_FALSE &&
          fp_model_nan(c, nan_model, x));
    Z3_ast negative_zero = Z3_mk_fpa_zero(c, single, true); HOLD(c, negative_zero);
    Z3_ast x_is_negative_zero = negative_zero ? Z3_mk_eq(c, x, negative_zero) : NULL; HOLD(c, x_is_negative_zero);
    Z3_solver_reset(c, solver);
    if (x_is_negative_zero) Z3_solver_assert(c, solver, x_is_negative_zero);
    CHECK("float.conversions.signed-zero-model-satisfiable", x_is_negative_zero && Z3_solver_check(c, solver) == Z3_L_TRUE);
    Z3_model zero_model = Z3_solver_get_model(c, solver); if (zero_model) Z3_model_inc_ref(c, zero_model);
    CHECK("float.conversions.independent-retained-models", zero_model && fp_model_negative_zero(c, zero_model, x) &&
          fp_model_truth(c, zero_model, is_nan, Z3_L_FALSE) && fp_model_nan(c, nan_model, x));
    unsigned retained_id = Z3_get_ast_id(c, x);
    Z3_solver_dec_ref(c, solver);
    CHECK("float.conversions.retained-after-solver-release", Z3_get_ast_id(c, x) == retained_id &&
          fp_model_negative_zero(c, zero_model, x) && fp_model_nan(c, nan_model, x) &&
          Z3_get_error_code(c) == Z3_OK && contract_last_error == Z3_OK);
    Z3_model_dec_ref(c, zero_model);
    Z3_model_dec_ref(c, nan_model);
    Z3_del_context(c);
    return 0;
}
