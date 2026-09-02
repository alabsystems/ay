// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Additional exact-Z3-5.0.0 family probes. This file intentionally includes
// only the stock header and can be compiled unchanged against either library.

#ifndef _GNU_SOURCE
#define _GNU_SOURCE 1
#endif

#include "z3.h"

#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define AY_MAX_CALLABILITY_MARKERS 805

static const char *ay_called[AY_MAX_CALLABILITY_MARKERS];
static size_t ay_called_count;

static void ay_mark_call(const char *name) {
    for (size_t i = 0; i < ay_called_count; ++i) {
        if (strcmp(ay_called[i], name) == 0) {
            return;
        }
    }
    if (ay_called_count >= AY_MAX_CALLABILITY_MARKERS) {
        fputs("callability marker capacity exceeded\n", stderr);
        abort();
    }
    ay_called[ay_called_count++] = name;
}

#define AY_CALL(function, arguments) (ay_mark_call(#function), function arguments)

static int ay_compare_called(const void *left, const void *right) {
    const char *const *lhs = left;
    const char *const *rhs = right;
    return strcmp(*lhs, *rhs);
}

static void ay_print_callability(void) {
    qsort(ay_called, ay_called_count, sizeof(ay_called[0]), ay_compare_called);
    for (size_t i = 0; i < ay_called_count; ++i) {
        printf("AY-CALL %s\n", ay_called[i]);
    }
}

static int ay_verify_loaded_library(const char *expected) {
    if (expected && strcmp(expected, "--static") == 0) {
        return 1;
    }
    Dl_info info;
    if (!expected || dladdr((const void *)Z3_get_full_version, &info) == 0 ||
        !info.dli_fname) {
        return 0;
    }
    char *actual_path = realpath(info.dli_fname, NULL);
    char *expected_path = realpath(expected, NULL);
    int matches = actual_path && expected_path &&
                  strcmp(actual_path, expected_path) == 0;
    free(actual_path);
    free(expected_path);
    return matches;
}

#define CHECK(value)                                                           \
    do {                                                                       \
        if (!(value)) {                                                        \
            fprintf(stderr, "check failed at %s:%d: %s\n", __FILE__, __LINE__, \
                    #value);                                                   \
            return 1;                                                          \
        }                                                                      \
    } while (0)

static int bitvector_family(Z3_context c) {
    Z3_sort bv8 = AY_CALL(Z3_mk_bv_sort, (c, 8));
    Z3_ast x = AY_CALL(Z3_mk_unsigned_int64, (c, 5, bv8));
    Z3_ast y = AY_CALL(Z3_mk_unsigned_int64, (c, 3, bv8));
    bool bits[8] = {true, false, true, false, false, false, false, false};

    CHECK(AY_CALL(Z3_mk_bv_numeral, (c, 8, bits)));
    CHECK(AY_CALL(Z3_mk_bvnot, (c, x)));
    CHECK(AY_CALL(Z3_mk_bvredand, (c, x)));
    CHECK(AY_CALL(Z3_mk_bvredor, (c, x)));
    CHECK(AY_CALL(Z3_mk_bvnand, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvnor, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvxnor, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvneg, (c, x)));
    CHECK(AY_CALL(Z3_mk_bvsub, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsdiv, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvurem, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsrem, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsmod, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvuge, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvugt, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsge, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsgt, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_ext_rotate_left, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_ext_rotate_right, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvadd_no_overflow, (c, x, y, false)));
    CHECK(AY_CALL(Z3_mk_bvadd_no_underflow, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsub_no_overflow, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvsub_no_underflow, (c, x, y, false)));
    CHECK(AY_CALL(Z3_mk_bvsdiv_no_overflow, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_bvneg_no_overflow, (c, x)));
    CHECK(AY_CALL(Z3_mk_bvmul_no_overflow, (c, x, y, false)));
    CHECK(AY_CALL(Z3_mk_bvmul_no_underflow, (c, x, y)));
    CHECK(AY_CALL(Z3_mk_ubv_to_str, (c, x)));
    CHECK(AY_CALL(Z3_mk_sbv_to_str, (c, x)));
    return 0;
}

static int string_regex_family(Z3_context c) {
    unsigned codepoints[3] = {'a', 'b', 'c'};
    Z3_ast abc = AY_CALL(Z3_mk_string, (c, "abc"));
    Z3_ast ab = AY_CALL(Z3_mk_lstring, (c, 2, "ab"));
    Z3_ast u32 = AY_CALL(Z3_mk_u32string, (c, 3, codepoints));
    Z3_ast code = AY_CALL(Z3_mk_int, (c, 'A', AY_CALL(Z3_mk_int_sort, (c))));
    Z3_ast from_code = AY_CALL(Z3_mk_string_from_code, (c, code));
    Z3_ast re_abc = AY_CALL(Z3_mk_seq_to_re, (c, abc));
    Z3_sort re_sort = AY_CALL(Z3_get_sort, (c, re_abc));
    Z3_ast regexes[2] = {re_abc, AY_CALL(Z3_mk_seq_to_re, (c, ab))};

    CHECK(abc && ab && u32 && from_code && re_abc && re_sort);
    CHECK(AY_CALL(Z3_mk_string_to_code, (c, from_code)));
    CHECK(AY_CALL(Z3_mk_seq_last_index, (c, abc, ab)));
    CHECK(AY_CALL(Z3_mk_seq_replace_all, (c, abc, ab, u32)));
    CHECK(AY_CALL(Z3_mk_seq_replace_re, (c, abc, re_abc, ab)));
    CHECK(AY_CALL(Z3_mk_seq_replace_re_all, (c, abc, re_abc, ab)));
    CHECK(AY_CALL(Z3_mk_re_star, (c, re_abc)));
    CHECK(AY_CALL(Z3_mk_re_plus, (c, re_abc)));
    CHECK(AY_CALL(Z3_mk_re_option, (c, re_abc)));
    CHECK(AY_CALL(Z3_mk_re_union, (c, 2, regexes)));
    CHECK(AY_CALL(Z3_mk_re_concat, (c, 2, regexes)));
    CHECK(AY_CALL(Z3_mk_re_range, (c, AY_CALL(Z3_mk_string, (c, "a")), AY_CALL(Z3_mk_string, (c, "z")))));
    CHECK(AY_CALL(Z3_mk_re_allchar, (c, re_sort)));
    CHECK(AY_CALL(Z3_mk_re_power, (c, re_abc, 2)));
    CHECK(AY_CALL(Z3_mk_re_intersect, (c, 2, regexes)));
    CHECK(AY_CALL(Z3_mk_re_complement, (c, re_abc)));
    CHECK(AY_CALL(Z3_mk_re_diff, (c, regexes[0], regexes[1])));
    CHECK(AY_CALL(Z3_mk_re_empty, (c, re_sort)));
    CHECK(AY_CALL(Z3_mk_re_full, (c, re_sort)));
    CHECK(AY_CALL(Z3_mk_seq_in_re, (c, abc, re_abc)));
    return 0;
}

static int floating_point_family(Z3_context c) {
    Z3_sort f32 = AY_CALL(Z3_mk_fpa_sort_32, (c));
    Z3_ast rm = AY_CALL(Z3_mk_fpa_rne, (c));
    Z3_ast a = AY_CALL(Z3_mk_fpa_numeral_float, (c, 1.5f, f32));
    Z3_ast b = AY_CALL(Z3_mk_fpa_numeral_float, (c, 2.0f, f32));
    Z3_sort bv1 = AY_CALL(Z3_mk_bv_sort, (c, 1));
    Z3_sort bv8 = AY_CALL(Z3_mk_bv_sort, (c, 8));
    Z3_sort bv23 = AY_CALL(Z3_mk_bv_sort, (c, 23));
    Z3_sort bv32 = AY_CALL(Z3_mk_bv_sort, (c, 32));
    Z3_ast sign = AY_CALL(Z3_mk_unsigned_int64, (c, 0, bv1));
    Z3_ast exponent = AY_CALL(Z3_mk_unsigned_int64, (c, 127, bv8));
    Z3_ast significand = AY_CALL(Z3_mk_unsigned_int64, (c, 0, bv23));
    Z3_ast ieee = AY_CALL(Z3_mk_unsigned_int64, (c, UINT64_C(0x3fc00000), bv32));
    int64_t exponent_value = 0;
    uint64_t significand_value = 0;

    CHECK(f32 && rm && a && b);
    CHECK(AY_CALL(Z3_mk_fpa_fp, (c, sign, exponent, significand)));
    CHECK(AY_CALL(Z3_mk_fpa_numeral_int_uint, (c, false, 0, 3, f32)));
    CHECK(AY_CALL(Z3_mk_fpa_numeral_int64_uint64, (c, false, 0, 3, f32)));
    CHECK(AY_CALL(Z3_mk_fpa_abs, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_neg, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_sub, (c, rm, b, a)));
    CHECK(AY_CALL(Z3_mk_fpa_mul, (c, rm, a, b)));
    CHECK(AY_CALL(Z3_mk_fpa_div, (c, rm, b, a)));
    CHECK(AY_CALL(Z3_mk_fpa_rem, (c, b, a)));
    CHECK(AY_CALL(Z3_mk_fpa_min, (c, a, b)));
    CHECK(AY_CALL(Z3_mk_fpa_max, (c, a, b)));
    CHECK(AY_CALL(Z3_mk_fpa_leq, (c, a, b)));
    CHECK(AY_CALL(Z3_mk_fpa_geq, (c, b, a)));
    CHECK(AY_CALL(Z3_mk_fpa_gt, (c, b, a)));
    CHECK(AY_CALL(Z3_mk_fpa_is_normal, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_is_subnormal, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_is_zero, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_is_negative, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_is_positive, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_to_fp_bv, (c, ieee, f32)));
    CHECK(AY_CALL(Z3_mk_fpa_to_ieee_bv, (c, a)));
    CHECK(AY_CALL(Z3_mk_fpa_to_real, (c, a)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_sign_bv, (c, a)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_significand_bv, (c, a)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_exponent_bv, (c, a, false)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_exponent_string, (c, a, false)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_significand_string, (c, a)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_exponent_int64, (c, a, &exponent_value, false)));
    CHECK(AY_CALL(Z3_fpa_get_numeral_significand_uint64, (c, a, &significand_value)));
    (void)AY_CALL(Z3_fpa_is_numeral_negative, (c, a));
    (void)AY_CALL(Z3_fpa_is_numeral_subnormal, (c, a));
    return 0;
}

static int arithmetic_and_introspection_family(Z3_context c) {
    Z3_sort ints = AY_CALL(Z3_mk_int_sort, (c));
    Z3_sort reals = AY_CALL(Z3_mk_real_sort, (c));
    Z3_ast five = AY_CALL(Z3_mk_int, (c, 5, ints));
    Z3_ast two = AY_CALL(Z3_mk_int, (c, 2, ints));
    Z3_ast half = AY_CALL(Z3_mk_real_int64, (c, 1, 2));
    uint64_t value64 = 0;
    unsigned value = 0;

    CHECK(AY_CALL(Z3_mk_mod, (c, five, two)));
    CHECK(AY_CALL(Z3_mk_int2real, (c, five)));
    CHECK(AY_CALL(Z3_mk_real2int, (c, half)));
    CHECK(AY_CALL(Z3_mk_is_int, (c, half)));
    CHECK(AY_CALL(Z3_get_numeral_uint, (c, five, &value)) && value == 5);
    CHECK(AY_CALL(Z3_get_numeral_uint64, (c, five, &value64)) && value64 == 5);
    CHECK(AY_CALL(Z3_is_app, (c, five)));
    CHECK(AY_CALL(Z3_is_numeral_ast, (c, five)));
    CHECK(AY_CALL(Z3_is_well_sorted, (c, five)));
    Z3_sort half_sort = AY_CALL(Z3_get_sort, (c, half));
    CHECK(half_sort == reals);
    CHECK(AY_CALL(Z3_is_eq_sort, (c, half_sort, reals)));
    (void)AY_CALL(Z3_get_estimated_alloc_size, ());
    return 0;
}

int main(int argc, char **argv) {
    CHECK(argc == 2 && ay_verify_loaded_library(argv[1]));
    Z3_config cfg = AY_CALL(Z3_mk_config, ());
    CHECK(cfg);
    Z3_context c = AY_CALL(Z3_mk_context, (cfg));
    AY_CALL(Z3_del_config, (cfg));
    CHECK(c);
    AY_CALL(Z3_set_error_handler, (c, NULL));

    CHECK(bitvector_family(c) == 0);
    CHECK(string_regex_family(c) == 0);
    CHECK(floating_point_family(c) == 0);
    CHECK(arithmetic_and_introspection_family(c) == 0);
    AY_CALL(Z3_interrupt, (c));
    AY_CALL(Z3_del_context, (c));
    ay_print_callability();
    puts("exact Z3 5.1.0 additional family probes passed");
    return 0;
}
