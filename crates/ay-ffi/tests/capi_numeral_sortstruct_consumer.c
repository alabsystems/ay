// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C consumer for the Z3-compatible numeral-introspection + sort-structure
// getters (group A):
//   Z3_get_numerator / Z3_get_denominator, Z3_get_numeral_double,
//   Z3_get_numeral_rational_int64, Z3_get_numeral_small,
//   Z3_get_numeral_binary_string, Z3_get_string_contents, Z3_get_lstring,
//   Z3_mk_array_sort_n, Z3_get_array_arity, Z3_get_array_sort_domain_n,
//   Z3_get_seq_sort_basis, Z3_get_re_sort_basis,
//   Z3_get_finite_domain_sort_size,
//   Z3_get_tuple_sort_num_fields / _field_decl / _mk_decl.
//
// This single source compiles and runs against BOTH ay-ffi (default) and libz3
// 4.15.4 (`-DAY_TWIN_USE_Z3 -lz3`). Every non-guarded assertion is a value that
// libz3 itself returns for the SAME input, so passing on both engines is the
// cross-check. Blocks guarded by `#ifndef AY_TWIN_USE_Z3` are AY-specific
// documented divergences:
//   - AY canonicalizes n-domain arrays to curried form, so a hand-nested
//     array-of-array is the SAME sort as the n-domain one: it reports the full
//     curried arity (libz3 reports 1) and Z3_get_array_sort_range of an n-ary
//     array is the curried tail. Inherent to the canonical form, not a bug.
// Each is an honest structural difference, never a fabricated value.

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay.h"
#include "ay_z3_compat.h"
#endif

#include <stdio.h>
#include <string.h>

static int g_pass = 0;
static int g_fail = 0;

#define CHECK_U(actual, expected, what)                                        \
    do {                                                                       \
        unsigned a_ = (unsigned)(actual);                                      \
        unsigned e_ = (unsigned)(expected);                                    \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %u want %u\n", (what), a_, e_);               \
        }                                                                      \
    } while (0)

#define CHECK_B(actual, expected, what)                                        \
    do {                                                                       \
        int a_ = (actual) ? 1 : 0;                                             \
        int e_ = (expected) ? 1 : 0;                                           \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %d want %d\n", (what), a_, e_);               \
        }                                                                      \
    } while (0)

#define CHECK_S(actual, expected, what)                                        \
    do {                                                                       \
        const char* a_ = (actual);                                             \
        const char* e_ = (expected);                                           \
        if (a_ != NULL && strcmp(a_, e_) == 0) {                               \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %s want %s\n", (what), a_ ? a_ : "(null)",    \
                   e_);                                                        \
        }                                                                      \
    } while (0)

#define CHECK_D(actual, expected, what)                                        \
    do {                                                                       \
        double a_ = (actual);                                                  \
        double e_ = (expected);                                                \
        if (a_ == e_) {                                                        \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("FAIL %s: got %.17g want %.17g\n", (what), a_, e_);         \
        }                                                                      \
    } while (0)

// libz3's default error handler aborts the process; register a no-op so the
// intentionally-invalid probes (e.g. Z3_get_numeral_double on a BV numeral,
// which raises Z3_INVALID_ARG and returns 0.0) behave identically on both
// engines.
#ifdef AY_TWIN_USE_Z3
static void quiet_err(Z3_context c, Z3_error_code e) {
    (void)c;
    (void)e;
}
#else
static void quiet_err(Z3_context c, unsigned int e) {
    (void)c;
    (void)e;
}
#endif

// Z3's returned strings share an internal buffer; copy before a second call.
static void copy_str(char* dst, size_t cap, const char* src) {
    if (src == NULL) {
        dst[0] = '\0';
        return;
    }
    strncpy(dst, src, cap - 1);
    dst[cap - 1] = '\0';
}

static void test_numerator_denominator(Z3_context c) {
    char num[64], den[64];
    Z3_ast r = Z3_mk_real(c, 3, 4);
    copy_str(num, sizeof num, Z3_get_numeral_string(c, Z3_get_numerator(c, r)));
    copy_str(den, sizeof den,
             Z3_get_numeral_string(c, Z3_get_denominator(c, r)));
    CHECK_S(num, "3", "numerator(3/4)");
    CHECK_S(den, "4", "denominator(3/4)");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_sort(c, Z3_get_numerator(c, r))),
            Z3_INT_SORT, "numerator sort is Int");

    Z3_ast neg = Z3_mk_numeral(c, "-7/2", Z3_mk_real_sort(c));
    copy_str(num, sizeof num,
             Z3_get_numeral_string(c, Z3_get_numerator(c, neg)));
    copy_str(den, sizeof den,
             Z3_get_numeral_string(c, Z3_get_denominator(c, neg)));
    CHECK_S(num, "-7", "numerator(-7/2)");
    CHECK_S(den, "2", "denominator(-7/2)");

    Z3_ast i5 = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
    copy_str(num, sizeof num,
             Z3_get_numeral_string(c, Z3_get_numerator(c, i5)));
    copy_str(den, sizeof den,
             Z3_get_numeral_string(c, Z3_get_denominator(c, i5)));
    CHECK_S(num, "5", "numerator(int 5)");
    CHECK_S(den, "1", "denominator(int 5)");
}

static void test_numeral_double(Z3_context c) {
    CHECK_D(Z3_get_numeral_double(c, Z3_mk_real(c, 3, 4)), 0.75,
            "double(3/4)");
    CHECK_D(Z3_get_numeral_double(c, Z3_mk_int(c, 5, Z3_mk_int_sort(c))), 5.0,
            "double(int 5)");
    CHECK_D(Z3_get_numeral_double(c, Z3_mk_real(c, 1, 3)), 1.0 / 3.0,
            "double(1/3) is nearest double");
    // BV numeral: Z3_INVALID_ARG, result 0.0 on both engines.
    Z3_ast bv = Z3_mk_numeral(c, "10", Z3_mk_bv_sort(c, 8));
    CHECK_D(Z3_get_numeral_double(c, bv), 0.0, "double(bv) is error 0.0");
}

static void test_rational_int64_and_small(Z3_context c) {
    int64_t n = 0, d = 0;
    CHECK_B(Z3_get_numeral_rational_int64(c, Z3_mk_real(c, 3, 4), &n, &d), 1,
            "rational_int64(3/4) succeeds");
    CHECK_B(n == 3 && d == 4, 1, "rational_int64(3/4) = 3/4");
    CHECK_B(Z3_get_numeral_small(c, Z3_mk_int64(c, -5, Z3_mk_int_sort(c)), &n,
                                 &d),
            1, "small(-5) succeeds");
    CHECK_B(n == -5 && d == 1, 1, "small(-5) = -5/1");
    // BV numerals report (value, 1) on both engines.
    Z3_ast bv = Z3_mk_numeral(c, "10", Z3_mk_bv_sort(c, 8));
    CHECK_B(Z3_get_numeral_rational_int64(c, bv, &n, &d), 1,
            "rational_int64(bv 10) succeeds");
    CHECK_B(n == 10 && d == 1, 1, "rational_int64(bv 10) = 10/1");
    // Non-numeral: false.
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "ri64x"),
                           Z3_mk_int_sort(c));
    CHECK_B(Z3_get_numeral_rational_int64(c, x, &n, &d), 0,
            "rational_int64(non-numeral) is false");
}

static void test_binary_string(Z3_context c) {
    char buf[128];
    Z3_ast bv = Z3_mk_numeral(c, "10", Z3_mk_bv_sort(c, 8));
    copy_str(buf, sizeof buf, Z3_get_numeral_binary_string(c, bv));
    CHECK_S(buf, "1010", "binary(bv 10)");
    Z3_ast bv0 = Z3_mk_numeral(c, "0", Z3_mk_bv_sort(c, 4));
    copy_str(buf, sizeof buf, Z3_get_numeral_binary_string(c, bv0));
    CHECK_S(buf, "0", "binary(bv 0)");
    Z3_ast i5 = Z3_mk_int(c, 5, Z3_mk_int_sort(c));
    copy_str(buf, sizeof buf, Z3_get_numeral_binary_string(c, i5));
    CHECK_S(buf, "101", "binary(int 5)");
}

static void test_string_contents(Z3_context c) {
    Z3_ast s = Z3_mk_string(c, "hive");
    unsigned len = Z3_get_string_length(c, s);
    CHECK_U(len, 4, "string length of \"hive\"");
    unsigned contents[4] = {0, 0, 0, 0};
    Z3_get_string_contents(c, s, len, contents);
    CHECK_U(contents[0], 104, "contents[0] == 'h'");
    CHECK_U(contents[1], 105, "contents[1] == 'i'");
    CHECK_U(contents[2], 118, "contents[2] == 'v'");
    CHECK_U(contents[3], 101, "contents[3] == 'e'");
    unsigned blen = 999;
    const char* raw = Z3_get_lstring(c, s, &blen);
    CHECK_U(blen, 4, "lstring byte length");
    CHECK_B(raw != NULL && strncmp(raw, "hive", 4) == 0, 1, "lstring bytes");
}

static void test_array_structure(Z3_context c) {
    Z3_sort int_s = Z3_mk_int_sort(c);
    Z3_sort bool_s = Z3_mk_bool_sort(c);
    Z3_sort real_s = Z3_mk_real_sort(c);
    Z3_sort doms[2];
    doms[0] = int_s;
    doms[1] = bool_s;
    Z3_sort arr2 = Z3_mk_array_sort_n(c, 2, doms, real_s);
    CHECK_B(arr2 != NULL, 1, "mk_array_sort_n(2) builds a sort");
    CHECK_U(Z3_get_array_arity(c, arr2), 2, "2-D array arity");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_array_sort_domain_n(c, arr2, 0)),
            Z3_INT_SORT, "2-D array domain 0 is Int");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_array_sort_domain_n(c, arr2, 1)),
            Z3_BOOL_SORT, "2-D array domain 1 is Bool");

    Z3_sort arr1 = Z3_mk_array_sort(c, bool_s, int_s);
    CHECK_U(Z3_get_array_arity(c, arr1), 1, "1-D array arity");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_array_sort_domain_n(c, arr1, 0)),
            Z3_BOOL_SORT, "1-D array domain 0 is Bool");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_array_sort_range(c, arr1)), Z3_INT_SORT,
            "1-D array range is Int");

#ifndef AY_TWIN_USE_Z3
    // Documented divergence: AY canonicalizes n-ary arrays to curried form, so
    // a hand-nested array-of-array is the SAME sort as the mk_array_sort_n one
    // and reports the full curried arity (libz3 reports 1 for hand-nested and
    // would report range Real for arr2 where AY reports the curried tail).
    Z3_sort nested = Z3_mk_array_sort(c, int_s, Z3_mk_array_sort(c, bool_s,
                                                                 real_s));
    CHECK_U(Z3_get_array_arity(c, nested), 2, "AY: hand-nested curried arity");
    CHECK_B(Z3_is_eq_sort(c, nested, arr2), 1,
            "AY: hand-nested == mk_array_sort_n sort");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_array_sort_range(c, arr2)),
            Z3_ARRAY_SORT, "AY: n-ary range is the curried tail");
#endif
}

static void test_seq_re_finite(Z3_context c) {
    Z3_sort int_s = Z3_mk_int_sort(c);
    Z3_sort seq_int = Z3_mk_seq_sort(c, int_s);
    CHECK_U(Z3_get_sort_kind(c, Z3_get_seq_sort_basis(c, seq_int)),
            Z3_INT_SORT, "(Seq Int) basis is Int");

    Z3_sort str_s = Z3_mk_string_sort(c);
    Z3_sort re = Z3_mk_re_sort(c, str_s);
    Z3_sort re_basis = Z3_get_re_sort_basis(c, re);
    CHECK_B(re_basis != NULL, 1, "re basis exists");
    CHECK_U(Z3_get_sort_kind(c, re_basis), Z3_SEQ_SORT,
            "re basis is the string/seq sort");

    uint64_t sz = 123;
    CHECK_B(Z3_get_finite_domain_sort_size(c, int_s, &sz), 0,
            "Int is not a finite-domain sort");
    CHECK_U((unsigned)sz, 0, "finite-domain size slot is 0");

    // The String sort is a sequence of characters on both engines, so its basis
    // is the Char sort. (This was once an AY divergence returning NULL; AY now
    // reports its real Char sort, so the check is shared.)
    Z3_sort str_basis = Z3_get_seq_sort_basis(c, str_s);
    CHECK_B(str_basis != NULL, 1, "String-sort basis exists");
    CHECK_U(Z3_get_sort_kind(c, str_basis), Z3_CHAR_SORT,
            "String-sort basis is the Char sort");
}

static void test_tuple_introspection(Z3_context c) {
    Z3_sort int_s = Z3_mk_int_sort(c);
    Z3_sort real_s = Z3_mk_real_sort(c);
    Z3_symbol fnames[2];
    fnames[0] = Z3_mk_string_symbol(c, "fst");
    fnames[1] = Z3_mk_string_symbol(c, "snd");
    Z3_sort fsorts[2];
    fsorts[0] = int_s;
    fsorts[1] = real_s;
    unsigned refs[2] = {0, 0};
    Z3_constructor ctor = Z3_mk_constructor(
        c, Z3_mk_string_symbol(c, "mk-pair"),
        Z3_mk_string_symbol(c, "is-pair"), 2, fnames, fsorts, refs);
    Z3_constructor ctors[1];
    ctors[0] = ctor;
    Z3_sort pair = Z3_mk_datatype(c, Z3_mk_string_symbol(c, "Pair"), 1, ctors);
    CHECK_B(pair != NULL, 1, "single-ctor datatype (tuple) built");

    CHECK_U(Z3_get_tuple_sort_num_fields(c, pair), 2, "tuple num_fields");

    char buf[64];
    Z3_func_decl f0 = Z3_get_tuple_sort_field_decl(c, pair, 0);
    copy_str(buf, sizeof buf, Z3_get_symbol_string(c, Z3_get_decl_name(c, f0)));
    CHECK_S(buf, "fst", "tuple field 0 decl name");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, f0)), Z3_INT_SORT,
            "tuple field 0 range is Int");

    Z3_func_decl f1 = Z3_get_tuple_sort_field_decl(c, pair, 1);
    copy_str(buf, sizeof buf, Z3_get_symbol_string(c, Z3_get_decl_name(c, f1)));
    CHECK_S(buf, "snd", "tuple field 1 decl name");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, f1)), Z3_REAL_SORT,
            "tuple field 1 range is Real");

    Z3_func_decl mk = Z3_get_tuple_sort_mk_decl(c, pair);
    copy_str(buf, sizeof buf, Z3_get_symbol_string(c, Z3_get_decl_name(c, mk)));
    CHECK_S(buf, "mk-pair", "tuple mk decl name");
    CHECK_U(Z3_get_arity(c, mk), 2, "tuple mk decl arity");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_range(c, mk)), Z3_DATATYPE_SORT,
            "tuple mk decl range is the datatype");

    // The mk decl is REAL: applying it yields a term of the tuple sort.
    Z3_ast args[2];
    args[0] = Z3_mk_int(c, 1, int_s);
    args[1] = Z3_mk_numeral(c, "1/2", real_s);
    Z3_ast t = Z3_mk_app(c, mk, 2, args);
    CHECK_B(t != 0, 1, "mk decl applies");
    CHECK_U(Z3_get_sort_kind(c, Z3_get_sort(c, t)), Z3_DATATYPE_SORT,
            "applied tuple term has datatype sort");

    Z3_del_constructor(c, ctor);
}

// The error code reports the LAST call, and is cleared on entry to the next one
// (every entry point except the error accessors themselves resets it). A
// consumer that error-checks after each call must never see a stale error from
// an earlier one. Both engines agree; AY used to latch the first error forever.
static void test_error_code_lifecycle(Z3_context c) {
    Z3_ast neg = Z3_mk_numeral(c, "-5", Z3_mk_int_sort(c));
    Z3_get_numeral_binary_string(c, neg);  // negative -> no binary rendering
    CHECK_U(Z3_get_error_code(c), Z3_INVALID_ARG, "failing call sets INVALID_ARG");
    // Reading the code must not clear it.
    CHECK_U(Z3_get_error_code(c), Z3_INVALID_ARG, "reading the error preserves it");
    Z3_ast bv = Z3_mk_numeral(c, "10", Z3_mk_bv_sort(c, 8));
    Z3_get_numeral_binary_string(c, bv);  // succeeds
    CHECK_U(Z3_get_error_code(c), Z3_OK, "a later successful call clears the error");
}

int main(void) {
    Z3_config cfg = Z3_mk_config();
    Z3_context c = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(c, quiet_err);

    test_numerator_denominator(c);
    test_numeral_double(c);
    test_rational_int64_and_small(c);
    test_binary_string(c);
    test_string_contents(c);
    test_array_structure(c);
    test_seq_re_finite(c);
    test_tuple_introspection(c);
    test_error_code_lifecycle(c);

    Z3_del_context(c);

    printf("%d passed, %d failed\n", g_pass, g_fail);
    if (g_fail == 0) {
        printf("numeral-sortstruct consumer tests passed\n");
        return 0;
    }
    return 1;
}
