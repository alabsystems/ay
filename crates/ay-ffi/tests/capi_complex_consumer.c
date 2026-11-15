// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#ifdef AY_TWIN_USE_Z3
#include <z3.h>
#else
#include "ay_z3_compat.h"
#endif

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

static void ignore_error(Z3_context c, Z3_error_code code) {
    (void)c;
    (void)code;
}

static void rational(Z3_context c, Z3_ast value, int64_t numerator, int64_t denominator) {
    int64_t actual_numerator = 0, actual_denominator = 0;
    Z3_ast simplified = Z3_simplify(c, value);
    assert(simplified);
    assert(Z3_get_numeral_rational_int64(c, simplified, &actual_numerator, &actual_denominator));
    assert(actual_numerator == numerator);
    assert(actual_denominator == denominator);
}

int main(void) {
    Z3_config config = Z3_mk_config();
    Z3_context c = Z3_mk_context(config);
    Z3_del_config(config);
    Z3_set_error_handler(c, ignore_error);
    Z3_sort complex = Z3_mk_complex_sort(c);
    assert(complex && Z3_get_sort_kind(c, complex) == Z3_COMPLEX_SORT);
    Z3_sort integers = Z3_mk_int_sort(c);
    Z3_ast one = Z3_mk_int(c, 1, integers);
    Z3_ast two = Z3_mk_int(c, 2, integers);
    Z3_ast three = Z3_mk_int(c, 3, integers);
    Z3_ast minus_four = Z3_mk_int(c, -4, integers);
    Z3_ast z = Z3_mk_complex(c, one, two);
    assert(z && Z3_is_eq_sort(c, Z3_get_sort(c, z), complex));
    assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, z))) == Z3_OP_COMPLEX);
    Z3_ast symbolic = Z3_mk_const(c, Z3_mk_string_symbol(c, "z"), complex);
    Z3_ast real = Z3_mk_real_part(c, symbolic);
    Z3_ast imaginary = Z3_mk_imag_part(c, symbolic);
    assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, real))) == Z3_OP_REAL_PART);
    assert(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, imaginary))) == Z3_OP_IMAG_PART);
    Z3_ast factors[] = {z, z};
    Z3_ast square = Z3_mk_mul(c, 2, factors);
    rational(c, Z3_mk_real_part(c, square), -3, 1);
    rational(c, Z3_mk_imag_part(c, square), 4, 1);
    Z3_ast divisor = Z3_mk_complex(c, three, minus_four);
    Z3_ast quotient = Z3_mk_div(c, z, divisor);
    rational(c, Z3_mk_real_part(c, quotient), -1, 5);
    rational(c, Z3_mk_imag_part(c, quotient), 2, 5);
    Z3_ast subtrahends[] = {Z3_mk_real(c, 1, 1), one, z};
    Z3_ast difference = Z3_mk_sub(c, 3, subtrahends);
    rational(c, Z3_mk_real_part(c, difference), -1, 1);
    rational(c, Z3_mk_imag_part(c, difference), -2, 1);
    Z3_ast bits = Z3_mk_unsigned_int(c, 1, Z3_mk_bv_sort(c, 8));
    assert(!Z3_mk_complex(c, bits, one));
    assert(Z3_get_error_code(c) == Z3_EXCEPTION);
    Z3_del_context(c);
    puts("Complex C construction, arithmetic and introspection passed");
    return 0;
}
