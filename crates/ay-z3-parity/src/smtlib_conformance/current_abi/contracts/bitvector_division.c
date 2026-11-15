// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("bitvector.division.context-created", c != NULL);
    Z3_sort three = Z3_mk_bv_sort(c, 3); HOLD_SORT(c, three);
    CHECK("bitvector.division.sort-created", three && Z3_get_bv_sort_size(c, three) == 3);
    int unsigned_division = 1, signed_division = 1, signed_modulo = 1, shifts = 1, reconstruction = 1;
    for (unsigned a = 0; a < 8; ++a) for (unsigned b = 0; b < 8; ++b) {
        Z3_ast left = bv_unsigned(c, three, a), right = bv_unsigned(c, three, b);
        int sa = bv_signed(a, 3), sb = bv_signed(b, 3);
        /* Explicit SMT bit-vector zero branches; no C division by zero. */
        unsigned uq = b == 0 ? 7u : a / b;
        unsigned ur = b == 0 ? a : a % b;
        int sq = sb == 0 ? (sa < 0 ? 1 : -1) : sa / sb;
        int sr = sb == 0 ? sa : sa % sb;
        int sm = sr;
        if (sb != 0 && sr != 0 && ((sr < 0) != (sb < 0))) sm += sb;
        Z3_ast quotient = Z3_mk_bvudiv(c, left, right); HOLD(c, quotient);
        Z3_ast remainder = Z3_mk_bvurem(c, left, right); HOLD(c, remainder);
        unsigned_division &= bv_value_is(c, quotient, uq) && bv_value_is(c, remainder, ur);
        signed_division &= bv_value_is(c, Z3_mk_bvsdiv(c, left, right), (unsigned)sq & 7u) &&
            bv_value_is(c, Z3_mk_bvsrem(c, left, right), (unsigned)sr & 7u);
        signed_modulo &= bv_value_is(c, Z3_mk_bvsmod(c, left, right), (unsigned)sm & 7u);
        unsigned sl = b >= 3 ? 0u : (a << b) & 7u;
        unsigned lr = b >= 3 ? 0u : a >> b;
        unsigned ar = b >= 3 ? (sa < 0 ? 7u : 0u) :
            ((a >> b) | (sa < 0 ? 7u << (3u - b) : 0u)) & 7u;
        shifts &= bv_value_is(c, Z3_mk_bvshl(c, left, right), sl) &&
            bv_value_is(c, Z3_mk_bvlshr(c, left, right), lr) &&
            bv_value_is(c, Z3_mk_bvashr(c, left, right), ar);
        Z3_ast product = Z3_mk_bvmul(c, quotient, right); HOLD(c, product);
        Z3_ast restored = Z3_mk_bvadd(c, product, remainder); HOLD(c, restored);
        reconstruction &= bv_truth_is(c, Z3_mk_eq(c, restored, left), 1);
        Z3_dec_ref(c, restored); Z3_dec_ref(c, product);
        Z3_dec_ref(c, remainder); Z3_dec_ref(c, quotient);
        Z3_dec_ref(c, right); Z3_dec_ref(c, left);
    }
    CHECK("bitvector.division.all-three-bit-unsigned-including-zero", unsigned_division);
    CHECK("bitvector.division.all-three-bit-signed-including-zero", signed_division);
    CHECK("bitvector.division.all-three-bit-signed-modulo", signed_modulo);
    CHECK("bitvector.division.all-three-bit-shifts-including-oversized", shifts);
    CHECK("bitvector.division.all-three-bit-reconstruction", reconstruction);
    Z3_ast minimum = bv_unsigned(c, three, 4), minus_one = bv_unsigned(c, three, 7);
    CHECK("bitvector.division.signed-minimum-over-minus-one", bv_value_is(c, Z3_mk_bvsdiv(c, minimum, minus_one), 4) &&
          bv_value_is(c, Z3_mk_bvsrem(c, minimum, minus_one), 0) &&
          bv_value_is(c, Z3_mk_bvsmod(c, minimum, minus_one), 0));
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_div_x"), three); HOLD(c, x);
    Z3_ast y = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_div_y"), three); HOLD(c, y);
    Z3_ast quotient = Z3_mk_bvudiv(c, x, y); HOLD(c, quotient);
    Z3_ast remainder = Z3_mk_bvurem(c, x, y); HOLD(c, remainder);
    Z3_ast product = Z3_mk_bvmul(c, quotient, y); HOLD(c, product);
    Z3_ast restored = Z3_mk_bvadd(c, product, remainder); HOLD(c, restored);
    Z3_ast same = Z3_mk_eq(c, restored, x); HOLD(c, same);
    CHECK("bitvector.division.symbolic-reconstruction-including-zero", x && y && quotient && remainder && product && restored && same &&
          bv_unsat(c, Z3_mk_not(c, same)));
    Z3_dec_ref(c, same); Z3_dec_ref(c, restored); Z3_dec_ref(c, product);
    Z3_dec_ref(c, remainder); Z3_dec_ref(c, quotient); Z3_dec_ref(c, y); Z3_dec_ref(c, x);
    Z3_dec_ref(c, minus_one); Z3_dec_ref(c, minimum);
    Z3_dec_ref(c, Z3_sort_to_ast(c, three)); Z3_del_context(c);
    return 0;
}
