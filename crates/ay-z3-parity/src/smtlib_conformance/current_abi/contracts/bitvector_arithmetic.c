// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

int main(void) {
    Z3_context c = contract_context();
    CHECK("bitvector.arithmetic.context-created", c != NULL);
    Z3_sort three = Z3_mk_bv_sort(c, 3); HOLD_SORT(c, three);
    CHECK("bitvector.arithmetic.sort-created", three && Z3_get_bv_sort_size(c, three) == 3);
    int unary = 1, arithmetic = 1, bitwise = 1, unsigned_order = 1, signed_order = 1;
    for (unsigned a = 0; a < 8; ++a) {
        Z3_ast left = bv_unsigned(c, three, a);
        unary &= bv_value_is(c, Z3_mk_bvnot(c, left), (~a) & 7u) &&
            bv_value_is(c, Z3_mk_bvneg(c, left), (0u - a) & 7u) &&
            bv_value_is(c, Z3_mk_bvredand(c, left), a == 7u) &&
            bv_value_is(c, Z3_mk_bvredor(c, left), a != 0u);
        for (unsigned b = 0; b < 8; ++b) {
            Z3_ast right = bv_unsigned(c, three, b);
            int sa = bv_signed(a, 3), sb = bv_signed(b, 3);
            arithmetic &= bv_value_is(c, Z3_mk_bvadd(c, left, right), (a + b) & 7u) &&
                bv_value_is(c, Z3_mk_bvsub(c, left, right), (a - b) & 7u) &&
                bv_value_is(c, Z3_mk_bvmul(c, left, right), (a * b) & 7u);
            bitwise &= bv_value_is(c, Z3_mk_bvand(c, left, right), a & b) &&
                bv_value_is(c, Z3_mk_bvor(c, left, right), a | b) &&
                bv_value_is(c, Z3_mk_bvxor(c, left, right), a ^ b) &&
                bv_value_is(c, Z3_mk_bvnand(c, left, right), (~(a & b)) & 7u) &&
                bv_value_is(c, Z3_mk_bvnor(c, left, right), (~(a | b)) & 7u) &&
                bv_value_is(c, Z3_mk_bvxnor(c, left, right), (~(a ^ b)) & 7u);
            unsigned_order &= bv_truth_is(c, Z3_mk_bvult(c, left, right), a < b) &&
                bv_truth_is(c, Z3_mk_bvule(c, left, right), a <= b) &&
                bv_truth_is(c, Z3_mk_bvugt(c, left, right), a > b) &&
                bv_truth_is(c, Z3_mk_bvuge(c, left, right), a >= b);
            signed_order &= bv_truth_is(c, Z3_mk_bvslt(c, left, right), sa < sb) &&
                bv_truth_is(c, Z3_mk_bvsle(c, left, right), sa <= sb) &&
                bv_truth_is(c, Z3_mk_bvsgt(c, left, right), sa > sb) &&
                bv_truth_is(c, Z3_mk_bvsge(c, left, right), sa >= sb);
            Z3_dec_ref(c, right);
        }
        Z3_dec_ref(c, left);
    }
    CHECK("bitvector.arithmetic.all-three-bit-unary", unary);
    CHECK("bitvector.arithmetic.all-three-bit-modular", arithmetic);
    CHECK("bitvector.arithmetic.all-three-bit-bitwise", bitwise);
    CHECK("bitvector.arithmetic.all-three-bit-unsigned-order", unsigned_order);
    CHECK("bitvector.arithmetic.all-three-bit-signed-order", signed_order);
    Z3_ast x = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_inverse_x"), three); HOLD(c, x);
    Z3_ast y = Z3_mk_const(c, Z3_mk_string_symbol(c, "bv_inverse_y"), three); HOLD(c, y);
    Z3_ast sum = Z3_mk_bvadd(c, x, y); HOLD(c, sum);
    Z3_ast back = Z3_mk_bvsub(c, sum, y); HOLD(c, back);
    Z3_ast same = Z3_mk_eq(c, back, x); HOLD(c, same);
    CHECK("bitvector.arithmetic.symbolic-modular-inverse", x && y && sum && back && same &&
          bv_unsat(c, Z3_mk_not(c, same)));
    Z3_dec_ref(c, same); Z3_dec_ref(c, back); Z3_dec_ref(c, sum); Z3_dec_ref(c, y); Z3_dec_ref(c, x);
    Z3_dec_ref(c, Z3_sort_to_ast(c, three)); Z3_del_context(c);
    return 0;
}
