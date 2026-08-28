// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =======================================================================
// Bitvector operation tests
// =======================================================================

#[test]
fn test_bvadd_constant_folding() {
    let mut store = TermStore::new();

    // #x01 + #x02 = #x03
    let a = store.mk_bitvec(BigInt::from(1), 8);
    let b = store.mk_bitvec(BigInt::from(2), 8);
    let expected = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvadd(vec![a, b]);
    assert_eq!(result, expected);

    // Overflow: #xFF + #x01 = #x00 (for 8-bit)
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let overflow_result = store.mk_bvadd(vec![ff, one]);
    assert_eq!(overflow_result, zero);
}

#[test]
fn test_bvadd_identity() {
    let mut store = TermStore::new();

    // x + 0 = x
    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result = store.mk_bvadd(vec![x, zero]);
    assert_eq!(result, x);

    // 0 + x = x
    let result2 = store.mk_bvadd(vec![zero, x]);
    assert_eq!(result2, x);
}

#[test]
fn test_bvadd_cancels_bvsub_rhs() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(32));
    let y = store.mk_var("y", Sort::bitvec(32));

    let y_minus_x = store.mk_bvsub(vec![y, x]);
    let result = store.mk_bvadd(vec![x, y_minus_x]);
    assert_eq!(result, y);

    let y_minus_x_again = store.mk_bvsub(vec![y, x]);
    let result_commuted = store.mk_bvadd(vec![y_minus_x_again, x]);
    assert_eq!(result_commuted, y);
}

#[test]
fn test_bvsub_constant_folding() {
    let mut store = TermStore::new();

    // #x05 - #x03 = #x02
    let a = store.mk_bitvec(BigInt::from(5), 8);
    let b = store.mk_bitvec(BigInt::from(3), 8);
    let expected = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvsub(vec![a, b]);
    assert_eq!(result, expected);

    // Underflow: #x01 - #x02 = #xFF (for 8-bit)
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let underflow_result = store.mk_bvsub(vec![one, two]);
    assert_eq!(underflow_result, ff);
}

#[test]
fn test_bvsub_identity_and_self() {
    let mut store = TermStore::new();

    // x - 0 = x
    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result = store.mk_bvsub(vec![x, zero]);
    assert_eq!(result, x);

    // x - x = 0
    let self_sub = store.mk_bvsub(vec![x, x]);
    assert_eq!(self_sub, zero);
}

#[test]
fn test_bvmul_constant_folding() {
    let mut store = TermStore::new();

    // #x03 * #x04 = #x0C
    let a = store.mk_bitvec(BigInt::from(3), 8);
    let b = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(12), 8);
    let result = store.mk_bvmul(vec![a, b]);
    assert_eq!(result, expected);

    // Overflow: #x80 * #x02 = #x00 (for 8-bit)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let overflow_result = store.mk_bvmul(vec![x80, two]);
    assert_eq!(overflow_result, zero);
}

#[test]
fn test_bvmul_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x * 0 = 0
    let result = store.mk_bvmul(vec![x, zero]);
    assert_eq!(result, zero);

    // 0 * x = 0
    let result2 = store.mk_bvmul(vec![zero, x]);
    assert_eq!(result2, zero);

    // x * 1 = x
    let result3 = store.mk_bvmul(vec![x, one]);
    assert_eq!(result3, x);

    // 1 * x = x
    let result4 = store.mk_bvmul(vec![one, x]);
    assert_eq!(result4, x);
}

#[test]
fn test_bvmul_all_ones_is_neg() {
    // x * -1 = -x (all-ones constant rewrites to bvneg, eliminating the
    // multiplier circuit — the negate-by-multiply idiom).
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let neg_one = store.mk_bitvec(BigInt::from(0xFFu32), 8); // -1 mod 2^8
    let expected = store.mk_bvneg(x);

    // x * -1 = -x
    let result = store.mk_bvmul(vec![x, neg_one]);
    assert_eq!(result, expected, "bvmul(x, -1) should rewrite to bvneg(x)");

    // -1 * x = -x (commutative)
    let result2 = store.mk_bvmul(vec![neg_one, x]);
    assert_eq!(result2, expected, "bvmul(-1, x) should rewrite to bvneg(x)");

    // 64-bit: this is the MUL Xd,Xn,#-1 ≡ NEG identity the proof DB needs.
    let x64 = store.mk_var("x64", Sort::bitvec(64));
    let neg_one_64 = store.mk_bitvec((BigInt::from(1u8) << 64u32) - BigInt::from(1u8), 64);
    let neg_x64 = store.mk_bvneg(x64);
    let result64 = store.mk_bvmul(vec![neg_one_64, x64]);
    assert_eq!(
        result64, neg_x64,
        "bvmul(-1, x) at 64-bit should be bvneg(x)"
    );
}

#[test]
fn test_bvmul_neg_power_of_two_is_neg_shift() {
    // x * -(2^k) = -(x * 2^k) = -(x << k). The negative-power-of-two constant
    // is detected by negating into two's complement and testing for a power of
    // two. Sound because -(2^k) ≡ 2^w - 2^k (mod 2^w), so the product equals
    // -(x << k) in Z/2^w. This eliminates the full multiplier circuit that
    // would otherwise time out at 32/64-bit.
    let widths_and_negs: &[(u32, i64)] = &[
        (8, -8),  // 0xF8
        (8, -2),  // 0xFE  (smallest k=1)
        (8, -64), // 0xC0  (k=6)
        (32, -8), // 0xFFFFFFF8
        (64, -8), // 0xFF..F8
        (64, -1024),
    ];
    for &(width, neg) in widths_and_negs {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::bitvec(width));

        // Constant value of `neg` masked to width (two's complement).
        let modulus = BigInt::from(1u8) << width;
        let masked = (&modulus + BigInt::from(neg)) % &modulus;
        let const_neg = store.mk_bitvec(masked, width);

        // k = log2(-neg); build expected = bvneg(bvmul(x, 2^k)).
        let k = (-neg).trailing_zeros();
        let pow2 = store.mk_bitvec(BigInt::from(1u8) << k, width);
        let shifted = store.mk_bvmul(vec![x, pow2]);
        let expected = store.mk_bvneg(shifted);

        // x * -(2^k)
        let result = store.mk_bvmul(vec![x, const_neg]);
        assert_eq!(
            result, expected,
            "bvmul(x, {neg}) at {width}-bit should rewrite to bvneg(x << {k})"
        );

        // Commutative: -(2^k) * x
        let result_comm = store.mk_bvmul(vec![const_neg, x]);
        assert_eq!(
            result_comm, expected,
            "bvmul({neg}, x) at {width}-bit should rewrite to bvneg(x << {k}) (commutative)"
        );

        // The result must NOT be a residual bvmul (no full multiplier circuit).
        if let TermData::App(sym, _) = store.get(result) {
            assert_ne!(sym.name(), "bvmul", "bvmul(x, {neg}) must not stay a bvmul");
        }
        assert_eq!(store.sort(result), &Sort::bitvec(width));
    }
}

#[test]
fn test_bvmul_neg_power_of_two_value_preserving() {
    // Constant-fold cross-check: for concrete x, x * -(2^k) must equal the
    // value produced by the rewritten form, confirming equisatisfiability.
    let mut store = TermStore::new();
    let width = 8u32;
    // x = 5, c = -8 (0xF8). 5 * -8 = -40 mod 256 = 216 (0xD8).
    let x = store.mk_bitvec(BigInt::from(5), width);
    let c = store.mk_bitvec(BigInt::from(0xF8u32), width);
    let result = store.mk_bvmul(vec![x, c]);
    let expected = store.mk_bitvec(BigInt::from(0xD8u32), width);
    assert_eq!(result, expected, "5 * -8 mod 256 should be 0xD8 (216)");
}

#[test]
fn test_extract_low_of_mul_truncates_operands() {
    // The x86 Umul_I32 low-half identity: (zext64 a * zext64 b)[31:0] == a*b.
    // extract-low of a product rewrites to the product of the low slices, and
    // extract-over-zero_extend collapses each slice back to the 32-bit operand,
    // so the whole RHS reduces to the same `bvmul(a, b)` as the LHS.
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(32));
    let b = store.mk_var("b", Sort::bitvec(32));

    let za = store.mk_bvzero_extend(32, a); // 64-bit
    let zb = store.mk_bvzero_extend(32, b); // 64-bit
    let wide_mul = store.mk_bvmul(vec![za, zb]); // 64-bit product
    let low = store.mk_bvextract(31, 0, wide_mul);

    let expected = store.mk_bvmul(vec![a, b]); // 32-bit product
    assert_eq!(
        low, expected,
        "extract[31:0](zext a * zext b) should rewrite to a*b"
    );

    // Plain (non-extended) operands: extract-low of a wide product becomes the
    // product of the low slices (cheaper narrow multiply); still equivalent.
    let p = store.mk_var("p", Sort::bitvec(64));
    let q = store.mk_var("q", Sort::bitvec(64));
    let pq = store.mk_bvmul(vec![p, q]);
    let pq_low = store.mk_bvextract(31, 0, pq);
    let p_lo = store.mk_bvextract(31, 0, p);
    let q_lo = store.mk_bvextract(31, 0, q);
    let expected2 = store.mk_bvmul(vec![p_lo, q_lo]);
    assert_eq!(
        pq_low, expected2,
        "extract[31:0](p*q) should rewrite to (p[31:0])*(q[31:0])"
    );
}

#[test]
fn test_bvand_constant_folding() {
    let mut store = TermStore::new();

    // #xFF & #x0F = #x0F
    let a = store.mk_bitvec(BigInt::from(0xFF), 8);
    let b = store.mk_bitvec(BigInt::from(0x0F), 8);
    let expected = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bvand(vec![a, b]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvand_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);

    // x & 0 = 0
    let result = store.mk_bvand(vec![x, zero]);
    assert_eq!(result, zero);

    // x & #xFF = x (all-ones)
    let result2 = store.mk_bvand(vec![x, all_ones]);
    assert_eq!(result2, x);

    // x & x = x (idempotent)
    let result3 = store.mk_bvand(vec![x, x]);
    assert_eq!(result3, x);
}

#[test]
fn test_bvand_low_masked_sign_extend_canonicalizes_to_zero_extend() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(32));
    let signed = store.mk_bvsign_extend(32, x);
    let mask = store.mk_bitvec(BigInt::from(0xFFFF_FFFFu64), 64);
    let result = store.mk_bvand(vec![signed, mask]);
    let expected = store.mk_bvzero_extend(32, x);

    assert_eq!(result, expected);
}

#[test]
fn test_bvor_constant_folding() {
    let mut store = TermStore::new();

    // #xF0 | #x0F = #xFF
    let a = store.mk_bitvec(BigInt::from(0xF0), 8);
    let b = store.mk_bitvec(BigInt::from(0x0F), 8);
    let expected = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvor(vec![a, b]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvor_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);

    // x | 0 = x
    let result = store.mk_bvor(vec![x, zero]);
    assert_eq!(result, x);

    // x | #xFF = #xFF
    let result2 = store.mk_bvor(vec![x, all_ones]);
    assert_eq!(result2, all_ones);

    // x | x = x (idempotent)
    let result3 = store.mk_bvor(vec![x, x]);
    assert_eq!(result3, x);
}

#[test]
fn test_bvxor_constant_folding() {
    let mut store = TermStore::new();

    // #xF0 ^ #x0F = #xFF
    let a = store.mk_bitvec(BigInt::from(0xF0), 8);
    let b = store.mk_bitvec(BigInt::from(0x0F), 8);
    let expected = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvxor(vec![a, b]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvxor_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x ^ 0 = x
    let result = store.mk_bvxor(vec![x, zero]);
    assert_eq!(result, x);

    // x ^ x = 0
    let result2 = store.mk_bvxor(vec![x, x]);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvnot_constant_folding() {
    let mut store = TermStore::new();

    // ~#x00 = #xFF (for 8-bit)
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvnot(zero);
    assert_eq!(result, all_ones);

    // ~#xFF = #x00
    let result2 = store.mk_bvnot(all_ones);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvnot_double_negation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let not_x = store.mk_bvnot(x);
    let not_not_x = store.mk_bvnot(not_x);
    assert_eq!(not_not_x, x);
}

#[test]
fn test_bvneg_constant_folding() {
    let mut store = TermStore::new();

    // -#x01 = #xFF (for 8-bit, two's complement)
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvneg(one);
    assert_eq!(result, neg_one);

    // -#x00 = #x00
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvneg(zero);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvneg_double_negation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let neg_x = store.mk_bvneg(x);
    let neg_neg_x = store.mk_bvneg(neg_x);
    assert_eq!(neg_neg_x, x);
}

#[test]
fn test_bvshl_constant_folding() {
    let mut store = TermStore::new();

    // #x01 << 4 = #x10
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(0x10), 8);
    let result = store.mk_bvshl(vec![one, four]);
    assert_eq!(result, expected);

    // #x80 << 1 = #x00 (overflow)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let one_shift = store.mk_bitvec(BigInt::from(1), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let overflow_result = store.mk_bvshl(vec![x80, one_shift]);
    assert_eq!(overflow_result, zero);
}

#[test]
fn test_bvshl_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x << 0 = x
    let result = store.mk_bvshl(vec![x, zero]);
    assert_eq!(result, x);

    // 0 << x = 0
    let result2 = store.mk_bvshl(vec![zero, x]);
    assert_eq!(result2, zero);

    // x << 8 = 0 (shift >= width)
    let eight = store.mk_bitvec(BigInt::from(8), 8);
    let result3 = store.mk_bvshl(vec![x, eight]);
    assert_eq!(result3, zero);
}

// =========================================================================
// Constant-shift-to-extract rewrite tests (#8111)
// Reference: Z3 bv_rewriter, Yices2 term_manager.c:5298-5493
// =========================================================================

#[test]
fn test_bvshl_constant_shift_to_concat() {
    // bvshl(x, 3) for 8-bit should rewrite to concat(extract(x, 4, 0), bv_zero(3))
    // This eliminates the barrel-shifter circuit for constant shift amounts.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let three = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvshl(vec![x, three]);

    // Result should NOT be a bvshl application - it should be rewritten
    match store.get(result) {
        TermData::App(sym, _) => {
            assert_ne!(
                sym.name(),
                "bvshl",
                "bvshl(x, 3) should be rewritten to concat, not kept as bvshl"
            );
            // Should be a concat of extract and zero constant
            assert_eq!(
                sym.name(),
                "concat",
                "bvshl(x, K) should rewrite to concat(extract(x, n-K-1, 0), bv_zero(K))"
            );
        }
        _ => {
            // Could be a constant if both args are constant - that's fine too
        }
    }

    // Verify the sort is preserved
    assert_eq!(
        store.sort(result),
        &Sort::bitvec(8),
        "rewritten bvshl should preserve 8-bit width"
    );
}

#[test]
fn test_bvlshr_constant_shift_to_raw_concat() {
    // bvlshr(x, 2) for 8-bit rewrites to the raw
    // concat(#b00, extract(x, 7, 2)) surface used by checked Alethe export.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvlshr(vec![x, two]);

    let TermData::App(Symbol::Named(operator), operands) = store.get(result) else {
        panic!("symbolic constant lshr must normalize to concat")
    };
    assert_eq!(operator, "concat");
    let [high, extract] = operands.as_slice() else {
        panic!("concat must have exactly two operands")
    };
    assert!(matches!(
        store.get(*high),
        TermData::Const(Constant::BitVec { value, width })
            if *value == BigInt::from(0) && *width == 2
    ));
    assert!(matches!(
        store.get(*extract),
        TermData::App(Symbol::Indexed(name, indices), args)
            if name == "extract" && indices.as_slice() == [7, 2] && args.as_slice() == [x]
    ));

    assert_eq!(
        store.sort(result),
        &Sort::bitvec(8),
        "rewritten bvlshr should preserve 8-bit width"
    );
}

#[test]
fn test_bvlshr_raw_concat_rewrite_is_exhaustively_value_preserving() {
    // Exhaust every symbolic constant-shift rewrite through width 8. Replacing
    // x with a concrete value rebuilds concat/extract through the ordinary
    // canonical constructors, giving a direct constant-folding oracle for the
    // raw-concat representation used solely to retain the external proof
    // surface.
    for width in 2_u32..=8 {
        let modulus = 1_u64 << width;
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::bitvec(width));
        for shift in 1..width {
            let shift_term = store.mk_bitvec(BigInt::from(shift), width);
            let rewritten = store.mk_bvlshr(vec![x, shift_term]);
            assert!(matches!(
                store.get(rewritten),
                TermData::App(Symbol::Named(name), _) if name == "concat"
            ));
            for value in 0..modulus {
                let concrete = store.mk_bitvec(BigInt::from(value), width);
                let got = store.substitute(rewritten, &[x], &[concrete]);
                let expected = store.mk_bitvec(BigInt::from(value >> shift), width);
                assert_eq!(
                    got, expected,
                    "bad raw-concat lshr rewrite: width={width}, shift={shift}, value={value}"
                );
            }
        }
    }
}

#[test]
fn test_bvashr_constant_shift_to_sign_extend() {
    // bvashr(x, 2) for 8-bit should rewrite to sign_extend(2, extract(x, 7, 2))
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvashr(vec![x, two]);

    // Result should NOT be a bvashr application
    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(
            sym.name(),
            "bvashr",
            "bvashr(x, 2) should be rewritten, not kept as bvashr"
        );
    }

    assert_eq!(
        store.sort(result),
        &Sort::bitvec(8),
        "rewritten bvashr should preserve 8-bit width"
    );
}

#[test]
fn test_bvshl_constant_shift_by_1() {
    // Edge case: shift by 1
    // bvshl(x, 1) for 8-bit -> concat(extract(x, 6, 0), #b0)
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvshl(vec![x, one]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(sym.name(), "bvshl", "bvshl(x, 1) should be rewritten");
    }
    assert_eq!(store.sort(result), &Sort::bitvec(8));
}

#[test]
fn test_bvshl_constant_shift_width_minus_1() {
    // Edge case: shift by width-1
    // bvshl(x, 7) for 8-bit -> concat(extract(x, 0, 0), #b0000000)
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let result = store.mk_bvshl(vec![x, seven]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(sym.name(), "bvshl", "bvshl(x, 7) should be rewritten");
    }
    assert_eq!(store.sort(result), &Sort::bitvec(8));
}

#[test]
fn test_bvlshr_constant_shift_width_minus_1() {
    // Edge case: bvlshr(x, 7) for 8-bit -> concat(#b0000000, extract(x, 7, 7))
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let result = store.mk_bvlshr(vec![x, seven]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(sym.name(), "bvlshr", "bvlshr(x, 7) should be rewritten");
    }
    assert_eq!(store.sort(result), &Sort::bitvec(8));
}

// =========================================================================
// Mul-to-concat (mul2concat) rewrite tests (#8111)
// Reference: Z3 bv_rewriter.cpp:2483-2492
// =========================================================================

#[test]
fn test_bvmul_power_of_2_to_concat() {
    // bvmul(x, 4) for 8-bit should rewrite to concat(extract(x, 5, 0), #b00)
    // because 4 = 2^2, so this is equivalent to shifting left by 2.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let result = store.mk_bvmul(vec![x, four]);

    // Result should NOT be a bvmul application
    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(
            sym.name(),
            "bvmul",
            "bvmul(x, 4) should be rewritten to concat, not kept as bvmul"
        );
        assert_eq!(
            sym.name(),
            "concat",
            "bvmul(x, 2^k) should rewrite to concat(extract(x, n-k-1, 0), bv_zero(k))"
        );
    }

    assert_eq!(
        store.sort(result),
        &Sort::bitvec(8),
        "rewritten bvmul should preserve 8-bit width"
    );
}

#[test]
fn test_bvmul_power_of_2_commutative() {
    // bvmul(4, x) should also be rewritten (commutative)
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let result = store.mk_bvmul(vec![four, x]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(
            sym.name(),
            "bvmul",
            "bvmul(4, x) should be rewritten (commutative case)"
        );
    }

    assert_eq!(store.sort(result), &Sort::bitvec(8));
}

#[test]
fn test_bvmul_power_of_2_by_2() {
    // bvmul(x, 2) -> concat(extract(x, 6, 0), #b0) (shift left by 1)
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvmul(vec![x, two]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(
            sym.name(),
            "bvmul",
            "bvmul(x, 2) should be rewritten to concat"
        );
    }
    assert_eq!(store.sort(result), &Sort::bitvec(8));
}

#[test]
fn test_bvmul_power_of_2_by_128() {
    // bvmul(x, 128) for 8-bit -> concat(extract(x, 0, 0), #b0000000)
    // 128 = 2^7, shift left by 7
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let c128 = store.mk_bitvec(BigInt::from(128), 8);
    let result = store.mk_bvmul(vec![x, c128]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(
            sym.name(),
            "bvmul",
            "bvmul(x, 128) should be rewritten to concat"
        );
    }
    assert_eq!(store.sort(result), &Sort::bitvec(8));
}

fn contains_bvmul(store: &TermStore, root: TermId) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        match store.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "bvmul" {
                    return true;
                }
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(cond, then_term, else_term) => {
                pending.extend([*cond, *then_term, *else_term]);
            }
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                pending.push(*body);
                pending.extend(triggers.iter().flatten().copied());
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
        }
    }
    false
}

#[test]
fn test_bvmul_sparse_signed_constants_use_bounded_shift_add() {
    for width in [8u32, 64] {
        let modulus = BigInt::from(1u8) << width;
        for coefficient in [3i64, 5, 7, 11, 13, -3, -7] {
            let mut store = TermStore::new();
            let x = store.mk_var("x", Sort::bitvec(width));
            let masked = (&modulus + BigInt::from(coefficient)) % &modulus;
            let constant = store.mk_bitvec(masked, width);

            for args in [[x, constant], [constant, x]] {
                let result = store.mk_bvmul(args.to_vec());
                assert_eq!(store.sort(result), &Sort::bitvec(width));
                assert!(
                    !contains_bvmul(&store, result),
                    "{width}-bit multiply by {coefficient} must not retain a multiplier"
                );
            }
        }
    }
}

#[test]
fn test_bvmul_sparse_constant_rewrites_are_exhaustively_value_preserving() {
    // Exhaust every coefficient and input through width 6. Substitution rebuilds
    // the rewritten shift/add expression through canonical constructors, whose
    // constant folding gives a direct modular-semantics oracle.
    for width in 1u32..=6 {
        let modulus = 1u64 << width;
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::bitvec(width));
        for coefficient in 0..modulus {
            let constant = store.mk_bitvec(BigInt::from(coefficient), width);
            let product = store.mk_bvmul(vec![x, constant]);
            for input in 0..modulus {
                let input_term = store.mk_bitvec(BigInt::from(input), width);
                let got = store.substitute(product, &[x], &[input_term]);
                let expected = store.mk_bitvec(
                    BigInt::from(input.wrapping_mul(coefficient) % modulus),
                    width,
                );
                assert_eq!(
                    got, expected,
                    "bad {width}-bit rewrite for {input} * {coefficient}"
                );
            }
        }
    }
}

#[test]
fn test_bvmul_dense_constant_respects_rewrite_budget() {
    // Alternating bits have far more than four non-zero NAF digits. Retaining
    // bvmul is intentional: the rewrite must never trade one multiplier for an
    // unbounded addition tree.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(64));
    let dense = store.mk_bitvec(BigInt::from(0x5555_5555_5555_5555u64), 64);
    let result = store.mk_bvmul(vec![x, dense]);

    match store.get(result) {
        TermData::App(sym, _) => {
            assert_eq!(
                sym.name(),
                "bvmul",
                "dense constant must remain within the bounded rewrite budget"
            );
        }
        _ => panic!("expected residual bvmul for dense constant"),
    }
}

#[test]
fn test_bvmul_power_of_2_32bit() {
    // Test with wider bitvectors: bvmul(x, 256) for 32-bit
    // 256 = 2^8, so shift left by 8
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(32));
    let c256 = store.mk_bitvec(BigInt::from(256), 32);
    let result = store.mk_bvmul(vec![x, c256]);

    if let TermData::App(sym, _) = store.get(result) {
        assert_ne!(
            sym.name(),
            "bvmul",
            "bvmul(x, 256) on 32-bit should be rewritten to concat"
        );
    }
    assert_eq!(store.sort(result), &Sort::bitvec(32));
}

#[test]
fn test_bvshl_variable_shift_not_rewritten() {
    // bvshl(x, y) with variable shift should NOT be rewritten
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let result = store.mk_bvshl(vec![x, y]);

    match store.get(result) {
        TermData::App(sym, _) => {
            assert_eq!(
                sym.name(),
                "bvshl",
                "bvshl(x, y) with variable shift should be kept as bvshl"
            );
        }
        _ => panic!("Expected bvshl application for variable shift"),
    }
}

#[test]
fn test_bvlshr_constant_folding() {
    let mut store = TermStore::new();

    // #xFF >> 4 = #x0F
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bvlshr(vec![ff, four]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvlshr_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x >> 0 = x
    let result = store.mk_bvlshr(vec![x, zero]);
    assert_eq!(result, x);

    // 0 >> x = 0
    let result2 = store.mk_bvlshr(vec![zero, x]);
    assert_eq!(result2, zero);

    // x >> 8 = 0 (shift >= width)
    let eight = store.mk_bitvec(BigInt::from(8), 8);
    let result3 = store.mk_bvlshr(vec![x, eight]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvashr_constant_folding() {
    let mut store = TermStore::new();

    // #x80 >>> 4 = #xF8 (sign extension, negative)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(0xF8), 8);
    let result = store.mk_bvashr(vec![x80, four]);
    assert_eq!(result, expected);

    // #x70 >>> 4 = #x07 (no sign extension, positive)
    let x70 = store.mk_bitvec(BigInt::from(0x70), 8);
    let expected2 = store.mk_bitvec(BigInt::from(0x07), 8);
    let result2 = store.mk_bvashr(vec![x70, four]);
    assert_eq!(result2, expected2);
}

#[test]
fn test_bvashr_identity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x >>> 0 = x
    let result = store.mk_bvashr(vec![x, zero]);
    assert_eq!(result, x);

    // 0 >>> x = 0
    let result2 = store.mk_bvashr(vec![zero, x]);
    assert_eq!(result2, zero);
}

#[test]
fn test_bvudiv_constant_folding() {
    let mut store = TermStore::new();

    // #x10 / #x04 = #x04
    let x10 = store.mk_bitvec(BigInt::from(0x10), 8);
    let four = store.mk_bitvec(BigInt::from(4), 8);
    let expected = store.mk_bitvec(BigInt::from(4), 8);
    let result = store.mk_bvudiv(vec![x10, four]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvudiv_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x / 1 = x (valid: 1 is provably non-zero)
    let result = store.mk_bvudiv(vec![x, one]);
    assert_eq!(result, x);

    // bvudiv(0, x) must NOT simplify to 0: bvudiv(0, 0) = all_ones per SMT-LIB
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvudiv(vec![zero, x]);
    assert_ne!(
        result2, zero,
        "bvudiv(0, x) must not fold to 0 (x could be 0)"
    );

    // bvudiv(x, x) must NOT simplify to 1: bvudiv(0, 0) = all_ones per SMT-LIB
    let result3 = store.mk_bvudiv(vec![x, x]);
    assert_ne!(
        result3, one,
        "bvudiv(x, x) must not fold to 1 (x could be 0)"
    );
}

#[test]
fn test_bvudiv_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    // bvudiv(7, 0) = all_ones = 255 per SMT-LIB
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(255), 8);
    let result = store.mk_bvudiv(vec![seven, zero]);
    assert_eq!(result, all_ones);

    // bvudiv(0, 0) = all_ones = 255 per SMT-LIB
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvudiv(vec![zero2, zero]);
    assert_eq!(result2, all_ones);
}

#[test]
fn test_bvurem_constant_folding() {
    let mut store = TermStore::new();

    // #x17 % #x05 = #x03 (23 % 5 = 3)
    let x17 = store.mk_bitvec(BigInt::from(0x17), 8);
    let five = store.mk_bitvec(BigInt::from(5), 8);
    let expected = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvurem(vec![x17, five]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvurem_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x % 1 = 0
    let result = store.mk_bvurem(vec![x, one]);
    assert_eq!(result, zero);

    // x % 0 = x
    let result0 = store.mk_bvurem(vec![x, zero]);
    assert_eq!(result0, x);

    // 0 % x = 0
    let result2 = store.mk_bvurem(vec![zero, x]);
    assert_eq!(result2, zero);

    // x % x = 0
    let result3 = store.mk_bvurem(vec![x, x]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvurem_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    // bvurem(7, 0) = 7 per SMT-LIB
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result = store.mk_bvurem(vec![seven, zero]);
    assert_eq!(result, seven);

    // bvurem(0, 0) = 0 per SMT-LIB
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvurem(vec![zero2, zero]);
    assert_eq!(result2, zero);

    // bvurem(255, 0) = 255 per SMT-LIB
    let ff = store.mk_bitvec(BigInt::from(255), 8);
    let result3 = store.mk_bvurem(vec![ff, zero]);
    assert_eq!(result3, ff);
}
