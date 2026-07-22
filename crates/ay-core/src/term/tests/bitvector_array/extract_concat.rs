// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =========================================================================
// Bitvector extract, concat, extend, and rotate tests
// =========================================================================

#[test]
fn test_bvextract_constant_folding() {
    let mut store = TermStore::new();

    // extract(7,4,#xFF) -> #x0F (extracts bits 7..4 = 0b1111)
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result = store.mk_bvextract(7, 4, ff);
    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0x0F));
        assert_eq!(width, 4);
    } else {
        panic!("Expected bitvector constant");
    }

    // extract(3,0,#xAB) -> #x0B (extracts lower nibble)
    let ab = store.mk_bitvec(BigInt::from(0xAB), 8);
    let result2 = store.mk_bvextract(3, 0, ab);
    if let Some((val, width)) = store.get_bitvec(result2) {
        assert_eq!(*val, BigInt::from(0x0B));
        assert_eq!(width, 4);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvextract_full_extract() {
    let mut store = TermStore::new();

    // extract(7,0,x) -> x (full extract is identity)
    let x = store.mk_var("x", Sort::bitvec(8));
    let result = store.mk_bvextract(7, 0, x);
    assert_eq!(result, x);
}

#[test]
fn test_bvextract_over_zero_extend_low_slice() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let extended = store.mk_bvzero_extend(8, x);
    let result = store.mk_bvextract(3, 0, extended);
    let expected = store.mk_bvextract(3, 0, x);

    assert_eq!(result, expected);
}

#[test]
fn test_bvextract_over_zero_extend_high_slice_is_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let extended = store.mk_bvzero_extend(8, x);
    let result = store.mk_bvextract(11, 8, extended);

    assert_eq!(store.get_bitvec(result), Some((&BigInt::from(0), 4)));
}

#[test]
fn test_bvextract_over_zero_extend_crossing_slice() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let extended = store.mk_bvzero_extend(8, x);
    let result = store.mk_bvextract(9, 6, extended);
    let zeros = store.mk_bitvec(BigInt::from(0), 2);
    let low = store.mk_bvextract(7, 6, x);
    let expected = store.mk_bvconcat(vec![zeros, low]);

    assert_eq!(result, expected);
}

#[test]
fn test_bvextract_over_nested_extract() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(16));
    let inner = store.mk_bvextract(11, 4, x);
    let result = store.mk_bvextract(3, 1, inner);
    let expected = store.mk_bvextract(7, 5, x);

    assert_eq!(result, expected);
}

#[test]
fn test_bvconcat_constant_folding() {
    let mut store = TermStore::new();

    // concat(#x0F, #xF0) -> #x0FF0
    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);
    let xf0 = store.mk_bitvec(BigInt::from(0xF0), 8);
    let result = store.mk_bvconcat(vec![x0f, xf0]);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0x0FF0));
        assert_eq!(width, 16);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvconcat_mixed_widths() {
    let mut store = TermStore::new();

    // concat(4-bit, 8-bit) should give 12-bit result
    let nibble = store.mk_bitvec(BigInt::from(0xA), 4);
    let byte = store.mk_bitvec(BigInt::from(0xBC), 8);
    let result = store.mk_bvconcat(vec![nibble, byte]);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0xABC));
        assert_eq!(width, 12);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvconcat_zero_high_canonicalizes_to_zero_extend() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 4);
    let result = store.mk_bvconcat(vec![zero, x]);
    let expected = store.mk_bvzero_extend(4, x);

    assert_eq!(result, expected);
}

#[test]
fn test_bvconcat_adjacent_extracts_canonicalize_to_slice() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(16));
    let high = store.mk_bvextract(11, 8, x);
    let low = store.mk_bvextract(7, 4, x);
    let result = store.mk_bvconcat(vec![high, low]);
    let expected = store.mk_bvextract(11, 4, x);

    assert_eq!(result, expected);
}

#[test]
fn test_bvconcat_extract_chain_canonicalizes_to_slice() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let b7 = store.mk_bvextract(7, 7, x);
    let b6 = store.mk_bvextract(6, 6, x);
    let b5 = store.mk_bvextract(5, 5, x);
    let b4 = store.mk_bvextract(4, 4, x);
    let high = store.mk_bvconcat(vec![b7, b6]);
    let low = store.mk_bvconcat(vec![b5, b4]);
    let result = store.mk_bvconcat(vec![high, low]);
    let expected = store.mk_bvextract(7, 4, x);

    assert_eq!(result, expected);
}

#[test]
fn test_bvzero_extend_constant_folding() {
    let mut store = TermStore::new();

    // zero_extend(4, #x0F) -> #x00F (12-bit)
    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bvzero_extend(4, x0f);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0x0F));
        assert_eq!(width, 12);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvzero_extend_identity() {
    let mut store = TermStore::new();

    // zero_extend(0, x) -> x
    let x = store.mk_var("x", Sort::bitvec(8));
    let result = store.mk_bvzero_extend(0, x);
    assert_eq!(result, x);
}

#[test]
fn test_bvzero_extend_nested_flattens() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let inner = store.mk_bvzero_extend(4, x);
    let result = store.mk_bvzero_extend(12, inner);
    let expected = store.mk_bvzero_extend(16, x);

    assert_eq!(result, expected);
    assert_eq!(store.sort(result), &Sort::bitvec(24));
}

#[test]
fn test_bvsign_extend_positive() {
    let mut store = TermStore::new();

    // sign_extend(4, #x7F) -> #x07F (12-bit, positive so zero extended)
    let x7f = store.mk_bitvec(BigInt::from(0x7F), 8);
    let result = store.mk_bvsign_extend(4, x7f);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0x07F));
        assert_eq!(width, 12);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvsign_extend_negative() {
    let mut store = TermStore::new();

    // sign_extend(4, #x8F) -> #xF8F (12-bit, negative so ones extended)
    let x8f = store.mk_bitvec(BigInt::from(0x8F), 8);
    let result = store.mk_bvsign_extend(4, x8f);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0xF8F));
        assert_eq!(width, 12);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvsign_extend_identity() {
    let mut store = TermStore::new();

    // sign_extend(0, x) -> x
    let x = store.mk_var("x", Sort::bitvec(8));
    let result = store.mk_bvsign_extend(0, x);
    assert_eq!(result, x);
}

#[test]
fn test_bvrotate_left_constant_folding() {
    let mut store = TermStore::new();

    // rotate_left(2, #xA5) -> #x96
    // #xA5 = 0b10100101, rotate left 2 = 0b10010110 = #x96
    let xa5 = store.mk_bitvec(BigInt::from(0xA5), 8);
    let result = store.mk_bvrotate_left(2, xa5);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0x96));
        assert_eq!(width, 8);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvrotate_left_identity() {
    let mut store = TermStore::new();

    // rotate_left(0, x) -> x
    let x = store.mk_var("x", Sort::bitvec(8));
    let result = store.mk_bvrotate_left(0, x);
    assert_eq!(result, x);

    // rotate_left(8, x) -> x (full rotation)
    let result2 = store.mk_bvrotate_left(8, x);
    assert_eq!(result2, x);
}

#[test]
fn test_bvrotate_right_constant_folding() {
    let mut store = TermStore::new();

    // rotate_right(2, #xA5) -> #x69
    // #xA5 = 0b10100101, rotate right 2 = 0b01101001 = #x69
    let xa5 = store.mk_bitvec(BigInt::from(0xA5), 8);
    let result = store.mk_bvrotate_right(2, xa5);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0x69));
        assert_eq!(width, 8);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvrotate_right_identity() {
    let mut store = TermStore::new();

    // rotate_right(0, x) -> x
    let x = store.mk_var("x", Sort::bitvec(8));
    let result = store.mk_bvrotate_right(0, x);
    assert_eq!(result, x);

    // rotate_right(8, x) -> x (full rotation)
    let result2 = store.mk_bvrotate_right(8, x);
    assert_eq!(result2, x);
}

#[test]
fn test_bvrotate_inverse() {
    let mut store = TermStore::new();

    // rotate_left(n, rotate_right(n, x)) should give back original
    let xa5 = store.mk_bitvec(BigInt::from(0xA5), 8);
    let rotated_right = store.mk_bvrotate_right(3, xa5);
    let rotated_back = store.mk_bvrotate_left(3, rotated_right);
    assert_eq!(rotated_back, xa5);
}

#[test]
fn test_bvrepeat_constant_folding() {
    let mut store = TermStore::new();

    // repeat(3, #xAB) -> #xABABAB
    let xab = store.mk_bitvec(BigInt::from(0xAB), 8);
    let result = store.mk_bvrepeat(3, xab);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0xABABAB));
        assert_eq!(width, 24);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bvrepeat_identity() {
    let mut store = TermStore::new();

    // repeat(1, x) -> x
    let x = store.mk_var("x", Sort::bitvec(8));
    let result = store.mk_bvrepeat(1, x);
    assert_eq!(result, x);
}

#[test]
fn test_bvrepeat_small() {
    let mut store = TermStore::new();

    // repeat(4, #b11) -> #b11111111 = #xFF
    let x3 = store.mk_bitvec(BigInt::from(0b11), 2);
    let result = store.mk_bvrepeat(4, x3);

    if let Some((val, width)) = store.get_bitvec(result) {
        assert_eq!(*val, BigInt::from(0xFF));
        assert_eq!(width, 8);
    } else {
        panic!("Expected bitvector constant");
    }
}

#[test]
fn test_bv2nat_constant_folding() {
    let mut store = TermStore::new();

    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bv2nat(x0f);

    assert_eq!(store.get_int(result).cloned(), Some(BigInt::from(15)));
}

#[test]
fn test_bv2int_signed_constant_folding() {
    let mut store = TermStore::new();

    // Unsigned cases (is_signed = false) should match bv2nat
    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);
    let unsigned = store.mk_bv2int(x0f, false);
    assert_eq!(store.get_int(unsigned).cloned(), Some(BigInt::from(15)));

    // Signed positive: 0x7F (127) is positive, so bv2int_signed = 127
    let x7f = store.mk_bitvec(BigInt::from(0x7F), 8);
    let signed_pos = store.mk_bv2int(x7f, true);
    assert_eq!(store.get_int(signed_pos).cloned(), Some(BigInt::from(127)));

    // Signed negative: 0xFF is -1 in two's complement (8-bit)
    let xff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let signed_neg = store.mk_bv2int(xff, true);
    assert_eq!(store.get_int(signed_neg).cloned(), Some(BigInt::from(-1)));

    // Signed negative: 0x80 is -128 in two's complement (8-bit)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let signed_min = store.mk_bv2int(x80, true);
    assert_eq!(store.get_int(signed_min).cloned(), Some(BigInt::from(-128)));

    // Width=1 bitvectors: signed range is [-1, 0]
    // 0b0 (value 0) -> 0
    // 0b1 (value 1) -> -1
    let bit0 = store.mk_bitvec(BigInt::from(0), 1);
    let signed_0 = store.mk_bv2int(bit0, true);
    assert_eq!(store.get_int(signed_0).cloned(), Some(BigInt::from(0)));

    let bit1 = store.mk_bitvec(BigInt::from(1), 1);
    let signed_1 = store.mk_bv2int(bit1, true);
    assert_eq!(store.get_int(signed_1).cloned(), Some(BigInt::from(-1)));
}

#[test]
fn test_bv2int_symbolic() {
    let mut store = TermStore::new();

    // For symbolic bitvectors, mk_bv2int should produce an ITE expression
    let x = store.mk_var("x", Sort::bitvec(8));

    // Unsigned case: should produce bv2nat(x)
    let unsigned = store.mk_bv2int(x, false);
    assert_eq!(store.sort(unsigned), &Sort::Int);
    // Check it's a bv2nat application
    if let TermData::App(Symbol::Named(name), args) = store.get(unsigned) {
        assert_eq!(name, "bv2nat");
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], x);
    } else {
        panic!("Expected bv2nat application");
    }

    // Signed case: should produce ite(bvslt x 0, bv2nat(x) - 256, bv2nat(x))
    let signed = store.mk_bv2int(x, true);
    assert_eq!(store.sort(signed), &Sort::Int);
    // Check it's an ITE
    if let TermData::Ite(cond, then_branch, else_branch) = store.get(signed) {
        // Condition should be bvslt
        if let TermData::App(Symbol::Named(name), _) = store.get(*cond) {
            assert_eq!(name, "bvslt");
        } else {
            panic!("Expected bvslt condition");
        }
        // Both branches should have Int sort
        assert_eq!(store.sort(*then_branch), &Sort::Int);
        assert_eq!(store.sort(*else_branch), &Sort::Int);
    } else {
        panic!("Expected ITE for signed symbolic conversion");
    }
}

#[test]
fn test_int2bv_constant_folding_and_wraparound() {
    let mut store = TermStore::new();

    let fifteen = store.mk_int(BigInt::from(15));
    let result = store.mk_int2bv(8, fifteen);
    assert_eq!(result, store.mk_bitvec(BigInt::from(0x0F), 8));

    // -1 mod 2^8 = 255
    let minus_one = store.mk_int(BigInt::from(-1));
    let result2 = store.mk_int2bv(8, minus_one);
    assert_eq!(result2, store.mk_bitvec(BigInt::from(0xFF), 8));

    // 256 mod 2^8 = 0
    let two_fifty_six = store.mk_int(BigInt::from(256));
    let result3 = store.mk_int2bv(8, two_fifty_six);
    assert_eq!(result3, store.mk_bitvec(BigInt::from(0), 8));
}

#[test]
fn test_int2bv_bv2nat_roundtrip_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let nat = store.mk_bv2nat(x);
    let back = store.mk_int2bv(8, nat);
    assert_eq!(back, x);
}

#[test]
fn test_int2bv_bv2int_signed_roundtrip() {
    // Test that int2bv(bv2int(x, signed)) = x for constant bitvectors
    let mut store = TermStore::new();

    // Positive value: 0x7F (127 signed)
    let x7f = store.mk_bitvec(BigInt::from(0x7F), 8);
    let signed = store.mk_bv2int(x7f, true);
    assert_eq!(store.get_int(signed).cloned(), Some(BigInt::from(127)));
    let back = store.mk_int2bv(8, signed);
    assert_eq!(back, x7f);

    // Negative value: 0xFF (-1 signed)
    let xff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let signed_neg = store.mk_bv2int(xff, true);
    assert_eq!(store.get_int(signed_neg).cloned(), Some(BigInt::from(-1)));
    let back_neg = store.mk_int2bv(8, signed_neg);
    assert_eq!(back_neg, xff);

    // Min value: 0x80 (-128 signed)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let signed_min = store.mk_bv2int(x80, true);
    assert_eq!(store.get_int(signed_min).cloned(), Some(BigInt::from(-128)));
    let back_min = store.mk_int2bv(8, signed_min);
    assert_eq!(back_min, x80);
}

#[test]
fn test_bv2int_32bit_width() {
    // Test 32-bit width to verify BigInt arithmetic works for common sizes
    let mut store = TermStore::new();

    // Max positive 32-bit signed: 0x7FFFFFFF = 2147483647
    let max_pos = store.mk_bitvec(BigInt::from(0x7FFFFFFFu32), 32);
    let signed_max = store.mk_bv2int(max_pos, true);
    assert_eq!(
        store.get_int(signed_max).cloned(),
        Some(BigInt::from(2147483647i64))
    );

    // -1 in 32-bit: 0xFFFFFFFF
    let minus_one = store.mk_bitvec(BigInt::from(0xFFFFFFFFu32), 32);
    let signed_neg1 = store.mk_bv2int(minus_one, true);
    assert_eq!(
        store.get_int(signed_neg1).cloned(),
        Some(BigInt::from(-1i64))
    );

    // Min 32-bit signed: 0x80000000 = -2147483648
    let min_neg = store.mk_bitvec(BigInt::from(0x80000000u32), 32);
    let signed_min = store.mk_bv2int(min_neg, true);
    assert_eq!(
        store.get_int(signed_min).cloned(),
        Some(BigInt::from(-2147483648i64))
    );

    // Verify roundtrip works
    let back = store.mk_int2bv(32, signed_min);
    assert_eq!(back, min_neg);
}

#[test]
fn test_bvnand_bvnor_bvxnor_constant_folding() {
    let mut store = TermStore::new();

    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(0xFF), 8);
    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);

    // nand(FF, FF) = 00
    assert_eq!(store.mk_bvnand(vec![all_ones, all_ones]), zero);

    // nor(00, 00) = FF
    assert_eq!(store.mk_bvnor(vec![zero, zero]), all_ones);

    // xnor(0F, 0F) = FF
    assert_eq!(store.mk_bvxnor(vec![x0f, x0f]), all_ones);
}
