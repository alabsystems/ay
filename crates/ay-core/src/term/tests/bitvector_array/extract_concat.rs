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

mod integer_conversions;

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
