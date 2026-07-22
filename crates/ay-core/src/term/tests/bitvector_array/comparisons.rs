// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =========================================================================
// Bitvector comparison tests
// =========================================================================

#[test]
fn test_bvult_constant_folding() {
    let mut store = TermStore::new();

    // 1 < 2 = true (unsigned)
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvult(one, two);
    assert_eq!(result, store.true_term());

    // 2 < 1 = false (unsigned)
    let result2 = store.mk_bvult(two, one);
    assert_eq!(result2, store.false_term());

    // 0xFF < 0x01 = false (unsigned: 255 < 1 is false)
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result3 = store.mk_bvult(ff, one);
    assert_eq!(result3, store.false_term());
}

#[test]
fn test_bvult_reflexivity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x < x = false
    let result = store.mk_bvult(x, x);
    assert_eq!(result, store.false_term());

    // x < 0 = false (nothing is less than 0 unsigned)
    let result2 = store.mk_bvult(x, zero);
    assert_eq!(result2, store.false_term());
}

#[test]
fn test_bvule_constant_folding() {
    let mut store = TermStore::new();

    // 1 <= 2 = true
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvule(one, two);
    assert_eq!(result, store.true_term());

    // 2 <= 2 = true
    let result2 = store.mk_bvule(two, two);
    assert_eq!(result2, store.true_term());

    // 2 <= 1 = false
    let result3 = store.mk_bvule(two, one);
    assert_eq!(result3, store.false_term());
}

#[test]
fn test_bvule_reflexivity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x <= x = true
    let result = store.mk_bvule(x, x);
    assert_eq!(result, store.true_term());

    // 0 <= x = true (0 is <= everything unsigned)
    let result2 = store.mk_bvule(zero, x);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_bvugt_normalization() {
    let mut store = TermStore::new();

    // bvugt(a, b) should normalize to bvult(b, a)
    let a = store.mk_bitvec(BigInt::from(5), 8);
    let b = store.mk_bitvec(BigInt::from(3), 8);

    // 5 > 3 = true
    let result = store.mk_bvugt(a, b);
    assert_eq!(result, store.true_term());

    // 3 > 5 = false
    let result2 = store.mk_bvugt(b, a);
    assert_eq!(result2, store.false_term());
}

#[test]
fn test_bvuge_normalization() {
    let mut store = TermStore::new();

    // bvuge(a, b) should normalize to bvule(b, a)
    let a = store.mk_bitvec(BigInt::from(5), 8);
    let b = store.mk_bitvec(BigInt::from(3), 8);

    // 5 >= 3 = true
    let result = store.mk_bvuge(a, b);
    assert_eq!(result, store.true_term());

    // 5 >= 5 = true
    let result2 = store.mk_bvuge(a, a);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_bvslt_constant_folding() {
    let mut store = TermStore::new();

    // Signed comparison: -1 < 1 is true
    // In 8-bit two's complement, 0xFF = -1
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvslt(neg_one, one);
    assert_eq!(result, store.true_term());

    // Signed: 1 < -1 is false
    let result2 = store.mk_bvslt(one, neg_one);
    assert_eq!(result2, store.false_term());

    // Signed: -128 (0x80) < 127 (0x7F) is true
    let min_val = store.mk_bitvec(BigInt::from(0x80), 8);
    let max_val = store.mk_bitvec(BigInt::from(0x7F), 8);
    let result3 = store.mk_bvslt(min_val, max_val);
    assert_eq!(result3, store.true_term());

    // Signed: 127 < -128 is false
    let result4 = store.mk_bvslt(max_val, min_val);
    assert_eq!(result4, store.false_term());
}

#[test]
fn test_bvslt_reflexivity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));

    // x < x = false
    let result = store.mk_bvslt(x, x);
    assert_eq!(result, store.false_term());
}

#[test]
fn test_bvsle_constant_folding() {
    let mut store = TermStore::new();

    // Signed: -1 <= 1 is true
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsle(neg_one, one);
    assert_eq!(result, store.true_term());

    // Signed: -1 <= -1 is true
    let result2 = store.mk_bvsle(neg_one, neg_one);
    assert_eq!(result2, store.true_term());

    // Signed: 1 <= -1 is false
    let result3 = store.mk_bvsle(one, neg_one);
    assert_eq!(result3, store.false_term());
}

#[test]
fn test_bvsle_reflexivity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));

    // x <= x = true
    let result = store.mk_bvsle(x, x);
    assert_eq!(result, store.true_term());
}

#[test]
fn test_bvsgt_normalization() {
    let mut store = TermStore::new();

    // bvsgt(a, b) normalizes to bvslt(b, a)
    // Signed: 1 > -1 is true
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsgt(one, neg_one);
    assert_eq!(result, store.true_term());

    // Signed: -1 > 1 is false
    let result2 = store.mk_bvsgt(neg_one, one);
    assert_eq!(result2, store.false_term());
}

#[test]
fn test_bvsge_normalization() {
    let mut store = TermStore::new();

    // bvsge(a, b) normalizes to bvsle(b, a)
    // Signed: 1 >= -1 is true
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsge(one, neg_one);
    assert_eq!(result, store.true_term());

    // Signed: 1 >= 1 is true
    let result2 = store.mk_bvsge(one, one);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_signed_vs_unsigned_comparison() {
    let mut store = TermStore::new();

    // 0xFF: unsigned = 255, signed = -1
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // Unsigned: 255 < 1 is false
    let ult_result = store.mk_bvult(ff, one);
    assert_eq!(ult_result, store.false_term());

    // Signed: -1 < 1 is true
    let slt_result = store.mk_bvslt(ff, one);
    assert_eq!(slt_result, store.true_term());
}
