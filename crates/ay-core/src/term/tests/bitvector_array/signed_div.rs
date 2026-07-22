// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =========================================================================
// Signed bitvector division/remainder/modulo tests
// =========================================================================

#[test]
fn test_bvsdiv_constant_folding_positive() {
    let mut store = TermStore::new();

    // 7 / 2 = 3 (both positive)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let expected = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvsdiv(vec![seven, two]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsdiv_constant_folding_negative_dividend() {
    let mut store = TermStore::new();

    // -7 / 2 = -3 (8-bit: 0xF9 / 2 = 0xFD which is -3)
    // -7 in 8-bit two's complement is 256 - 7 = 249 = 0xF9
    let neg_seven = store.mk_bitvec(BigInt::from(249), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    // -3 in 8-bit two's complement is 256 - 3 = 253 = 0xFD
    let expected = store.mk_bitvec(BigInt::from(253), 8);
    let result = store.mk_bvsdiv(vec![neg_seven, two]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsdiv_constant_folding_negative_divisor() {
    let mut store = TermStore::new();

    // 7 / -2 = -3 (truncated towards zero)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    // -2 in 8-bit is 254
    let neg_two = store.mk_bitvec(BigInt::from(254), 8);
    // -3 in 8-bit is 253
    let expected = store.mk_bitvec(BigInt::from(253), 8);
    let result = store.mk_bvsdiv(vec![seven, neg_two]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsdiv_constant_folding_both_negative() {
    let mut store = TermStore::new();

    // -7 / -2 = 3 (both negative, result positive)
    let neg_seven = store.mk_bitvec(BigInt::from(249), 8);
    let neg_two = store.mk_bitvec(BigInt::from(254), 8);
    let expected = store.mk_bitvec(BigInt::from(3), 8);
    let result = store.mk_bvsdiv(vec![neg_seven, neg_two]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsdiv_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x / 1 = x (valid: 1 is provably non-zero)
    let result = store.mk_bvsdiv(vec![x, one]);
    assert_eq!(result, x);

    // bvsdiv(0, x) must NOT simplify to 0: bvsdiv(0, 0) = all_ones per SMT-LIB
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvsdiv(vec![zero, x]);
    assert_ne!(
        result2, zero,
        "bvsdiv(0, x) must not fold to 0 (x could be 0)"
    );

    // bvsdiv(x, x) must NOT simplify to 1: bvsdiv(0, 0) = all_ones per SMT-LIB
    let result3 = store.mk_bvsdiv(vec![x, x]);
    assert_ne!(
        result3, one,
        "bvsdiv(x, x) must not fold to 1 (x could be 0)"
    );
}

#[test]
fn test_bvsdiv_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    // bvsdiv(7, 0) = all_ones = 255 (positive dividend -> ~0)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let all_ones = store.mk_bitvec(BigInt::from(255), 8);
    let result = store.mk_bvsdiv(vec![seven, zero]);
    assert_eq!(result, all_ones);

    // bvsdiv(0, 0) = all_ones = 255 (msb(0)=0, so ~0)
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result2 = store.mk_bvsdiv(vec![zero2, zero]);
    assert_eq!(result2, all_ones);

    // bvsdiv(-1, 0) = 1 (negative dividend -> 1)
    let neg_one = store.mk_bitvec(BigInt::from(255), 8); // -1 in 8-bit
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result3 = store.mk_bvsdiv(vec![neg_one, zero]);
    assert_eq!(result3, one);

    // bvsdiv(-128, 0) = 1 (negative dividend -> 1)
    let neg_128 = store.mk_bitvec(BigInt::from(128), 8); // -128 in 8-bit
    let result4 = store.mk_bvsdiv(vec![neg_128, zero]);
    assert_eq!(result4, one);
}

#[test]
fn test_bvsdiv_div_by_zero_symbolic_dividend_not_constant_folded() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // For symbolic dividends, keep term symbolic instead of folding to one constant.
    let result = store.mk_bvsdiv(vec![x, zero]);
    if let TermData::App(Symbol::Named(name), args) = store.get(result) {
        assert_eq!(name, "bvsdiv");
        assert_eq!(args, &[x, zero]);
    } else {
        panic!("Expected App term for symbolic bvsdiv(x, 0)");
    }
}

#[test]
fn test_bvsrem_constant_folding_positive() {
    let mut store = TermStore::new();

    // 7 % 3 = 1 (both positive)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let three = store.mk_bitvec(BigInt::from(3), 8);
    let expected = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsrem(vec![seven, three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsrem_constant_folding_negative_dividend() {
    let mut store = TermStore::new();

    // -7 % 3 = -1 (sign follows dividend)
    let neg_seven = store.mk_bitvec(BigInt::from(249), 8); // -7
    let three = store.mk_bitvec(BigInt::from(3), 8);
    let expected = store.mk_bitvec(BigInt::from(255), 8); // -1
    let result = store.mk_bvsrem(vec![neg_seven, three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsrem_constant_folding_negative_divisor() {
    let mut store = TermStore::new();

    // 7 % -3 = 1 (sign follows dividend, dividend is positive)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let neg_three = store.mk_bitvec(BigInt::from(253), 8); // -3
    let expected = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsrem(vec![seven, neg_three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsrem_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x % 1 = 0
    let result = store.mk_bvsrem(vec![x, one]);
    assert_eq!(result, zero);

    // 0 % x = 0
    let result2 = store.mk_bvsrem(vec![zero, x]);
    assert_eq!(result2, zero);

    // x % x = 0
    let result3 = store.mk_bvsrem(vec![x, x]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvsrem_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // bvsrem(7, 0) = 7 per SMT-LIB (positive dividend)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let result = store.mk_bvsrem(vec![seven, zero]);
    assert_eq!(result, seven);

    // bvsrem(-1, 0) = -1 = #xFF per SMT-LIB (negative dividend)
    let neg_one = store.mk_bitvec(BigInt::from(255), 8); // -1 in 8-bit
    let result2 = store.mk_bvsrem(vec![neg_one, zero]);
    assert_eq!(result2, neg_one, "bvsrem(-1, 0) should return -1 = #xFF");

    // bvsrem(0, 0) = 0 per SMT-LIB
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result3 = store.mk_bvsrem(vec![zero2, zero]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvsmod_constant_folding_positive() {
    let mut store = TermStore::new();

    // 7 mod 3 = 1 (both positive)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let three = store.mk_bitvec(BigInt::from(3), 8);
    let expected = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsmod(vec![seven, three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsmod_constant_folding_negative_dividend() {
    let mut store = TermStore::new();

    // -7 mod 3 = 2 (sign follows divisor which is positive)
    // -7 = -3*3 + 2, so result is 2
    let neg_seven = store.mk_bitvec(BigInt::from(249), 8); // -7
    let three = store.mk_bitvec(BigInt::from(3), 8);
    let expected = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvsmod(vec![neg_seven, three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsmod_constant_folding_negative_divisor() {
    let mut store = TermStore::new();

    // 7 mod -3 = -2 (sign follows divisor which is negative)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let neg_three = store.mk_bitvec(BigInt::from(253), 8); // -3
    let expected = store.mk_bitvec(BigInt::from(254), 8); // -2
    let result = store.mk_bvsmod(vec![seven, neg_three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsmod_constant_folding_both_negative() {
    let mut store = TermStore::new();

    // -7 mod -3 = -1 (sign follows divisor which is negative)
    let neg_seven = store.mk_bitvec(BigInt::from(249), 8); // -7
    let neg_three = store.mk_bitvec(BigInt::from(253), 8); // -3
    let expected = store.mk_bitvec(BigInt::from(255), 8); // -1
    let result = store.mk_bvsmod(vec![neg_seven, neg_three]);
    assert_eq!(result, expected);
}

#[test]
fn test_bvsmod_simplifications() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // x mod 1 = 0
    let result = store.mk_bvsmod(vec![x, one]);
    assert_eq!(result, zero);

    // 0 mod x = 0
    let result2 = store.mk_bvsmod(vec![zero, x]);
    assert_eq!(result2, zero);

    // x mod x = 0
    let result3 = store.mk_bvsmod(vec![x, x]);
    assert_eq!(result3, zero);
}

#[test]
fn test_bvsmod_div_by_zero_constant_fold() {
    let mut store = TermStore::new();

    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // bvsmod(7, 0) = 7 per SMT-LIB (positive dividend)
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let result = store.mk_bvsmod(vec![seven, zero]);
    assert_eq!(result, seven);

    // bvsmod(-1, 0) = -1 = #xFF per SMT-LIB (negative dividend)
    let neg_one = store.mk_bitvec(BigInt::from(255), 8); // -1 in 8-bit
    let result2 = store.mk_bvsmod(vec![neg_one, zero]);
    assert_eq!(result2, neg_one, "bvsmod(-1, 0) should return -1 = #xFF");

    // bvsmod(-128, 0) = -128 = #x80 per SMT-LIB (min negative)
    let neg_128 = store.mk_bitvec(BigInt::from(128), 8); // -128 in 8-bit
    let result3 = store.mk_bvsmod(vec![neg_128, zero]);
    assert_eq!(
        result3, neg_128,
        "bvsmod(-128, 0) should return -128 = #x80"
    );

    // bvsmod(0, 0) = 0 per SMT-LIB
    let zero2 = store.mk_bitvec(BigInt::from(0), 8);
    let result4 = store.mk_bvsmod(vec![zero2, zero]);
    assert_eq!(result4, zero);
}

#[test]
fn test_bvcomp_constant_folding() {
    let mut store = TermStore::new();

    let five = store.mk_bitvec(BigInt::from(5), 8);
    let seven = store.mk_bitvec(BigInt::from(7), 8);
    let five2 = store.mk_bitvec(BigInt::from(5), 8);

    // bvcomp(5, 5) = #b1
    let result = store.mk_bvcomp(five, five2);
    let expected_one = store.mk_bitvec(BigInt::from(1), 1);
    assert_eq!(result, expected_one);

    // bvcomp(5, 7) = #b0
    let result2 = store.mk_bvcomp(five, seven);
    let expected_zero = store.mk_bitvec(BigInt::from(0), 1);
    assert_eq!(result2, expected_zero);
}

#[test]
fn test_bvcomp_reflexivity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));

    // bvcomp(x, x) = #b1
    let result = store.mk_bvcomp(x, x);
    let expected = store.mk_bitvec(BigInt::from(1), 1);
    assert_eq!(result, expected);
}
