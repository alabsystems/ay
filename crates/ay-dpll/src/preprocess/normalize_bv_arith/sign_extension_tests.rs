// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::preprocess::normalize_bv_arith::NormalizeBvArith;

fn bv(terms: &mut TermStore, value: u64, width: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(value), width)
}

/// `concat(ite(msb(x) = b, then, else), x)` over the low 32 bits of `word`.
fn spelled(terms: &mut TermStore, word: TermId, bit: u64, then_ones: bool) -> TermId {
    let low = terms.mk_bvextract(31, 0, word);
    let sign = terms.mk_bvextract(31, 31, low);
    let literal = bv(terms, bit, 1);
    let condition = terms.mk_eq(sign, literal);
    let (ones, zero) = (bv(terms, u64::from(u32::MAX), 32), bv(terms, 0, 32));
    let high = if then_ones {
        terms.mk_ite(condition, ones, zero)
    } else {
        terms.mk_ite(condition, zero, ones)
    };
    terms.mk_bvconcat(vec![high, low])
}

#[test]
fn a_spelled_sign_extension_rebuilds_as_the_operator() {
    let mut terms = TermStore::new();
    let word = terms.mk_var("x", Sort::bitvec(64));
    let low = terms.mk_bvextract(31, 0, word);
    let operator = terms.mk_bvsign_extend(32, low);
    for (bit, then_ones) in [(1, true), (0, false)] {
        let spelled = spelled(&mut terms, word, bit, then_ones);
        assert_ne!(
            spelled, operator,
            "the constructor must not already fold it"
        );
        let mut pass = NormalizeBvArith::new();
        assert_eq!(pass.normalize(&mut terms, spelled), operator);
    }
}

#[test]
fn a_product_of_the_two_spellings_folds_by_hash_consing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let (x_low, y_low) = (terms.mk_bvextract(31, 0, x), terms.mk_bvextract(31, 0, y));
    let (x_ext, y_ext) = (
        terms.mk_bvsign_extend(32, x_low),
        terms.mk_bvsign_extend(32, y_low),
    );
    let (x_spelled, y_spelled) = (
        spelled(&mut terms, x, 1, true),
        spelled(&mut terms, y, 1, true),
    );
    let left = terms.mk_bvmul(vec![x_spelled, y_spelled]);
    let right = terms.mk_bvmul(vec![x_ext, y_ext]);
    let equality = terms.mk_eq(left, right);
    let mut pass = NormalizeBvArith::new();
    assert_eq!(pass.normalize(&mut terms, equality), terms.mk_bool(true));
}

#[test]
fn a_near_miss_stays_a_concat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let other = terms.mk_var("other", Sort::bitvec(64));
    let low = terms.mk_bvextract(31, 0, x);
    let ones = bv(&mut terms, u64::from(u32::MAX), 32);
    let zero = bv(&mut terms, 0, 32);
    let one = bv(&mut terms, 1, 1);
    let cases = [
        // The branch order disagrees with the tested value.
        spelled(&mut terms, x, 0, true),
        spelled(&mut terms, x, 1, false),
        // The tested bit is not the operand's sign bit.
        {
            let bit = terms.mk_bvextract(30, 30, low);
            let condition = terms.mk_eq(bit, one);
            let high = terms.mk_ite(condition, ones, zero);
            terms.mk_bvconcat(vec![high, low])
        },
        // The tested word is another operand.
        {
            let other_low = terms.mk_bvextract(31, 0, other);
            let bit = terms.mk_bvextract(31, 31, other_low);
            let condition = terms.mk_eq(bit, one);
            let high = terms.mk_ite(condition, ones, zero);
            terms.mk_bvconcat(vec![high, low])
        },
        // A branch is not all ones.
        {
            let bit = terms.mk_bvextract(31, 31, low);
            let condition = terms.mk_eq(bit, one);
            let almost = bv(&mut terms, u64::from(u32::MAX) - 1, 32);
            let high = terms.mk_ite(condition, almost, zero);
            terms.mk_bvconcat(vec![high, low])
        },
    ];
    for case in cases {
        let mut pass = NormalizeBvArith::new();
        let normalized = pass.normalize(&mut terms, case);
        assert!(
            matches!(terms.get(normalized), TermData::App(Symbol::Named(name), _) if name == "concat"),
            "a near miss must stay a concat"
        );
    }
}
