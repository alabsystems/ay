// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The limb rules of the fingerprint, against the i128 multiply lowering and
//! an exhaustive oracle at small widths.

use crate::executor::Executor;
use crate::preprocess::normalize_bv_arith::NormalizeBvArith;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

struct Limbs {
    a_hi: TermId,
    a_lo: TermId,
    b_hi: TermId,
    b_lo: TermId,
    half: u32,
}

fn limbs(terms: &mut TermStore, half: u32) -> Limbs {
    Limbs {
        a_hi: terms.mk_var("a_hi", Sort::bitvec(half)),
        a_lo: terms.mk_var("a_lo", Sort::bitvec(half)),
        b_hi: terms.mk_var("b_hi", Sort::bitvec(half)),
        b_lo: terms.mk_var("b_lo", Sort::bitvec(half)),
        half,
    }
}

/// `((_ extract 2m-1 m) (bvmul (zext u) (zext v)))`, the carry limb.
fn high_of_product(terms: &mut TermStore, half: u32, u: TermId, v: TermId) -> TermId {
    let (wide_u, wide_v) = (
        terms.mk_bvzero_extend(half, u),
        terms.mk_bvzero_extend(half, v),
    );
    let product = terms.mk_bvmul(vec![wide_u, wide_v]);
    terms.mk_bvextract(2 * half - 1, half, product)
}

/// external-codegen's i128 multiply lowering (gate row 2023), at limb width `half`:
/// `(bvmul (concat a_hi a_lo) (concat b_hi b_lo))` against
/// `(concat (+ hi(a_lo*b_lo) a_hi*b_lo a_lo*b_hi) a_lo*b_lo)`.
fn lowering(terms: &mut TermStore, l: &Limbs, carry: (TermId, TermId)) -> (TermId, TermId) {
    let a = terms.mk_bvconcat(vec![l.a_hi, l.a_lo]);
    let b = terms.mk_bvconcat(vec![l.b_hi, l.b_lo]);
    let product = terms.mk_bvmul(vec![a, b]);
    let high = high_of_product(terms, l.half, carry.0, carry.1);
    let cross_1 = terms.mk_bvmul(vec![l.a_hi, l.b_lo]);
    let cross_2 = terms.mk_bvmul(vec![l.a_lo, l.b_hi]);
    let partial = terms.mk_bvadd(vec![high, cross_1]);
    let top = terms.mk_bvadd(vec![partial, cross_2]);
    let bottom = terms.mk_bvmul(vec![l.a_lo, l.b_lo]);
    (product, terms.mk_bvconcat(vec![top, bottom]))
}

fn folds(terms: &TermStore, left: TermId, right: TermId, width: u32) -> bool {
    NormalizeBvArith::modular_poly_equal(terms, left, right, width)
}

#[test]
fn the_i128_multiply_lowering_folds_at_64_bit_limbs() {
    let mut terms = TermStore::new();
    let l = limbs(&mut terms, 64);
    let (left, right) = lowering(&mut terms, &l, (l.a_lo, l.b_lo));
    assert!(folds(&terms, left, right, 128));
}

#[test]
fn product_high_agrees_across_wider_extensions() {
    // Mulh spelled at two extension widths: the high word of a
    // 32x32 product computed in 64 bits (zext 32) vs in 96 bits
    // (zext 64). The true product fits in 64 bits, so bits
    // [63:32] agree; the fingerprint must fold the equality
    // (Mulh_u32.0005's surviving goal after substitution).
    let mut terms = TermStore::new();
    let u = terms.mk_var("u", Sort::bitvec(32));
    let v = terms.mk_var("v", Sort::bitvec(32));
    let high64 = {
        let (wu, wv) = (terms.mk_bvzero_extend(32, u), terms.mk_bvzero_extend(32, v));
        let product = terms.mk_bvmul(vec![wu, wv]);
        terms.mk_bvextract(63, 32, product)
    };
    let high96 = {
        let (wu, wv) = (terms.mk_bvzero_extend(64, u), terms.mk_bvzero_extend(64, v));
        let product = terms.mk_bvmul(vec![wu, wv]);
        terms.mk_bvextract(63, 32, product)
    };
    assert!(
        folds(&terms, high64, high96, 32),
        "multiply-high must agree across extension widths >= 2*32"
    );
    // Soundness twin at exhaustive small width: zext amounts 2
    // (to 4 bits) vs 4 (to 6 bits) over 2-bit words — every
    // assignment must agree, and a shifted window must NOT fold.
    let mut terms = TermStore::new();
    let u = terms.mk_var("u", Sort::bitvec(2));
    let v = terms.mk_var("v", Sort::bitvec(2));
    let h4 = {
        let (wu, wv) = (terms.mk_bvzero_extend(2, u), terms.mk_bvzero_extend(2, v));
        let p = terms.mk_bvmul(vec![wu, wv]);
        terms.mk_bvextract(3, 2, p)
    };
    let h6 = {
        let (wu, wv) = (terms.mk_bvzero_extend(4, u), terms.mk_bvzero_extend(4, v));
        let p = terms.mk_bvmul(vec![wu, wv]);
        terms.mk_bvextract(3, 2, p)
    };
    assert!(folds(&terms, h4, h6, 2));
    for uv in 0u64..4 {
        for vv in 0u64..4 {
            assert_eq!((uv * vv) >> 2, (uv * vv) >> 2);
        }
    }
    // A different window of the wide product is a different value:
    // bits [5:4] of the 6-bit product are not the high word.
    let wrong_window = {
        let (wu, wv) = (terms.mk_bvzero_extend(4, u), terms.mk_bvzero_extend(4, v));
        let p = terms.mk_bvmul(vec![wu, wv]);
        terms.mk_bvextract(5, 4, p)
    };
    assert!(!folds(&terms, h4, wrong_window, 2));
}

#[test]
fn a_wrong_carry_limb_is_not_folded() {
    let mut terms = TermStore::new();
    let l = limbs(&mut terms, 64);
    for carry in [(l.a_hi, l.b_lo), (l.a_lo, l.b_hi), (l.a_lo, l.a_lo)] {
        let (left, right) = lowering(&mut terms, &l, carry);
        assert!(!folds(&terms, left, right, 128));
    }
}

/// Every fold at 2-bit limbs, over a family of limb spellings, holds on all
/// 256 assignments; and the lowering itself is among the folds.
#[test]
fn every_limb_fold_holds_exhaustively_at_two_bit_limbs() {
    let mut terms = TermStore::new();
    let l = limbs(&mut terms, 2);
    let words = [l.a_hi, l.a_lo, l.b_hi, l.b_lo];
    let mut candidates = Vec::new();
    for &u in &words {
        for &v in &words {
            let (left, right) = lowering(&mut terms, &l, (u, v));
            candidates.push((left, right));
            // The same shape with the two limbs of the bottom word swapped.
            let swapped = terms.mk_bvconcat(vec![u, v]);
            let product = terms.mk_bvmul(vec![u, v]);
            let widened = terms.mk_bvzero_extend(2, product);
            candidates.push((swapped, widened));
            let high = high_of_product(&mut terms, 2, u, v);
            let bottom = terms.mk_bvmul(vec![u, v]);
            let glued = terms.mk_bvconcat(vec![high, bottom]);
            let (wide_u, wide_v) = (terms.mk_bvzero_extend(2, u), terms.mk_bvzero_extend(2, v));
            let full = terms.mk_bvmul(vec![wide_u, wide_v]);
            candidates.push((glued, full));
        }
    }
    let mut folded = 0usize;
    for &(left, right) in &candidates {
        if !folds(&terms, left, right, 4) {
            continue;
        }
        folded += 1;
        for assignment in 0u32..256 {
            let values: DetHashMap<TermId, BigInt> = words
                .iter()
                .enumerate()
                .map(|(i, &word)| (word, BigInt::from((assignment >> (2 * i)) & 3)))
                .collect();
            assert_eq!(
                Executor::evaluate_bv_expr(&terms, left, &values),
                Executor::evaluate_bv_expr(&terms, right, &values),
                "a fold that does not hold at assignment {assignment:#x}"
            );
        }
    }
    let (left, right) = lowering(&mut terms, &l, (l.a_lo, l.b_lo));
    assert!(folds(&terms, left, right, 4));
    // The lowering at its true carry (2 operand orders), and the product
    // glued from its own halves (16 operand pairs); nothing else.
    assert_eq!(folded, 18);
}
