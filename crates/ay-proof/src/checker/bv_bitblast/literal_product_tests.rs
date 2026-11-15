// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{evaluate, mask, non_adjacent_form};
use crate::checker::bv_bitblast::recognize_bv_bitblast;
use ay_core::{Sort, Symbol, TermId, TermStore};

fn app(terms: &mut TermStore, op: &str, args: [TermId; 2], width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::bitvec(width))
}

fn literal(terms: &mut TermStore, value: u128, width: u32) -> TermId {
    terms.mk_bitvec(value.into(), width)
}

/// Every digit string is its value modulo `2^w`, no two digits are adjacent
/// and none reaches the width.
#[test]
fn the_digits_are_the_value_modulo_the_width_and_non_adjacent() {
    for width in [1_u32, 4, 10, 64, 128] {
        let samples = (0..600_u128).chain([511, (1 << 32) - 1, u128::from(u64::MAX), u128::MAX]);
        for value in samples.map(|value| value & mask(width)) {
            let digits = non_adjacent_form(value, width);
            assert_eq!(evaluate(&digits, width), value, "{value} at {width}");
            assert!(digits.windows(2).all(|pair| pair[0].0 > pair[1].0 + 1));
            assert!(digits.iter().all(|&(power, _)| power < width));
        }
    }
    assert_eq!(non_adjacent_form(511, 64), vec![(9, false), (0, true)]);
    assert_eq!(non_adjacent_form(u128::from(u64::MAX), 64), vec![(0, true)]);
}

/// Gate rows 1901 and 1903: `x * (2^a - 1)` against `(x << a) - x` at 64
/// bits is recognized, in both operand orders, and a subtractor off by one is
/// not.
#[test]
fn a_strength_reduced_product_is_its_shift_difference() {
    let width = 64;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    for shift in [9_u32, 32] {
        let constant = literal(&mut terms, (1_u128 << shift) - 1, width);
        let amount = literal(&mut terms, u128::from(shift), width);
        let shifted = app(&mut terms, "bvshl", [x, amount], width);
        let difference = app(&mut terms, "bvsub", [shifted, x], width);
        for product in [[constant, x], [x, constant]] {
            let product = app(&mut terms, "bvmul", product, width);
            let identity = terms.mk_eq(product, difference);
            assert!(recognize_bv_bitblast(&terms, &[identity]), "a={shift}");
            let one = literal(&mut terms, 1, width);
            let off = app(&mut terms, "bvadd", [difference, one], width);
            let false_identity = terms.mk_eq(product, off);
            assert!(
                !recognize_bv_bitblast(&terms, &[false_identity]),
                "a={shift}"
            );
        }
    }
}

/// At 10 bits (past the exhaustive evaluator, so the proof-producing lowering
/// decides), a literal product is recognized equal to its binary
/// shift-and-add spelling, which multiplies nothing, and never to that sum
/// plus one: whichever lowering a literal takes, it is the product. The
/// literals are the small ones and every `±2^a ± 2^b ± 1`, which covers each
/// digit count the lowering admits and some it does not.
#[test]
fn a_literal_product_is_its_binary_shift_sum() {
    let width = 10;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let one = literal(&mut terms, 1, width);
    let powers = || (0..width).map(|power| 1_u128 << power);
    let signed = |value: u128, negative: bool| {
        if negative {
            value.wrapping_neg()
        } else {
            value
        }
    };
    let mut values: Vec<u128> = (0..40).collect();
    for high in powers() {
        for low in powers() {
            for (negative_high, negative_low) in
                [(false, false), (false, true), (true, false), (true, true)]
            {
                let sum = signed(high, negative_high).wrapping_add(signed(low, negative_low));
                values.extend(
                    [sum.wrapping_sub(1), sum.wrapping_add(1)].map(|value| value & mask(width)),
                );
            }
        }
    }
    values.sort_unstable();
    values.dedup();
    let mut checked = 0;
    for value in values {
        let constant = literal(&mut terms, value, width);
        let product = app(&mut terms, "bvmul", [constant, x], width);
        let mut sum = literal(&mut terms, 0, width);
        for power in (0..width).filter(|&power| (value >> power) & 1 == 1) {
            let amount = literal(&mut terms, u128::from(power), width);
            let shifted = app(&mut terms, "bvshl", [x, amount], width);
            sum = app(&mut terms, "bvadd", [sum, shifted], width);
        }
        if product == sum {
            // The store folded both spellings to one term (`0`, `x`, ...).
            continue;
        }
        let identity = terms.mk_eq(product, sum);
        assert!(recognize_bv_bitblast(&terms, &[identity]), "c={value}");
        let off = app(&mut terms, "bvadd", [sum, one], width);
        let false_identity = terms.mk_eq(product, off);
        assert!(
            !recognize_bv_bitblast(&terms, &[false_identity]),
            "c={value}"
        );
        checked += 1;
    }
    assert!(checked > 200, "only {checked} literals were checked");
}
