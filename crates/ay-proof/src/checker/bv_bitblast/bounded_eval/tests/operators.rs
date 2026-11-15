// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) const BINARY: &[&str] = &[
    "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvadd", "bvsub", "bvmul", "bvudiv",
    "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
];
pub(super) const COMPARISONS: &[&str] = &[
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge", "=",
];

fn binary_matrix(terms: &mut TermStore, width: u32, values: &[u64]) {
    for &left in values {
        let lhs = bv(terms, left, width);
        for &right in values {
            let rhs = bv(terms, right, width);
            for &name in BINARY {
                let term = app(terms, name, &[lhs, rhs], Sort::bitvec(width));
                assert!(matches!(
                    compare(terms, term, &[]),
                    Some(EvalValue::BitVec { .. })
                ));
            }
            for &name in COMPARISONS {
                let term = app(terms, name, &[lhs, rhs], Sort::Bool);
                assert!(matches!(
                    compare(terms, term, &[]),
                    Some(EvalValue::Bool(_))
                ));
            }
        }
        for name in ["bvnot", "bvneg"] {
            let term = app(terms, name, &[lhs], Sort::bitvec(width));
            assert!(matches!(
                compare(terms, term, &[]),
                Some(EvalValue::BitVec { .. })
            ));
        }
    }
}

#[test]
fn every_named_numeric_operator_matches_for_all_one_and_two_bit_values() {
    let mut terms = TermStore::new();
    binary_matrix(&mut terms, 1, &[0, 1]);
    binary_matrix(&mut terms, 2, &[0, 1, 2, 3]);
}

#[test]
fn machine_width_boundaries_keep_overflow_signed_minimum_and_overshift_semantics() {
    let mut terms = TermStore::new();
    binary_matrix(&mut terms, 63, &[0, 1, 63, 1 << 62, (1 << 63) - 1]);
    binary_matrix(&mut terms, 64, &[0, 1, 64, 1 << 63, u64::MAX]);
}

#[test]
fn signed_zero_division_modulo_and_shift_results_have_independent_value_controls() {
    let mut terms = TermStore::new();
    // Values are four-bit two's complement: 13=-3, 14=-2, 15=-1.
    for (name, left, right, expected) in [
        ("bvsdiv", 13, 0, 1),
        ("bvsdiv", 3, 0, 15),
        ("bvsdiv", 8, 15, 8),
        ("bvsrem", 13, 2, 15),
        ("bvsmod", 13, 2, 1),
        ("bvsmod", 3, 14, 15),
        ("bvsrem", 13, 0, 13),
        ("bvsmod", 13, 0, 13),
        ("bvudiv", 3, 0, 15),
        ("bvurem", 3, 0, 3),
        ("bvshl", 3, 4, 0),
        ("bvlshr", 15, 4, 0),
        ("bvashr", 8, 4, 15),
        ("bvashr", 7, 4, 0),
    ] {
        let lhs = bv(&mut terms, left, 4);
        let rhs = bv(&mut terms, right, 4);
        let term = app(&mut terms, name, &[lhs, rhs], Sort::bitvec(4));
        assert_eq!(
            compare(&terms, term, &[]),
            Some(EvalValue::BitVec {
                value: expected,
                width: 4
            })
        );
    }
}

#[test]
fn concat_keeps_high_low_order_and_the_sixty_four_bit_boundary() {
    let mut terms = TermStore::new();
    for (high, high_width, low, low_width, expected) in [
        (2, 2, 1, 2, Some(9)),
        (1, 1, 0, 63, Some(1 << 63)),
        ((1 << 63) - 1, 63, 1, 1, Some(u64::MAX)),
        (1, 64, 0, 1, None),
    ] {
        let hi = bv(&mut terms, high, high_width);
        let lo = bv(&mut terms, low, low_width);
        let width = high_width + low_width;
        let term = app(&mut terms, "concat", &[hi, lo], Sort::bitvec(width));
        assert_eq!(
            compare(&terms, term, &[]),
            expected.map(|value| EvalValue::BitVec { value, width })
        );
    }
}
