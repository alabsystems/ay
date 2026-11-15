// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

#[test]
fn indexed_operator_matrix_matches_for_small_inputs_and_width_changing_edges() {
    let mut terms = TermStore::new();
    for value in 0..4 {
        let arg = bv(&mut terms, value, 2);
        for (name, indices, width) in [
            ("extract", vec![1, 0], 2),
            ("extract", vec![1, 1], 1),
            ("extract", vec![0, 0], 1),
            ("zero_extend", vec![0], 2),
            ("zero_extend", vec![62], 64),
            ("sign_extend", vec![0], 2),
            ("sign_extend", vec![62], 64),
            ("repeat", vec![1], 2),
            ("repeat", vec![32], 64),
        ] {
            let term = indexed(&mut terms, name, &indices, arg, width);
            assert!(matches!(
                compare(&terms, term, &[]),
                Some(EvalValue::BitVec { .. })
            ));
        }
        for name in ["rotate_left", "rotate_right"] {
            for count in [0, 1, 2, 3, u32::MAX] {
                let term = indexed(&mut terms, name, &[count], arg, 2);
                assert!(matches!(
                    compare(&terms, term, &[]),
                    Some(EvalValue::BitVec { .. })
                ));
            }
        }
    }
    let negative = bv(&mut terms, 2, 2);
    let extended = indexed(&mut terms, "sign_extend", &[62], negative, 64);
    assert_eq!(
        compare(&terms, extended, &[]),
        Some(EvalValue::BitVec {
            value: u64::MAX - 1,
            width: 64
        })
    );
    let one = bv(&mut terms, 1, 1);
    let repeated = indexed(&mut terms, "repeat", &[64], one, 64);
    assert_eq!(
        compare(&terms, repeated, &[]),
        Some(EvalValue::BitVec {
            value: u64::MAX,
            width: 64
        })
    );
}

#[test]
fn indexed_shape_and_checked_width_failures_preserve_unsupported_not_a_value() {
    let mut terms = TermStore::new();
    let arg = bv(&mut terms, 2, 2);
    for (name, indices) in [
        ("extract", vec![]),
        ("extract", vec![1]),
        ("extract", vec![0, 1]),
        ("extract", vec![2, 0]),
        ("extract", vec![u32::MAX, 0]),
        ("zero_extend", vec![]),
        ("zero_extend", vec![1, 2]),
        ("zero_extend", vec![63]),
        ("zero_extend", vec![u32::MAX]),
        ("sign_extend", vec![63]),
        ("sign_extend", vec![u32::MAX]),
        ("rotate_left", vec![]),
        ("rotate_right", vec![1, 2]),
        ("repeat", vec![0]),
        ("repeat", vec![33]),
        ("repeat", vec![u32::MAX]),
        ("bvadd", vec![1]),
        ("unknown", vec![1]),
    ] {
        let term = indexed(&mut terms, name, &indices, arg, 2);
        assert_eq!(compare(&terms, term, &[]), None);
    }
    for name in [
        "extract",
        "zero_extend",
        "sign_extend",
        "rotate_left",
        "rotate_right",
        "repeat",
    ] {
        let named = app(&mut terms, name, &[arg], Sort::bitvec(2));
        assert_eq!(compare(&terms, named, &[]), None);
        for args in [vec![], vec![arg, arg]] {
            let term = terms.mk_app(Symbol::indexed(name, vec![1]), args, Sort::bitvec(2));
            assert_eq!(compare(&terms, term, &[]), None);
        }
    }
}
