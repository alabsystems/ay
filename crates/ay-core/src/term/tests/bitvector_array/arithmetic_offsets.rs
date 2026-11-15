// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::*;

#[test]
fn test_bvadd_reassociates_constant_offsets_without_reordering_symbols() {
    for width in [1, 8, 32, 64, 256] {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::bitvec(width));
        let y = store.mk_var("y", Sort::bitvec(width));
        let one = store.mk_bitvec(BigInt::from(1), width);
        let xy = store.mk_bvadd(vec![x, y]);
        let yx = store.mk_bvadd(vec![y, x]);
        let expected_xy = store.mk_bvadd(vec![xy, one]);
        let expected_yx = store.mk_bvadd(vec![yx, one]);
        for inner in [vec![one, x], vec![x, one]] {
            let offset = store.mk_bvadd(inner);
            assert_eq!(store.mk_bvadd(vec![offset, y]), expected_xy);
            assert_eq!(store.mk_bvadd(vec![y, offset]), expected_yx);
        }
        let all_ones = store.mk_bitvec((BigInt::from(1) << width) - 1, width);
        let y_minus_one = store.mk_bvadd(vec![y, all_ones]);
        let x_plus_one = store.mk_bvadd(vec![x, one]);
        assert_eq!(store.mk_bvadd(vec![x_plus_one, y_minus_one]), xy);
    }
}

#[test]
fn test_bvadd_reassociated_offsets_preserve_every_small_value() {
    // Enumerate all inputs and offsets, including overflow, against direct
    // modular arithmetic rather than only comparing constructor shapes.
    for width in 1..=4 {
        let modulus = 1_u32 << width;
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::bitvec(width));
        let y = store.mk_var("y", Sort::bitvec(width));
        for offset in 0..modulus {
            let c = store.mk_bitvec(BigInt::from(offset), width);
            let inner = store.mk_bvadd(vec![c, x]);
            let expressions = [
                store.mk_bvadd(vec![inner, y]),
                store.mk_bvadd(vec![y, inner]),
            ];
            for xv in 0..modulus {
                for yv in 0..modulus {
                    let inputs = [
                        store.mk_bitvec(BigInt::from(xv), width),
                        store.mk_bitvec(BigInt::from(yv), width),
                    ];
                    let expected =
                        store.mk_bitvec(BigInt::from((xv + yv + offset) % modulus), width);
                    for expression in expressions {
                        assert_eq!(store.substitute(expression, &[x, y], &inputs), expected);
                    }
                }
            }
        }
    }
}

#[test]
fn test_bv_offsets_preserve_malformed_nested_widths() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let wide = store.mk_bitvec(BigInt::from(1), 16);
    for op in ["bvadd", "bvsub"] {
        let malformed = store.intern(
            TermData::App(Symbol::named(op), vec![x, wide]),
            Sort::bitvec(8),
        );
        let chained = if op == "bvadd" {
            store.mk_bvadd(vec![malformed, one])
        } else {
            store.mk_bvsub(vec![malformed, one])
        };
        assert!(matches!(store.get(chained), TermData::App(_, args) if args == &[malformed, one]));
        if op == "bvadd" {
            let symbolic = store.mk_bvadd(vec![malformed, y]);
            assert!(
                matches!(store.get(symbolic), TermData::App(_, args) if args == &[malformed, y])
            );
        }
    }
}
