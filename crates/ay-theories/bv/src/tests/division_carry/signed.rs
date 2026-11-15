// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn signed_value(value: u64, width: u32) -> i64 {
    let modulus = 1_i64 << width;
    if value & (1 << (width - 1)) == 0 {
        value as i64
    } else {
        value as i64 - modulus
    }
}

fn expected_signed(a: u64, b: u64, width: u32) -> [u64; 3] {
    let mask = (1_u64 << width) - 1;
    let a = signed_value(a, width);
    let b = signed_value(b, width);
    let (q, r, m) = if b == 0 {
        (if a < 0 { 1 } else { -1 }, a, a)
    } else {
        let r = a % b;
        let m = if r != 0 && (r < 0) != (b < 0) {
            r + b
        } else {
            r
        };
        (a / b, r, m)
    };
    [q as u64 & mask, r as u64 & mask, m as u64 & mask]
}

#[test]
fn signed_dispatch_exhausts_small_words_including_zero_and_min_overflow() {
    for width in 1..=5 {
        let mut store = setup_store();
        let a = store.mk_var("a", Sort::bitvec(width));
        let b = store.mk_var("b", Sort::bitvec(width));
        let terms = ["bvsdiv", "bvsrem", "bvsmod"].map(|name| {
            // Raw application prevents construction-time folding from bypassing dispatch.
            store.mk_app(Symbol::named(name), [a, b], Sort::bitvec(width))
        });
        let mut solver = BvSolver::new(&store);
        let a_bits = solver.get_bits(a);
        let b_bits = solver.get_bits(b);
        let outputs = terms.map(|term| solver.get_bits(term));
        assert_eq!(solver.signed_div_cache.len(), 1);
        let circuit = Circuit::new(&solver);
        for av in 0..1_u64 << width {
            for bv in 0..1_u64 << width {
                let fixes = [fix_word(&a_bits, av), fix_word(&b_bits, bv)].concat();
                let model = circuit.propagate(&fixes);
                let actual = outputs.each_ref().map(|bits| word_value(&model, bits));
                assert_eq!(
                    actual,
                    expected_signed(av, bv, width),
                    "w={width},a={av},b={bv}"
                );
            }
        }
    }
}

#[test]
fn unsigned_dispatch_shares_one_divider_in_either_request_order() {
    for reverse in [false, true] {
        let mut store = setup_store();
        let a = store.mk_var("a", Sort::bitvec(5));
        let b = store.mk_var("b", Sort::bitvec(5));
        let q = store.mk_app(Symbol::named("bvudiv"), [a, b], Sort::bitvec(5));
        let r = store.mk_app(Symbol::named("bvurem"), [a, b], Sort::bitvec(5));
        let mut solver = BvSolver::new(&store);
        let first = solver.get_bits(if reverse { r } else { q });
        let count = (solver.num_vars(), solver.clauses().len());
        let second = solver.get_bits(if reverse { q } else { r });
        assert_eq!((solver.num_vars(), solver.clauses().len()), count);
        assert_eq!(solver.unsigned_div_cache.len(), 1);
        let a_bits = solver.get_bits(a);
        let b_bits = solver.get_bits(b);
        let model = Circuit::new(&solver)
            .propagate(&[fix_word(&a_bits, 29), fix_word(&b_bits, 3)].concat());
        let expected = if reverse { (2, 9) } else { (9, 2) };
        assert_eq!(
            (word_value(&model, &first), word_value(&model, &second)),
            expected
        );
    }
}
