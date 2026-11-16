// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn zero_padded_division_exhausts_small_inputs_including_zero_divisors() {
    let store = setup_store();
    for a_width in 1..=3 {
        for b_width in 1..=3 {
            for width in [4, 32, 64] {
                let mut solver = BvSolver::new(&store);
                let a = fresh_word(&mut solver, a_width);
                let b = fresh_word(&mut solver, b_width);
                let zero = solver.fresh_false();
                let mut padded_a = a.clone();
                let mut padded_b = b.clone();
                padded_a.resize(width, zero);
                padded_b.resize(width, zero);
                let (q, r) = solver.bitblast_udiv_urem(&padded_a, &padded_b);
                assert_eq!((q.len(), r.len()), (width, width));
                let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
                let mask = u64::MAX >> (64 - width);
                for av in 0..1_u64 << a_width {
                    for bv in 0..1_u64 << b_width {
                        let model =
                            circuit.propagate(&[fix_word(&a, av), fix_word(&b, bv)].concat());
                        let expected = match av.checked_div(bv) {
                            Some(quotient) => (quotient, av % bv),
                            None => (mask, av),
                        };
                        assert_eq!(
                            (word_value(&model, &q), word_value(&model, &r)),
                            expected,
                            "a_width={a_width},b_width={b_width},width={width},a={av},b={bv}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn zero_padded_native_dispatch_preserves_division_remainder_cache() {
    for reverse in [false, true] {
        let mut store = setup_store();
        let a = store.mk_var("a", Sort::bitvec(8));
        let b = store.mk_var("b", Sort::bitvec(8));
        let padded_a = store.mk_bvzero_extend(24, a);
        let padded_b = store.mk_bvzero_extend(24, b);
        let q = store.mk_app(
            Symbol::named("bvudiv"),
            [padded_a, padded_b],
            Sort::bitvec(32),
        );
        let r = store.mk_app(
            Symbol::named("bvurem"),
            [padded_a, padded_b],
            Sort::bitvec(32),
        );
        let mut solver = BvSolver::new(&store);
        let first = solver.get_bits(if reverse { r } else { q });
        let before = (solver.num_vars(), solver.clauses().len());
        let second = solver.get_bits(if reverse { q } else { r });
        assert_eq!((solver.num_vars(), solver.clauses().len()), before);
        assert_eq!(solver.unsigned_div_cache.len(), 1);
        let a_bits = solver.get_bits(a);
        let b_bits = solver.get_bits(b);
        let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
        for (av, bv) in [(255, 0), (0, 0), (255, 1), (255, 3), (1, 255)] {
            let model = circuit.propagate(&[fix_word(&a_bits, av), fix_word(&b_bits, bv)].concat());
            let (q, r) = match av.checked_div(bv) {
                Some(quotient) => (quotient, av % bv),
                None => (u32::MAX as u64, av),
            };
            let expected = if reverse { (r, q) } else { (q, r) };
            assert_eq!(
                (word_value(&model, &first), word_value(&model, &second)),
                expected
            );
        }
    }
}

#[test]
fn zero_padded_small_unsigned_division_uses_its_actual_eager_circuit() {
    for (a_width, b_width) in [(8, 8), (8, 12), (12, 8)] {
        for width in [32, 64] {
            let mut store = setup_store();
            let a = store.mk_var("a", Sort::bitvec(a_width));
            let b = store.mk_var("b", Sort::bitvec(b_width));
            let za = store.mk_bvzero_extend(width - a_width, a);
            let zb = store.mk_bvzero_extend(width - b_width, b);
            let q = store.mk_app(Symbol::named("bvudiv"), [za, zb], Sort::bitvec(width));
            let r = store.mk_app(Symbol::named("bvurem"), [za, zb], Sort::bitvec(width));
            let mut solver = BvSolver::new(&store);
            solver.set_delay_enabled(true);
            let q = solver.get_bits(q);
            let r = solver.get_bits(r);
            assert_eq!((q.len(), r.len()), (width as usize, width as usize));
            assert!(solver.delayed_ops().is_empty());
            let a_bits = solver.get_bits(a);
            let b_bits = solver.get_bits(b);
            let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
            for (av, bv) in [(255, 0), (0, 0), (255, 1), (255, 3), (1, 255)] {
                let model =
                    circuit.propagate(&[fix_word(&a_bits, av), fix_word(&b_bits, bv)].concat());
                let expected = match av.checked_div(bv) {
                    Some(quotient) => (quotient, av % bv),
                    None => (u64::MAX >> (64 - width), av),
                };
                assert_eq!((word_value(&model, &q), word_value(&model, &r)), expected);
            }
        }
    }
}

#[test]
fn zero_padded_wide_or_signed_division_retains_delayed_classification() {
    for (a_width, b_width, operation) in [
        (13, 13, "bvudiv"),
        (13, 13, "bvurem"),
        (8, 13, "bvudiv"),
        (13, 8, "bvudiv"),
        (8, 13, "bvurem"),
        (13, 8, "bvurem"),
        (8, 8, "bvsdiv"),
        (8, 8, "bvsrem"),
        (8, 8, "bvsmod"),
    ] {
        let mut store = setup_store();
        let a = store.mk_var("a", Sort::bitvec(a_width));
        let b = store.mk_var("b", Sort::bitvec(b_width));
        let a = store.mk_bvzero_extend(32 - a_width, a);
        let b = store.mk_bvzero_extend(32 - b_width, b);
        let term = store.mk_app(Symbol::named(operation), [a, b], Sort::bitvec(32));
        let mut solver = BvSolver::new(&store);
        solver.set_delay_enabled(true);
        assert_eq!(solver.get_bits(term).len(), 32);
        assert_eq!(solver.delayed_ops().len(), 1);
    }
}
