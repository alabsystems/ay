// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn fix_big_word(bits: &[CnfLit], value: &BigInt) -> Vec<CnfLit> {
    bits.iter()
        .enumerate()
        .map(|(index, &lit)| {
            if ((value >> index) & BigInt::from(1)) != BigInt::from(0) {
                lit
            } else {
                -lit
            }
        })
        .collect()
}

fn big_word_value(model: &[Option<bool>], bits: &[CnfLit]) -> BigInt {
    bits.iter()
        .enumerate()
        .fold(BigInt::from(0), |value, (index, &lit)| {
            if bit_value(model, lit) {
                value | (BigInt::from(1) << index)
            } else {
                value
            }
        })
}

fn counts(solver: &BvSolver<'_>) -> (u32, usize, usize) {
    (
        solver.num_vars(),
        solver.clauses().len(),
        solver.clauses().iter().map(|c| c.literals().len()).sum(),
    )
}

fn assert_smaller(width: usize, solver: &BvSolver<'_>, old: &BvSolver<'_>) {
    let current = counts(solver);
    let legacy = counts(old);
    assert!(
        current.0 < legacy.0,
        "width {width}: new {current:?}, old {legacy:?}"
    );
    assert!(
        current.1 < legacy.1,
        "width {width}: new {current:?}, old {legacy:?}"
    );
    assert!(
        current.2 < legacy.2,
        "width {width}: new {current:?}, old {legacy:?}"
    );
}

#[test]
fn dense_dividers_strictly_reduce_real_cnf_at_widths_32_and_64() {
    let store = setup_store();
    for width in [32, 64] {
        let mut solver = BvSolver::new(&store);
        let a = fresh_word(&mut solver, width);
        let b = fresh_word(&mut solver, width);
        let _ = solver.bitblast_udiv_urem(&a, &b);
        let mut old = BvSolver::new(&store);
        let old_a = fresh_word(&mut old, width);
        let old_b = fresh_word(&mut old, width);
        let _ = oracle::divide(&mut old, &old_a, &old_b);
        assert_smaller(width, &solver, &old);
    }
}

#[test]
fn wide_dense_divider_models_match_big_integer_and_frozen_cnf() {
    let store = setup_store();
    for width in [64, 129] {
        let mut solver = BvSolver::new(&store);
        let a = fresh_word(&mut solver, width);
        let b = fresh_word(&mut solver, width);
        let (q, r) = solver.bitblast_udiv_urem(&a, &b);
        let circuit = Circuit::new(&solver);
        let mut old = BvSolver::new(&store);
        let old_a = fresh_word(&mut old, width);
        let old_b = fresh_word(&mut old, width);
        let (old_q, old_r) = oracle::divide(&mut old, &old_a, &old_b);
        let old_circuit = Circuit::new(&old);
        assert_smaller(width, &solver, &old);
        let max = (BigInt::from(1) << width) - BigInt::from(1);
        let high = BigInt::from(1) << (width - 1);
        let cases = [
            (max.clone(), BigInt::from(0)),
            (max.clone(), BigInt::from(1)),
            (max.clone(), BigInt::from(3)),
            (&high + BigInt::from(19), &high + BigInt::from(1)),
            (&high - BigInt::from(1), high.clone()),
            (BigInt::from(0), max.clone()),
        ];
        for (av, bv) in cases {
            let fixes = [fix_big_word(&a, &av), fix_big_word(&b, &bv)].concat();
            let model = circuit.propagate(&fixes);
            let old_model = old_circuit.propagate(&fixes);
            let expected = if bv == BigInt::from(0) {
                (max.clone(), av.clone())
            } else {
                (&av / &bv, &av % &bv)
            };
            assert_eq!(
                (big_word_value(&model, &q), big_word_value(&model, &r)),
                expected
            );
            assert_eq!(
                (
                    big_word_value(&old_model, &old_q),
                    big_word_value(&old_model, &old_r)
                ),
                expected
            );
        }
    }
}

#[test]
fn wide_fused_subtraction_preserves_high_bit_carry() {
    let store = setup_store();
    for width in [64, 129] {
        let mut solver = BvSolver::new(&store);
        let a = fresh_word(&mut solver, width);
        let b = fresh_word(&mut solver, width);
        let (difference, carry) = solver.bitblast_sub_with_carry(&a, &b);
        let circuit = Circuit::new(&solver);
        let max = (BigInt::from(1) << width) - BigInt::from(1);
        let high = BigInt::from(1) << (width - 1);
        for (av, bv) in [
            (max.clone(), high.clone()),
            (high.clone(), high),
            (BigInt::from(0), max.clone()),
        ] {
            let fixes = [fix_big_word(&a, &av), fix_big_word(&b, &bv)].concat();
            let model = circuit.propagate(&fixes);
            assert_eq!(big_word_value(&model, &difference), (&av - &bv) & &max);
            assert_eq!(bit_value(&model, carry), av >= bv);
        }
    }
}

#[test]
fn zero_padded_129_bit_dispatch_preserves_full_width_zero_division() {
    let mut store = setup_store();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let padded_a = store.mk_bvzero_extend(121, a);
    let padded_b = store.mk_bvzero_extend(121, b);
    let quotient = store.mk_app(
        Symbol::named("bvudiv"),
        [padded_a, padded_b],
        Sort::bitvec(129),
    );
    let remainder = store.mk_app(
        Symbol::named("bvurem"),
        [padded_a, padded_b],
        Sort::bitvec(129),
    );
    let mut solver = BvSolver::new(&store);
    let q = solver.get_bits(quotient);
    let r = solver.get_bits(remainder);
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let circuit = Circuit::new(&solver);
    let max: BigInt = (BigInt::from(1) << 129_usize) - BigInt::from(1);
    for (av, bv) in [(255_u32, 0_u32), (0, 0), (255, 1), (255, 3), (1, 255)] {
        let av = BigInt::from(av);
        let bv = BigInt::from(bv);
        let fixes = [fix_big_word(&a_bits, &av), fix_big_word(&b_bits, &bv)].concat();
        let model = circuit.propagate(&fixes);
        let expected = if bv == BigInt::from(0) {
            (max.clone(), av)
        } else {
            (&av / &bv, &av % &bv)
        };
        assert_eq!(
            (big_word_value(&model, &q), big_word_value(&model, &r)),
            expected
        );
    }
}
