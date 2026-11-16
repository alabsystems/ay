// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Concrete CNF propagation, without a SAT solver or production gate evaluator.

use super::*;
use crate::cnf_test_support::{bit_value, word_value, Circuit};

mod oracle;
mod signed;
mod wide;
mod zero_padding;

fn fresh_word(solver: &mut BvSolver<'_>, width: usize) -> BvBits {
    solver.batch_fresh_vars(width).to_vec()
}

fn fix_word(bits: &[CnfLit], value: u64) -> Vec<CnfLit> {
    bits.iter()
        .enumerate()
        .map(|(bit, &lit)| if value & (1 << bit) != 0 { lit } else { -lit })
        .collect()
}

fn check_subtraction(solver: &mut BvSolver<'_>, inputs: &BvBits, a: &BvBits, b: &BvBits) {
    let width = a.len();
    let mask = (1_u64 << width) - 1;
    let (difference, no_borrow) = solver.bitblast_sub_with_carry(a, b);
    let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
    for assignment in 0..1_u64 << inputs.len() {
        let model = circuit.propagate(&fix_word(inputs, assignment));
        let av = word_value(&model, a);
        let bv = word_value(&model, b);
        assert_eq!(word_value(&model, &difference), av.wrapping_sub(bv) & mask);
        assert_eq!(bit_value(&model, no_borrow), av >= bv);
    }
}

#[test]
fn fused_subtraction_exhausts_width_zero_through_six() {
    let store = setup_store();
    for width in 0..=6 {
        for complemented in [false, true] {
            let mut solver = BvSolver::new(&store);
            let a = fresh_word(&mut solver, width);
            let raw_b = fresh_word(&mut solver, width);
            let inputs = [a.as_slice(), raw_b.as_slice()].concat();
            let b = raw_b
                .iter()
                .map(|&bit| if complemented { -bit } else { bit })
                .collect();
            check_subtraction(&mut solver, &inputs, &a, &b);
        }
    }
}

#[test]
fn fused_subtraction_preserves_alias_complement_and_constant_literals() {
    let store = setup_store();
    for width in 0..=6 {
        for pattern in 0..4 {
            let mut solver = BvSolver::new(&store);
            let a = fresh_word(&mut solver, width);
            let f = solver.fresh_false();
            let b = a
                .iter()
                .enumerate()
                .map(|(i, &lit)| match pattern {
                    0 => lit,
                    1 => -lit,
                    2 => {
                        if i % 2 == 0 {
                            f
                        } else {
                            -f
                        }
                    }
                    _ => -a[width - 1 - i],
                })
                .collect();
            check_subtraction(&mut solver, &a, &a, &b);
        }
    }
}

#[test]
fn restoring_division_exhausts_unsigned_width_one_through_five() {
    let store = setup_store();
    for width in 1..=5 {
        let mut solver = BvSolver::new(&store);
        let a = fresh_word(&mut solver, width);
        let b = fresh_word(&mut solver, width);
        let (q, r) = solver.bitblast_udiv_urem(&a, &b);
        let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
        let mut old = BvSolver::new(&store);
        let old_a = fresh_word(&mut old, width);
        let old_b = fresh_word(&mut old, width);
        let (old_q, old_r) = oracle::divide(&mut old, &old_a, &old_b);
        let old_circuit = Circuit::from_clauses(old.num_vars(), old.clauses());
        let limit = 1_u64 << width;
        for av in 0..limit {
            for bv in 0..limit {
                let fixes = [fix_word(&a, av), fix_word(&b, bv)].concat();
                let model = circuit.propagate(&fixes);
                let old_model = old_circuit.propagate(&fixes);
                let expected = match av.checked_div(bv) {
                    Some(quotient) => (quotient, av % bv),
                    None => (limit - 1, av),
                };
                assert_eq!((word_value(&model, &q), word_value(&model, &r)), expected);
                assert_eq!(
                    (
                        word_value(&old_model, &old_q),
                        word_value(&old_model, &old_r)
                    ),
                    expected
                );
            }
        }
    }
}

#[test]
fn empty_division_preserves_empty_no_allocation_result() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    assert_eq!(
        solver.bitblast_udiv_urem(&vec![], &vec![]),
        (vec![], vec![])
    );
    assert_eq!(solver.num_vars(), 0);
    assert_eq!(solver.clauses(), &[] as &[CnfClause]);
}
