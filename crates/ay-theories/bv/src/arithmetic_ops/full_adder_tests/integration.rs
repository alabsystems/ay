// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

mod delayed;
mod wide;

#[derive(Clone, Copy, Debug)]
enum Operation {
    Add,
    Subtract,
    Multiply,
    Divide,
}

fn current(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits, operation: Operation) -> Vec<BvBits> {
    match operation {
        Operation::Add => vec![solver.bitblast_add(a, b)],
        Operation::Subtract => vec![solver.bitblast_sub(a, b)],
        Operation::Multiply => vec![solver.bitblast_mul(a, b)],
        Operation::Divide => {
            let (q, r) = solver.bitblast_udiv_urem(a, b);
            vec![q, r]
        }
    }
}

fn previous(
    solver: &mut BvSolver<'_>,
    a: &BvBits,
    b: &BvBits,
    operation: Operation,
) -> Vec<BvBits> {
    match operation {
        Operation::Add => vec![legacy::add(solver, a, b)],
        Operation::Subtract => vec![legacy::subtract(solver, a, b)],
        Operation::Multiply => vec![legacy::multiply(solver, a, b)],
        Operation::Divide => {
            let (q, r) = legacy::divide(solver, a, b);
            vec![q, r]
        }
    }
}

fn expected(a: u64, b: u64, width: usize, operation: Operation) -> Vec<u64> {
    let mask = u64::MAX >> (64 - width);
    match operation {
        Operation::Add => vec![a.wrapping_add(b) & mask],
        Operation::Subtract => vec![a.wrapping_sub(b) & mask],
        Operation::Multiply => vec![a.wrapping_mul(b) & mask],
        Operation::Divide if b == 0 => vec![mask, a],
        Operation::Divide => vec![a / b, a % b],
    }
}

#[test]
fn all_small_arithmetic_outputs_are_forced_by_concrete_inputs() {
    let store = setup_store();
    for width in 1..=5 {
        for operation in [
            Operation::Add,
            Operation::Subtract,
            Operation::Multiply,
            Operation::Divide,
        ] {
            let mut solver = BvSolver::new(&store);
            let a = fresh_word(&mut solver, width);
            let b = fresh_word(&mut solver, width);
            let outputs = current(&mut solver, &a, &b, operation);
            let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
            let mut old = BvSolver::new(&store);
            let old_a = fresh_word(&mut old, width);
            let old_b = fresh_word(&mut old, width);
            assert_eq!(a, old_a);
            assert_eq!(b, old_b);
            let old_outputs = previous(&mut old, &old_a, &old_b, operation);
            let old_circuit = Circuit::from_clauses(old.num_vars(), old.clauses());
            for av in 0..1_u64 << width {
                for bv in 0..1_u64 << width {
                    let fixes = [fix_word(&a, av), fix_word(&b, bv)].concat();
                    let model = circuit.propagate(&fixes);
                    let old_model = old_circuit.propagate(&fixes);
                    let actual: Vec<_> = outputs
                        .iter()
                        .map(|word| word_value(&model, word))
                        .collect();
                    let prior: Vec<_> = old_outputs
                        .iter()
                        .map(|word| word_value(&old_model, word))
                        .collect();
                    let expected = expected(av, bv, width, operation);
                    assert_eq!(actual, expected, "{operation:?} w={width} a={av} b={bv}");
                    assert_eq!(prior, expected, "old {operation:?} w={width} a={av} b={bv}");
                }
            }
        }
    }
}

#[test]
fn small_shift_add_multiplication_exercises_adders_without_const_case_bypass() {
    let store = setup_store();
    for width in 2..=5 {
        let mut solver = BvSolver::new(&store);
        let a = fresh_word(&mut solver, width);
        let b = fresh_word(&mut solver, width);
        let out = solver.bitblast_mul_shift_add(&a, &b);
        let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
        for av in 0..1_u64 << width {
            for bv in 0..1_u64 << width {
                let model = circuit.propagate(&[fix_word(&a, av), fix_word(&b, bv)].concat());
                assert_eq!(word_value(&model, &out), (av * bv) & ((1 << width) - 1));
            }
        }
    }
}

#[test]
fn constant_circuits_preserve_values_and_frozen_uncompressed_paths() {
    let store = setup_store();
    for width in [1, 8, 32, 64] {
        for av in [0, 1, 3, u64::MAX] {
            for bv in [0, 1, 5, u64::MAX] {
                for operation in [
                    Operation::Add,
                    Operation::Subtract,
                    Operation::Multiply,
                    Operation::Divide,
                ] {
                    let mut solver = BvSolver::new(&store);
                    let a = solver.const_bits(av, width);
                    let b = solver.const_bits(bv, width);
                    let outputs = current(&mut solver, &a, &b, operation);
                    let mut old = BvSolver::new(&store);
                    let old_a = old.const_bits(av, width);
                    let old_b = old.const_bits(bv, width);
                    let old_outputs = previous(&mut old, &old_a, &old_b, operation);
                    // Every output bit must be forced by the emitted CNF,
                    // including fully folded constant outputs.
                    let model =
                        Circuit::from_clauses(solver.num_vars(), solver.clauses()).propagate(&[]);
                    let old_model =
                        Circuit::from_clauses(old.num_vars(), old.clauses()).propagate(&[]);
                    let actual: Vec<_> = outputs
                        .iter()
                        .map(|word| word_value(&model, word))
                        .collect();
                    let prior: Vec<_> = old_outputs
                        .iter()
                        .map(|word| word_value(&old_model, word))
                        .collect();
                    let mask = u64::MAX >> (64 - width);
                    let expected = expected(av & mask, bv & mask, width, operation);
                    assert_eq!(actual, expected, "{operation:?} w={width} a={av} b={bv}");
                    assert_eq!(prior, expected, "old {operation:?} w={width} a={av} b={bv}");
                    if matches!(operation, Operation::Divide)
                        && width > 1
                        && (av | bv) & (1_u64 << (width - 1)) == 0
                    {
                        // Common zero high bits deliberately select a smaller
                        // divider. Its literal IDs and CNF need not match the
                        // frozen full-width circuit, but every value above
                        // must agree and no circuit-size dimension may grow.
                        let now = counts(&solver);
                        let before = counts(&old);
                        assert!(
                            now.0 <= before.0 && now.1 <= before.1 && now.2 <= before.2,
                            "w={width} a={av} b={bv}: current={now:?}, frozen={before:?}"
                        );
                    } else {
                        assert_eq!(outputs, old_outputs);
                        assert_eq!(counts(&solver), counts(&old));
                        assert_eq!(solver.clauses(), old.clauses());
                    }
                }
            }
        }
    }
}
