// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use num_bigint::BigInt;

#[derive(Clone, Copy, Debug)]
enum Shape {
    Dense,
    ZeroExtended,
}

fn inputs(solver: &mut BvSolver<'_>, width: usize, shape: Shape) -> (BvBits, BvBits, usize) {
    let active = match shape {
        Shape::Dense => width,
        Shape::ZeroExtended => 16.min(width),
    };
    let mut a = fresh_word(solver, active);
    let mut b = fresh_word(solver, active);
    if active < width {
        let zero = solver.fresh_false();
        a.resize(width, zero);
        b.resize(width, zero);
    }
    (a, b, active)
}

fn fix_big(bits: &[CnfLit], value: &BigInt) -> Vec<CnfLit> {
    bits.iter()
        .enumerate()
        .map(|(index, &lit)| {
            if ((value >> index) & BigInt::from(1)) == BigInt::from(0) {
                -lit
            } else {
                lit
            }
        })
        .collect()
}

fn big_value(model: &[Option<bool>], word: &[CnfLit]) -> BigInt {
    word.iter()
        .enumerate()
        .fold(BigInt::from(0), |value, (index, &lit)| {
            if bit_value(model, lit) {
                value | (BigInt::from(1) << index)
            } else {
                value
            }
        })
}

fn expected_big(a: &BigInt, b: &BigInt, mask: &BigInt, operation: Operation) -> Vec<BigInt> {
    match operation {
        Operation::Add => vec![(a + b) & mask],
        Operation::Subtract => vec![(a - b) & mask],
        Operation::Multiply => vec![(a * b) & mask],
        Operation::Divide if b == &BigInt::from(0) => vec![mask.clone(), a.clone()],
        Operation::Divide => vec![a / b, a % b],
    }
}

fn cases(active: usize) -> Vec<(BigInt, BigInt)> {
    let max = (BigInt::from(1) << active) - BigInt::from(1);
    let high = BigInt::from(1) << (active - 1);
    vec![
        (max.clone(), BigInt::from(0)),
        (max.clone(), BigInt::from(1)),
        (max.clone(), BigInt::from(3)),
        (
            high.clone() + BigInt::from(19),
            high.clone() + BigInt::from(1),
        ),
        (high.clone() - BigInt::from(1), high),
        (BigInt::from(0), max),
    ]
}

fn compare_models(width: usize, shape: Shape, operation: Operation) {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    let (a, b, active) = inputs(&mut solver, width, shape);
    let outputs = current(&mut solver, &a, &b, operation);
    let circuit = Circuit::new(&solver);
    let mut old = BvSolver::new(&store);
    let (old_a, old_b, old_active) = inputs(&mut old, width, shape);
    assert_eq!(active, old_active);
    assert_eq!(a, old_a);
    assert_eq!(b, old_b);
    let old_outputs = previous(&mut old, &old_a, &old_b, operation);
    let old_circuit = Circuit::new(&old);
    let mask = (BigInt::from(1) << width) - BigInt::from(1);
    for (av, bv) in cases(active) {
        let fixes = [fix_big(&a, &av), fix_big(&b, &bv)].concat();
        let model = circuit.propagate(&fixes);
        let old_model = old_circuit.propagate(&fixes);
        let values: Vec<_> = outputs.iter().map(|word| big_value(&model, word)).collect();
        let prior: Vec<_> = old_outputs
            .iter()
            .map(|word| big_value(&old_model, word))
            .collect();
        let expected = expected_big(&av, &bv, &mask, operation);
        assert_eq!(values, expected, "{operation:?} {shape:?} w={width}");
        assert_eq!(prior, expected, "old {operation:?} {shape:?} w={width}");
    }
}

#[test]
fn wide_dense_and_padded_arithmetic_match_exact_big_integer_results() {
    for width in [64, 129] {
        for shape in [Shape::Dense, Shape::ZeroExtended] {
            for operation in [
                Operation::Add,
                Operation::Subtract,
                Operation::Multiply,
                Operation::Divide,
            ] {
                compare_models(width, shape, operation);
            }
        }
    }
}

#[test]
fn fresh_dense_arithmetic_reduces_frozen_base_cnf() {
    let store = setup_store();
    for width in [32, 64] {
        for operation in [
            Operation::Add,
            Operation::Subtract,
            Operation::Multiply,
            Operation::Divide,
        ] {
            let mut solver = BvSolver::new(&store);
            let (a, b, _) = inputs(&mut solver, width, Shape::Dense);
            let _ = current(&mut solver, &a, &b, operation);
            let mut old = BvSolver::new(&store);
            let (old_a, old_b, _) = inputs(&mut old, width, Shape::Dense);
            let _ = previous(&mut old, &old_a, &old_b, operation);
            let new = counts(&solver);
            let prior = counts(&old);
            assert!(
                new.0 < prior.0 && new.1 < prior.1 && new.2 < prior.2,
                "{operation:?} w={width}: new {new:?}, frozen base {prior:?}"
            );
        }
    }
}

#[test]
fn zero_extended_arithmetic_does_not_grow_the_frozen_base_cnf() {
    let store = setup_store();
    for width in [32, 64] {
        for operation in [
            Operation::Add,
            Operation::Subtract,
            Operation::Multiply,
            Operation::Divide,
        ] {
            let mut solver = BvSolver::new(&store);
            let (a, b, _) = inputs(&mut solver, width, Shape::ZeroExtended);
            let _ = current(&mut solver, &a, &b, operation);
            let mut old = BvSolver::new(&store);
            let (old_a, old_b, _) = inputs(&mut old, width, Shape::ZeroExtended);
            let _ = previous(&mut old, &old_a, &old_b, operation);
            let new = counts(&solver);
            let prior = counts(&old);
            assert!(
                new.0 <= prior.0 && new.1 <= prior.1 && new.2 <= prior.2,
                "{operation:?} padded w={width}: new {new:?}, frozen base {prior:?}"
            );
        }
    }
}
