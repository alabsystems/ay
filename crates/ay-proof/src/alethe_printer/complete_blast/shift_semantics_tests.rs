// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The barrel-shifter circuits a `bitblast_shl`/`bitblast_lshr`/
//! `bitblast_ashr` conclusion prints are TRUE wherever AY prints them:
//! evaluated over every operand pair they agree with SMT-LIB's
//! `bvshl`/`bvlshr`/`bvashr`.
//!
//! The consumer re-derives the circuit and compares it syntactically, so a
//! circuit that is merely accepted by some checker version is not evidence
//! that it is right. Upstream Carcara 9a352ee builds the `bvashr` circuit with
//! a zero-filled overshift layer, which is wrong for a negative operand
//! (`(bvashr #x8 #x4)` is `#xf`, not `#x0`); AY copied that layer, Clean's
//! Carcara (which fills with the sign bit) refused 18 of external-codegen's
//! certificates for it, and nothing in AY evaluated the circuit. The default
//! (Clean) circuit is exact everywhere; the `AletheDialect::PinnedCarcara` one
//! only inside the domain `arithmetic_shift_is_admissible` admits, and the
//! negative control below pins why that guard is load-bearing.

use super::super::dialect::{with_alethe_dialect, AletheDialect};
use super::circuit::{Circuit, GateKind, SRef, ShiftOp};
use std::collections::HashMap;

fn evaluate(circuit: &Circuit, reference: SRef, env: &HashMap<String, bool>) -> bool {
    let value = match circuit.kind(reference.gate) {
        GateKind::Atom(name) => env[name],
        GateKind::Const(value) => *value,
        GateKind::And(args) => args.iter().all(|&a| evaluate(circuit, a, env)),
        GateKind::Or(args) => args.iter().any(|&a| evaluate(circuit, a, env)),
        GateKind::Xor(a, b) => evaluate(circuit, *a, env) ^ evaluate(circuit, *b, env),
        GateKind::Implies(a, b) => !evaluate(circuit, *a, env) || evaluate(circuit, *b, env),
        GateKind::Iff(a, b) => evaluate(circuit, *a, env) == evaluate(circuit, *b, env),
        GateKind::Ite(c, a, b) => {
            if evaluate(circuit, *c, env) {
                evaluate(circuit, *a, env)
            } else {
                evaluate(circuit, *b, env)
            }
        }
        GateKind::Theory(body) => panic!("a shift circuit has no theory atom: {body}"),
    };
    value ^ reference.negative()
}

/// SMT-LIB's value of `op x y` at `width` bits.
fn reference(op: ShiftOp, x: u32, y: u32, width: u32) -> u32 {
    let mask = (1 << width) - 1;
    let negative = x >> (width - 1) & 1 == 1;
    match op {
        ShiftOp::Shl if y < width => (x << y) & mask,
        ShiftOp::LShr if y < width => x >> y,
        ShiftOp::AShr if y < width => {
            let fill = if negative { mask & !(mask >> y) } else { 0 };
            (x >> y) | fill
        }
        ShiftOp::Shl | ShiftOp::LShr => 0,
        ShiftOp::AShr if negative => mask,
        ShiftOp::AShr => 0,
    }
}

#[test]
fn every_printed_shift_circuit_computes_the_smt_lib_shift() {
    for width in [1_u32, 3, 4] {
        for op in [ShiftOp::Shl, ShiftOp::LShr, ShiftOp::AShr] {
            let mut circuit = Circuit::new("t".to_string());
            let xs: Vec<SRef> = (0..width).map(|i| circuit.atom(format!("x{i}"))).collect();
            let ys: Vec<SRef> = (0..width).map(|i| circuit.atom(format!("y{i}"))).collect();
            let size: Vec<SRef> = (0..width)
                .map(|i| circuit.constant(width >> i & 1 == 1))
                .collect();
            let bits = circuit
                .shift(op, &xs, &ys, &size)
                .expect("a narrow shift circuit builds");
            for x in 0..1_u32 << width {
                for y in 0..1_u32 << width {
                    let mut env = HashMap::new();
                    for i in 0..width {
                        env.insert(format!("x{i}"), x >> i & 1 == 1);
                        env.insert(format!("y{i}"), y >> i & 1 == 1);
                    }
                    let value = bits.iter().enumerate().fold(0, |value, (i, &bit)| {
                        value | u32::from(evaluate(&circuit, bit, &env)) << i
                    });
                    assert_eq!(
                        value,
                        reference(op, x, y, width),
                        "{op:?} at width {width}: x={x:#b} y={y:#b}"
                    );
                }
            }
        }
    }
}

/// The `bvashr` circuit of `width` bits over free `x` and `y`, in `dialect`.
fn ashr_circuit(width: u32, dialect: AletheDialect) -> (Circuit, Vec<SRef>) {
    let mut circuit = Circuit::new("t".to_string());
    let xs: Vec<SRef> = (0..width).map(|i| circuit.atom(format!("x{i}"))).collect();
    let ys: Vec<SRef> = (0..width).map(|i| circuit.atom(format!("y{i}"))).collect();
    let size: Vec<SRef> = (0..width)
        .map(|i| circuit.constant(width >> i & 1 == 1))
        .collect();
    let bits = with_alethe_dialect(dialect, || circuit.shift(ShiftOp::AShr, &xs, &ys, &size))
        .expect("a narrow shift circuit builds");
    (circuit, bits)
}

fn value_at(circuit: &Circuit, bits: &[SRef], x: u32, y: u32, width: u32) -> u32 {
    let mut env = HashMap::new();
    for i in 0..width {
        env.insert(format!("x{i}"), x >> i & 1 == 1);
        env.insert(format!("y{i}"), y >> i & 1 == 1);
    }
    bits.iter().enumerate().fold(0, |value, (i, &bit)| {
        value | u32::from(evaluate(circuit, bit, &env)) << i
    })
}

/// The pinned (zero-filled) `bvashr` circuit is SMT-LIB's `bvashr` on every
/// operand pair with a non-negative `x` or a `y` below the width: a superset
/// of every instance `arithmetic_shift_is_admissible` lets through.
#[test]
fn the_pinned_ashr_circuit_computes_bvashr_inside_the_admitted_domain() {
    for width in [1_u32, 3, 4] {
        let (circuit, bits) = ashr_circuit(width, AletheDialect::PinnedCarcara);
        for x in 0..1_u32 << width {
            for y in 0..1_u32 << width {
                let negative = x >> (width - 1) & 1 == 1;
                let expected = if negative && y >= width {
                    0 // the pinned zero fill; see the control below
                } else {
                    reference(ShiftOp::AShr, x, y, width)
                };
                let value = value_at(&circuit, &bits, x, y, width);
                assert_eq!(value, expected, "width {width}: x={x:#b} y={y:#b}");
            }
        }
    }
}

/// NEGATIVE CONTROL: outside that domain the pinned circuit is FALSE (a
/// negative operand shifted by the width evaluates to zero, not all ones), and
/// pinned Carcara would accept it. That is why the guard must gate every
/// `bitblast_ashr` AY prints. The default (Clean) circuit is exact there.
#[test]
fn the_pinned_ashr_circuit_is_false_outside_the_admitted_domain() {
    for width in [1_u32, 3, 4] {
        let x = 1_u32 << (width - 1);
        let (circuit, bits) = ashr_circuit(width, AletheDialect::PinnedCarcara);
        assert_eq!(
            value_at(&circuit, &bits, x, width, width),
            0,
            "width {width}"
        );
        assert_ne!(
            0,
            reference(ShiftOp::AShr, x, width, width),
            "width {width}"
        );
        let (circuit, bits) = ashr_circuit(width, AletheDialect::Clean);
        assert_eq!(
            value_at(&circuit, &bits, x, width, width),
            reference(ShiftOp::AShr, x, width, width),
            "width {width}: the default circuit is SMT-LIB's"
        );
    }
}
