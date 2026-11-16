// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The guard that decides where pinned Carcara's divider may be printed.
//!
//! REGRESSION (e9b297e37, measured 2026-09-30 on 938ec0327): every
//! `bitblast_udiv` / `bitblast_urem` step is spelled with Clean's fixed
//! divider, pinned Carcara 9a352ee refuses each one ("expected terms to be
//! equal"), and the certificate said `carcara_surface=supported`. Pinned
//! Carcara's own divider is no substitute: it is FALSE for most operands, and
//! pinned Carcara would accept those false steps. These tests pin the domain
//! where it is true, which is the only domain the pinned dialect prints it on.

use super::super::circuit::{Circuit, Divider, GateKind, SRef};
use super::super::ground::constant_values;
use super::{pinned_divider_is_true, smt_lib_udiv_urem};
use std::collections::HashMap;

/// The value of every gate under `inputs`, in creation (= dependency) order.
fn gate_values(circuit: &Circuit, inputs: &HashMap<String, bool>) -> Vec<bool> {
    let mut values: Vec<bool> = Vec::with_capacity(circuit.len());
    let read = |values: &[bool], r: &SRef| values[r.gate as usize] != r.negative();
    for gate in 0..circuit.len() as u32 {
        let value = match circuit.kind(gate) {
            GateKind::Atom(name) => inputs[name],
            GateKind::Const(value) => *value,
            GateKind::And(args) => args.iter().all(|arg| read(&values, arg)),
            GateKind::Or(args) => args.iter().any(|arg| read(&values, arg)),
            GateKind::Xor(a, b) => read(&values, a) != read(&values, b),
            GateKind::Implies(a, b) => !read(&values, a) || read(&values, b),
            GateKind::Iff(a, b) => read(&values, a) == read(&values, b),
            GateKind::Ite(c, a, b) => {
                if read(&values, c) {
                    read(&values, a)
                } else {
                    read(&values, b)
                }
            }
            GateKind::Theory(_) => unreachable!("no theory atoms in a divider"),
        };
        values.push(value);
    }
    values
}

fn word(values: &[bool], bits: &[SRef]) -> u32 {
    bits.iter().enumerate().fold(0, |acc, (index, bit)| {
        acc | u32::from(values[bit.gate as usize] != bit.negative()) << index
    })
}

fn little_endian(bits: &[bool]) -> u32 {
    bits.iter()
        .enumerate()
        .fold(0, |acc, (index, bit)| acc | u32::from(*bit) << index)
}

/// SMT-LIB's `bvudiv` and `bvurem`, zero divisor included.
fn reference(x: u32, y: u32, width: u32) -> (u32, u32) {
    match x.checked_div(y) {
        Some(quotient) => (quotient, x % y),
        None => ((1 << width) - 1, x),
    }
}

/// How a closed operand's bits are spelled.
#[derive(Clone, Copy, Debug)]
enum Spelling {
    /// Literal `true` / `false`, as a bit-vector literal blasts.
    Literal,
    /// `(or false true)` / `(and true false)`: closed, never the literal
    /// `false` the divider's syntactic base case looks for.
    Gated,
}

fn operand(circuit: &mut Circuit, value: u32, width: u32, spelling: Spelling) -> Vec<SRef> {
    let (t, f) = (circuit.constant(true), circuit.constant(false));
    (0..width)
        .map(
            |index| match (spelling, value.checked_shr(index).unwrap_or(0) & 1 == 1) {
                (Spelling::Literal, bit) => circuit.constant(bit),
                (Spelling::Gated, true) => circuit.or(vec![f, t]),
                (Spelling::Gated, false) => circuit.and(vec![t, f]),
            },
        )
        .collect()
}

#[test]
fn the_reference_is_smt_lib_division() {
    let bits = |value: u32| {
        (0..4)
            .map(|index| value >> index & 1 == 1)
            .collect::<Vec<_>>()
    };
    for x in 0..16 {
        for y in 0..16 {
            let (quot, rem) = smt_lib_udiv_urem(&bits(x), &bits(y));
            assert_eq!(
                (little_endian(&quot), little_endian(&rem)),
                reference(x, y, 4),
                "{x} / {y}"
            );
        }
    }
}

/// Over free operand bits, pinned Carcara's divider is SMT-LIB's division on
/// a zero divisor, and wrong for SOME dividend under every other divisor, so
/// no symbolic dividend is admitted past a non-zero divisor. Clean's divider,
/// built in the same circuit, is SMT-LIB's everywhere.
#[test]
fn the_pinned_divider_is_true_on_a_zero_divisor_and_false_under_every_other() {
    for width in 2..=5_u32 {
        let mut circuit = Circuit::new(String::new());
        let xs: Vec<SRef> = (0..width).map(|i| circuit.atom(format!("x{i}"))).collect();
        let ys: Vec<SRef> = (0..width).map(|i| circuit.atom(format!("y{i}"))).collect();
        let (pinned_quot, pinned_rem) = circuit
            .udiv_urem_spelled(&xs, &ys, Divider::Pinned)
            .expect("pinned divider");
        let (clean_quot, clean_rem) = circuit
            .udiv_urem_spelled(&xs, &ys, Divider::Clean)
            .expect("Clean divider");
        for y in 0..1_u32 << width {
            let mut divided_wrongly = false;
            for x in 0..1_u32 << width {
                let inputs: HashMap<String, bool> = (0..width)
                    .flat_map(|i| {
                        [
                            (format!("x{i}"), x >> i & 1 == 1),
                            (format!("y{i}"), y >> i & 1 == 1),
                        ]
                    })
                    .collect();
                let values = gate_values(&circuit, &inputs);
                let want = reference(x, y, width);
                let clean = (word(&values, &clean_quot), word(&values, &clean_rem));
                assert_eq!(clean, want, "Clean, width {width}: {x} / {y}");
                let pinned = (word(&values, &pinned_quot), word(&values, &pinned_rem));
                if y == 0 {
                    assert_eq!(pinned, want, "pinned, width {width}: {x} / 0");
                }
                divided_wrongly |= pinned != want;
            }
            assert_eq!(
                divided_wrongly,
                y != 0,
                "width {width}, divisor {y}: the pinned divider is wrong for some dividend \
                 exactly when the divisor is not zero"
            );
        }
    }
}

/// On closed operands the guard admits a step exactly when the pinned bits
/// PRINTED over those very operands are SMT-LIB's quotient or remainder, for
/// literal bits and for closed bits that are not the literal `false` (the
/// divider's syntactic base case sees those two differently). Both answers
/// occur, so the evaluation is load-bearing.
#[test]
fn on_closed_operands_the_guard_admits_exactly_the_true_pinned_steps() {
    for width in [3_u32, 4] {
        let (mut admitted, mut refused) = (0_u32, 0_u32);
        for x in 0..1_u32 << width {
            for y in 0..1_u32 << width {
                for remainder in [false, true] {
                    for spelling in [Spelling::Literal, Spelling::Gated] {
                        let mut circuit = Circuit::new(String::new());
                        let xs = operand(&mut circuit, x, width, spelling);
                        let ys = operand(&mut circuit, y, width, spelling);
                        let admits = pinned_divider_is_true(&circuit, &xs, &ys, remainder);
                        let (quot, rem) = circuit
                            .udiv_urem_spelled(&xs, &ys, Divider::Pinned)
                            .expect("pinned divider");
                        let printed =
                            constant_values(&circuit, if remainder { &rem } else { &quot })
                                .expect("a closed divider evaluates");
                        let (want_quot, want_rem) = reference(x, y, width);
                        let want = if remainder { want_rem } else { want_quot };
                        assert_eq!(
                            admits,
                            little_endian(&printed) == want,
                            "width {width} {spelling:?}: {x} {} {y}",
                            if remainder { "rem" } else { "div" }
                        );
                        if admits {
                            admitted += 1;
                        } else {
                            refused += 1;
                        }
                    }
                }
            }
        }
        assert!(
            admitted > 0 && refused > 0,
            "{admitted} admitted, {refused} refused"
        );
    }
}

/// The measured probes: `(bvudiv #x80 #x02)` and `(bvurem 192 128)` at 64
/// bits are divided wrongly by pinned Carcara's circuit and refused; a zero
/// divisor is admitted, over a free dividend too; a free dividend under a
/// non-zero divisor is refused.
#[test]
fn the_guard_on_the_measured_probes_and_on_free_operands() {
    let closed = |x: u32, y: u32, width: u32, remainder: bool| {
        let mut circuit = Circuit::new(String::new());
        let xs = operand(&mut circuit, x, width, Spelling::Literal);
        let ys = operand(&mut circuit, y, width, Spelling::Literal);
        pinned_divider_is_true(&circuit, &xs, &ys, remainder)
    };
    assert!(
        !closed(128, 2, 8, false),
        "pinned divides #x80 by #x02 as #x00"
    );
    assert!(!closed(128, 2, 8, true));
    assert!(
        !closed(192, 128, 64, true),
        "pinned leaves an all-ones remainder"
    );
    assert!(closed(64, 0, 8, true) && closed(64, 0, 8, false));
    assert!(closed(7, 2, 4, false), "pinned divides 7 by 2 correctly");
    assert!(!closed(7, 2, 4, true), "but leaves an all-ones remainder");

    let mut circuit = Circuit::new(String::new());
    let free: Vec<SRef> = (0..8).map(|i| circuit.atom(format!("x{i}"))).collect();
    for spelling in [Spelling::Literal, Spelling::Gated] {
        let zero = operand(&mut circuit, 0, 8, spelling);
        let three = operand(&mut circuit, 3, 8, spelling);
        for remainder in [false, true] {
            assert!(pinned_divider_is_true(&circuit, &free, &zero, remainder));
            assert!(!pinned_divider_is_true(&circuit, &free, &three, remainder));
            assert!(!pinned_divider_is_true(&circuit, &zero, &free, remainder));
        }
    }
}
