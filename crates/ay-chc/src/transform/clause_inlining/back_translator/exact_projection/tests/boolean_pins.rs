// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn pinned_choice(value: bool) -> (ChcExpr, ChcVar) {
    let local = ChcVar::new("local", ChcSort::Bool);
    let output = var("output", 2);
    let pin = if value {
        expr(&local)
    } else {
        op(ChcOp::Not, vec![expr(&local)])
    };
    let choice = op(
        ChcOp::Ite,
        vec![expr(&local), ChcExpr::BitVec(1, 2), ChcExpr::BitVec(2, 2)],
    );
    (op(ChcOp::And, vec![pin, eq(expr(&output), choice)]), output)
}

#[test]
fn asserted_boolean_locals_close_with_exact_positive_and_negative_images() {
    for value in [false, true] {
        let (formula, output) = pinned_choice(value);
        let projected = closed(&formula, &[output]);
        for candidate in 0..4 {
            assert_eq!(
                oracle::truth(&projected, &[("output", candidate)]),
                candidate == if value { 1 } else { 2 }
            );
        }
    }
}

#[test]
fn a_single_boolean_pin_has_an_existential_witness_in_both_polarities() {
    let local = ChcVar::new("local", ChcSort::Bool);
    for formula in [expr(&local), op(ChcOp::Not, vec![expr(&local)])] {
        assert!(oracle::truth(&closed(&formula, &[]), &[]));
    }
}

#[test]
fn contradictory_boolean_pins_have_no_witness_and_retained_flags_stay_constrained() {
    let local = ChcVar::new("local", ChcSort::Bool);
    let contradiction = op(
        ChcOp::And,
        vec![expr(&local), op(ChcOp::Not, vec![expr(&local)])],
    );
    assert!(!oracle::truth(&closed(&contradiction, &[]), &[]));
    for value in [false, true] {
        let (formula, output) = pinned_choice(value);
        let projected = closed(&formula, &[output, local.clone()]);
        for candidate in 0..4 {
            for flag in 0..2 {
                assert_eq!(
                    oracle::truth(&projected, &[("output", candidate), ("local", flag)]),
                    (flag == u128::from(value)) && candidate == if value { 1 } else { 2 }
                );
            }
        }
    }
}

#[test]
fn boolean_pins_do_not_hide_invalid_source_types() {
    let local = var("local", 2);
    for bad in [expr(&local), op(ChcOp::Not, vec![expr(&local)])] {
        declined(&bad, &[]);
    }
}

#[test]
fn boolean_pin_substitution_retains_every_resource_boundary() {
    let (formula, output) = pinned_choice(true);
    resources::assert_poll_boundaries(&formula, std::slice::from_ref(&output));
    resources::assert_numeric_boundaries(&formula, &[output]);
}
