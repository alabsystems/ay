// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod negative;
mod parsed;
mod resources;

fn shift(x: &ChcVar, amount: u128) -> ChcExpr {
    let ChcSort::BitVec(width) = x.sort else {
        panic!("bitvector fixture")
    };
    op(ChcOp::BvLShr, vec![expr(x), ChcExpr::BitVec(amount, width)])
}

fn binding(width: u32, amount: u128) -> (ChcExpr, Vec<ChcVar>) {
    let local = var("local", width);
    let result = var("result", width);
    (eq(expr(&result), shift(&local, amount)), vec![result])
}

/// Independent finite witness calculation: repeated unsigned halving rather
/// than using the production upper-bound calculation or a host shift.
fn shifted_value(mut value: u128, amount: u128, width: u32) -> u128 {
    if amount >= u128::from(width) {
        return 0;
    }
    for _ in 0..amount {
        value /= 2;
    }
    value
}

pub(super) fn operation_count(expr: &ChcExpr, expected: ChcOp) -> usize {
    match expr {
        ChcExpr::Op(operation, args) => {
            usize::from(*operation == expected)
                + args
                    .iter()
                    .map(|arg| operation_count(arg, expected))
                    .sum::<usize>()
        }
        _ => 0,
    }
}

#[test]
fn every_small_width_shift_image_matches_complete_witness_enumeration() {
    for width in 1..=4 {
        let size = 1u128 << width;
        for amount in 0..size {
            let (formula, keep) = binding(width, amount);
            let projected = closed(&formula, &keep);
            for result in 0..size {
                let exists = (0..size).any(|x| shifted_value(x, amount, width) == result);
                assert_eq!(
                    oracle::truth(&projected, &[("result", result)]),
                    exists,
                    "width={width} amount={amount} result={result}"
                );
            }
        }
    }
}

#[test]
fn duplicate_aliases_and_both_equality_orientations_preserve_correlations() {
    let x = var("x", 4);
    let a = var("a", 4);
    let b = var("b", 4);
    let c = var("c", 4);
    for amount in [0, 1, 3, 4, 15] {
        let formula = op(
            ChcOp::And,
            vec![
                eq(expr(&a), shift(&x, amount)),
                eq(shift(&x, amount), expr(&b)),
                eq(
                    expr(&c),
                    op(ChcOp::BvAdd, vec![shift(&x, amount), expr(&a)]),
                ),
            ],
        );
        let projected = closed(&formula, &[a.clone(), b.clone(), c.clone()]);
        for a in 0..16 {
            for b in 0..16 {
                for c in 0..16 {
                    let exists = (0..16).any(|x| {
                        let value = shifted_value(x, amount, 4);
                        a == value && b == value && c == (value + a) % 16
                    });
                    assert_eq!(
                        oracle::truth(&projected, &[("a", a), ("b", b), ("c", c)]),
                        exists
                    );
                }
            }
        }
    }
}

#[test]
fn width_128_zero_last_bit_and_overshift_images_have_exact_boundaries() {
    for (amount, maximum) in [(0, u128::MAX), (127, 1), (128, 0), (u128::MAX, 0)] {
        let (formula, keep) = binding(128, amount);
        let projected = closed(&formula, &keep);
        for result in [0, 1, 2, 1u128 << 127, u128::MAX] {
            assert_eq!(
                oracle::truth(&projected, &[("result", result)]),
                result <= maximum,
                "amount={amount} result={result}"
            );
            if result <= maximum {
                let witness = match amount {
                    0 => result,
                    127 => result * (1u128 << 127),
                    _ => 0,
                };
                assert!(oracle::truth(
                    &formula,
                    &[("result", result), ("local", witness)]
                ));
            }
        }
    }
}

#[test]
fn directly_pinned_local_and_kept_operand_keep_their_original_restrictions() {
    let x = var("x", 4);
    let result = var("result", 4);
    let formula = eq(expr(&result), shift(&x, 1));
    let kept = closed(&formula, &[result.clone(), x.clone()]);
    let pinned = closed(
        &op(
            ChcOp::And,
            vec![formula.clone(), eq(expr(&x), ChcExpr::BitVec(10, 4))],
        ),
        &[result],
    );
    for result in 0..16 {
        assert_eq!(oracle::truth(&pinned, &[("result", result)]), result == 5);
        for x in 0..16 {
            assert_eq!(
                oracle::truth(&kept, &[("result", result), ("x", x)]),
                result == x / 2
            );
        }
    }
}
