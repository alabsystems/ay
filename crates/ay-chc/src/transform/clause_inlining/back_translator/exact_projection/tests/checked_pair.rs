// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod negatives;
mod resources;
mod source;

#[derive(Clone, Copy, Debug)]
enum Arithmetic {
    Difference,
    Product,
}

#[derive(Clone, Copy, Debug)]
enum Polarity {
    Direct,
    Complement,
}

#[derive(Clone, Copy)]
enum Orientation {
    Forward,
    Reverse,
}

fn low(arithmetic: Arithmetic, x: &ChcVar, y: &ChcVar) -> ChcExpr {
    let operation = match arithmetic {
        Arithmetic::Difference => ChcOp::BvSub,
        Arithmetic::Product => ChcOp::BvMul,
    };
    op(operation, vec![expr(x), expr(y)])
}

fn wide(x: &ChcVar, y: &ChcVar, width: u32) -> ChcExpr {
    op(
        ChcOp::BvMul,
        vec![
            op(ChcOp::BvZeroExtend(width), vec![expr(x)]),
            op(ChcOp::BvZeroExtend(width), vec![expr(y)]),
        ],
    )
}

fn high(x: &ChcVar, y: &ChcVar, width: u32) -> ChcExpr {
    op(
        ChcOp::BvExtract(2 * width - 1, width),
        vec![wide(x, y, width)],
    )
}

fn observation(arithmetic: Arithmetic, x: &ChcVar, y: &ChcVar, width: u32) -> ChcExpr {
    match arithmetic {
        Arithmetic::Difference => op(ChcOp::BvULt, vec![expr(x), expr(y)]),
        Arithmetic::Product => eq(high(x, y, width), ChcExpr::BitVec(0, width)),
    }
}

fn polarized(observation: ChcExpr, polarity: Polarity) -> ChcExpr {
    match polarity {
        Polarity::Direct => observation,
        Polarity::Complement => op(ChcOp::Not, vec![observation]),
    }
}

fn oriented_eq(lhs: ChcExpr, rhs: ChcExpr, orientation: Orientation) -> ChcExpr {
    match orientation {
        Orientation::Forward => eq(lhs, rhs),
        Orientation::Reverse => eq(rhs, lhs),
    }
}

fn fixture(
    arithmetic: Arithmetic,
    width: u32,
    polarity: Polarity,
    orientation: Orientation,
) -> (ChcExpr, Vec<ChcVar>) {
    let x = var("x", width);
    let y = var("y", width);
    let result = var("result", width);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let observation = polarized(observation(arithmetic, &x, &y, width), polarity);
    (
        op(
            ChcOp::And,
            vec![
                oriented_eq(expr(&result), low(arithmetic, &x, &y), orientation),
                oriented_eq(expr(&flag), observation, orientation),
            ],
        ),
        vec![result, flag],
    )
}

#[test]
fn both_joint_images_match_exhaustive_small_width_operands_and_binding_polarities() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        for width in 1..=4 {
            let size = 1u128 << width;
            for polarity in [Polarity::Direct, Polarity::Complement] {
                for orientation in [Orientation::Forward, Orientation::Reverse] {
                    let (formula, keep) = fixture(arithmetic, width, polarity, orientation);
                    let projected = closed(&formula, &keep);
                    for result in 0..size {
                        for flag in 0..2 {
                            let exists = (0..size).any(|x| {
                                (0..size).any(|y| {
                                    oracle::truth(
                                        &formula,
                                        &[("x", x), ("y", y), ("result", result), ("flag", flag)],
                                    )
                                })
                            });
                            assert_eq!(
                                oracle::truth(&projected, &[("result", result), ("flag", flag)]),
                                exists,
                                "{arithmetic:?} width={width}, {polarity:?}, result={result}, flag={flag}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn repeated_result_and_complement_observation_aliases_remain_correlated() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        let (binding, mut keep) =
            fixture(arithmetic, 2, Polarity::Complement, Orientation::Reverse);
        let x = var("x", 2);
        let y = var("y", 2);
        let result2 = var("result2", 2);
        let flag2 = ChcVar::new("flag2", ChcSort::Bool);
        let formula = op(
            ChcOp::And,
            vec![
                binding,
                eq(low(arithmetic, &x, &y), expr(&result2)),
                eq(observation(arithmetic, &x, &y, 2), expr(&flag2)),
            ],
        );
        keep.extend([result2, flag2]);
        let projected = closed(&formula, &keep);
        for result in 0..4 {
            for result2 in 0..4 {
                for flag in 0..2 {
                    for flag2 in 0..2 {
                        let values = [
                            ("result", result),
                            ("result2", result2),
                            ("flag", flag),
                            ("flag2", flag2),
                        ];
                        let exists = (0..4).any(|x| {
                            (0..4).any(|y| {
                                let mut values = values.to_vec();
                                values.extend([("x", x), ("y", y)]);
                                oracle::truth(&formula, &values)
                            })
                        });
                        assert_eq!(oracle::truth(&projected, &values), exists);
                    }
                }
            }
        }
    }
}

#[test]
fn reversed_high_zero_equality_has_the_same_product_observation() {
    let x = var("x", 3);
    let y = var("y", 3);
    let result = var("result", 3);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let formula = op(
        ChcOp::And,
        vec![
            eq(expr(&result), low(Arithmetic::Product, &x, &y)),
            eq(expr(&flag), eq(ChcExpr::BitVec(0, 3), high(&x, &y, 3))),
        ],
    );
    let projected = closed(&formula, &[result, flag]);
    for result in 0..8 {
        for flag in 0..2 {
            assert!(oracle::truth(
                &projected,
                &[("result", result), ("flag", flag)]
            ));
        }
    }
}

#[test]
fn maximum_admitted_operand_widths_preserve_exact_images_and_witnesses() {
    let (difference, keep) = fixture(
        Arithmetic::Difference,
        128,
        Polarity::Direct,
        Orientation::Forward,
    );
    let projected = closed(&difference, &keep);
    for result in [0, 1, u128::MAX - 1, u128::MAX] {
        for borrow in 0..2 {
            assert_eq!(
                oracle::truth(&projected, &[("result", result), ("flag", borrow)]),
                borrow == 0 || result != 0
            );
            if borrow == 0 || result != 0 {
                let (x, y) = if borrow == 0 {
                    (result, 0)
                } else {
                    (0, 0u128.wrapping_sub(result))
                };
                assert!(oracle::truth(
                    &difference,
                    &[("x", x), ("y", y), ("result", result), ("flag", borrow)]
                ));
            }
        }
    }
    let (product, keep) = fixture(
        Arithmetic::Product,
        64,
        Polarity::Complement,
        Orientation::Forward,
    );
    let projected = closed(&product, &keep);
    let size = 1u128 << 64;
    for result in [0, 1, size - 2, size - 1] {
        for overflow in 0..2 {
            let (x, y) = match (overflow, result) {
                (0, _) => (result, 1),
                (_, 0) => (size / 2, 2),
                (_, value) if value == size - 1 => (size / 2 - 1, size / 2 + 1),
                _ => (size - 1, size - result),
            };
            let values = [("result", result), ("flag", overflow)];
            assert!(oracle::truth(&projected, &values));
            assert!(oracle::truth(
                &product,
                &[("x", x), ("y", y), values[0], values[1]]
            ));
        }
    }
    let (too_wide, keep) = fixture(
        Arithmetic::Product,
        65,
        Polarity::Direct,
        Orientation::Forward,
    );
    declined(&too_wide, &keep);
}
