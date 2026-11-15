// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod negative;
mod resources;

fn observation(local: &ChcVar, operation: ChcOp, constant: u128) -> ChcExpr {
    let ChcSort::BitVec(width) = local.sort else {
        panic!("bitvector fixture")
    };
    op(
        operation,
        vec![expr(local), ChcExpr::BitVec(constant, width)],
    )
}

fn image_value(mut value: u128, operation: ChcOp, constant: u128, width: u32) -> u128 {
    match operation {
        ChcOp::BvUDiv => value / constant,
        ChcOp::BvLShr => {
            if constant >= u128::from(width) {
                return 0;
            }
            for _ in 0..constant {
                value /= 2;
            }
            value
        }
        _ => unreachable!(),
    }
}

#[test]
fn constant_zero_shift_observation_needs_no_retained_variable() {
    let local = var("local", 32);
    let formula = eq(
        ChcExpr::BitVec(0, 32),
        observation(&local, ChcOp::BvLShr, 1),
    );
    assert_eq!(formula.vars(), vec![local.clone()]);
    let projected = closed(&formula, &[]);
    assert!(projected.vars().is_empty());
    assert!(oracle::truth(&projected, &[]));
    // The same operand must not become existential when the caller retains it.
    let retained = closed(&formula, &[local]);
    for value in [0, 1, 2, u128::from(u32::MAX)] {
        assert_eq!(oracle::truth(&retained, &[("local", value)]), value < 2);
    }
}

#[test]
fn every_small_width_constant_target_matches_complete_image_including_false() {
    for width in 1..=4 {
        let size = 1u128 << width;
        let local = var("local", width);
        for operation in [ChcOp::BvUDiv, ChcOp::BvLShr] {
            for constant in u128::from(operation == ChcOp::BvUDiv)..size {
                for target in 0..size {
                    let value = ChcExpr::BitVec(target, width);
                    let observed = observation(&local, operation, constant);
                    for formula in [eq(value.clone(), observed.clone()), eq(observed, value)] {
                        let projected = closed(&formula, &[]);
                        let exists =
                            (0..size).any(|x| image_value(x, operation, constant, width) == target);
                        assert_eq!(
                            oracle::truth(&projected, &[]),
                            exists,
                            "w={width} op={operation:?} k={constant} target={target}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn arbitrary_retained_arithmetic_targets_preserve_every_shared_use() {
    for width in 1..=4 {
        let size = 1u128 << width;
        let local = var("local", width);
        let a = var("a", width);
        let b = var("b", width);
        let c = var("c", width);
        for (operation, constant) in [
            (ChcOp::BvUDiv, 1),
            (ChcOp::BvUDiv, size - 1),
            (ChcOp::BvLShr, 0),
            (ChcOp::BvLShr, 1),
        ] {
            for arithmetic in [ChcOp::BvAdd, ChcOp::BvSub] {
                let target = op(arithmetic, vec![expr(&a), expr(&b)]);
                let observed = observation(&local, operation, constant);
                let formula = op(
                    ChcOp::And,
                    vec![
                        eq(target, observed.clone()),
                        eq(expr(&c), op(ChcOp::BvAdd, vec![observed, expr(&a)])),
                    ],
                );
                let projected = closed(&formula, &[a.clone(), b.clone(), c.clone()]);
                for a in 0..size {
                    for b in 0..size {
                        for c in 0..size {
                            let target = if arithmetic == ChcOp::BvAdd {
                                (a + b) % size
                            } else {
                                (a + size - b) % size
                            };
                            let exists = (0..size).any(|x| {
                                let observed = image_value(x, operation, constant, width);
                                observed == target && c == (observed + a) % size
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
    }
}

#[test]
fn retained_conditional_target_and_aliases_keep_correlations() {
    let local = var("local", 3);
    let a = var("a", 3);
    let b = var("b", 3);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let alias = var("alias", 3);
    for operation in [ChcOp::BvUDiv, ChcOp::BvLShr] {
        let observed = observation(&local, operation, 2);
        let target = op(ChcOp::Ite, vec![expr(&flag), expr(&a), expr(&b)]);
        let conditional = closed(
            &eq(observed.clone(), target.clone()),
            &[a.clone(), b.clone(), flag.clone()],
        );
        let formula = op(
            ChcOp::And,
            vec![
                eq(observed.clone(), target),
                eq(expr(&alias), observed.clone()),
                eq(observed, expr(&alias)),
            ],
        );
        let projected = closed(
            &formula,
            &[a.clone(), b.clone(), flag.clone(), alias.clone()],
        );
        for a in 0..8 {
            for b in 0..8 {
                for flag in 0..2 {
                    for alias in 0..8 {
                        let target = if flag == 1 { a } else { b };
                        let exists = (0..8)
                            .any(|x| image_value(x, operation, 2, 3) == target && alias == target);
                        let image_exists =
                            (0..8).any(|x| image_value(x, operation, 2, 3) == target);
                        assert_eq!(
                            oracle::truth(&conditional, &[("a", a), ("b", b), ("flag", flag)]),
                            image_exists
                        );
                        assert_eq!(
                            oracle::truth(
                                &projected,
                                &[("a", a), ("b", b), ("flag", flag), ("alias", alias)]
                            ),
                            exists
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn constant_width_128_targets_observe_division_and_overshift_boundaries() {
    let local = var("local", 128);
    for (operation, constant, maximum) in [
        (ChcOp::BvUDiv, 1, u128::MAX),
        (ChcOp::BvUDiv, u128::MAX, 1),
        (ChcOp::BvLShr, 0, u128::MAX),
        (ChcOp::BvLShr, 127, 1),
        (ChcOp::BvLShr, 128, 0),
        (ChcOp::BvLShr, u128::MAX, 0),
    ] {
        for target in [0, 1, 2, u128::MAX] {
            let formula = eq(
                ChcExpr::BitVec(target, 128),
                observation(&local, operation, constant),
            );
            assert_eq!(
                oracle::truth(&closed(&formula, &[]), &[]),
                target <= maximum
            );
        }
    }
}
