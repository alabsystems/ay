// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod negative;
mod resources;
mod sharing;

#[derive(Clone, Copy, Debug)]
enum Form {
    AddLeft,
    AddRight,
    SubLeft,
    SubRight,
}

const FORMS: [Form; 4] = [Form::AddLeft, Form::AddRight, Form::SubLeft, Form::SubRight];

#[derive(Clone, Copy, Debug)]
enum Orientation {
    Forward,
    Reverse,
}

const ORIENTATIONS: [Orientation; 2] = [Orientation::Forward, Orientation::Reverse];

fn arithmetic(form: Form, local: ChcExpr, other: ChcExpr) -> ChcExpr {
    match form {
        Form::AddLeft => op(ChcOp::BvAdd, vec![local, other]),
        Form::AddRight => op(ChcOp::BvAdd, vec![other, local]),
        Form::SubLeft => op(ChcOp::BvSub, vec![local, other]),
        Form::SubRight => op(ChcOp::BvSub, vec![other, local]),
    }
}

fn oriented(lhs: ChcExpr, rhs: ChcExpr, orientation: Orientation) -> ChcExpr {
    match orientation {
        Orientation::Forward => eq(lhs, rhs),
        Orientation::Reverse => eq(rhs, lhs),
    }
}

fn fixture(width: u32, form: Form, orientation: Orientation) -> (ChcExpr, Vec<ChcVar>) {
    let x = var("x", width);
    let result = var("result", width);
    let other = var("other", width);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let side = op(
        ChcOp::Ite,
        vec![
            op(ChcOp::BvULt, vec![expr(&x), expr(&other)]),
            eq(op(ChcOp::BvMul, vec![expr(&x), expr(&x)]), expr(&result)),
            eq(op(ChcOp::BvSub, vec![expr(&x), expr(&other)]), expr(&other)),
        ],
    );
    let formula = op(
        ChcOp::And,
        vec![
            oriented(
                expr(&result),
                arithmetic(form, expr(&x), expr(&other)),
                orientation,
            ),
            eq(expr(&flag), side),
        ],
    );
    (formula, vec![result, other, flag])
}

#[test]
fn every_inverse_orientation_preserves_exhaustive_side_constraints() {
    for width in 1..=4 {
        let size = 1u128 << width;
        for form in FORMS {
            for orientation in ORIENTATIONS {
                let (formula, keep) = fixture(width, form, orientation);
                let projected = closed(&formula, &keep);
                for result in 0..size {
                    for other in 0..size {
                        for flag in 0..2 {
                            let values = [("result", result), ("other", other), ("flag", flag)];
                            let exists = (0..size).any(|x| {
                                oracle::truth(
                                    &formula,
                                    &[values[0], values[1], values[2], ("x", x)],
                                )
                            });
                            assert_eq!(
                                oracle::truth(&projected, &values),
                                exists,
                                "w={width} {form:?} {orientation:?} {values:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn free_other_locals_do_not_survive_only_in_discharged_tautologies() {
    for width in 1..=4 {
        let size = 1u128 << width;
        let x = var("x", width);
        let y = var("y", width);
        let result = var("result", width);
        for form in FORMS {
            for target in [
                expr(&result),
                op(ChcOp::BvAdd, vec![expr(&result), expr(&y)]),
            ] {
                let formula = eq(target, arithmetic(form, expr(&x), expr(&y)));
                let projected = closed(&formula, std::slice::from_ref(&result));
                for result in 0..size {
                    let exists = (0..size).any(|x| {
                        (0..size).any(|y| {
                            oracle::truth(&formula, &[("result", result), ("x", x), ("y", y)])
                        })
                    });
                    assert!(exists);
                    assert_eq!(oracle::truth(&projected, &[("result", result)]), exists);
                }
            }
        }
    }
}

#[test]
fn inverse_rhs_may_retain_another_local_until_its_own_binding_is_processed() {
    for width in 1..=4 {
        let size = 1u128 << width;
        let x = var("x", width);
        let y = var("y", width);
        let r = var("r", width);
        let s = var("s", width);
        let flag = ChcVar::new("flag", ChcSort::Bool);
        let formula = op(
            ChcOp::And,
            vec![
                eq(expr(&flag), op(ChcOp::BvULt, vec![expr(&x), expr(&y)])),
                eq(
                    expr(&s),
                    op(ChcOp::BvAdd, vec![expr(&y), ChcExpr::BitVec(1, width)]),
                ),
                eq(expr(&r), op(ChcOp::BvAdd, vec![expr(&x), expr(&y)])),
            ],
        );
        let projected = closed(&formula, &[r, s, flag]);
        for r in 0..size {
            for s in 0..size {
                for flag in 0..2 {
                    let exists = (0..size).any(|x| {
                        (0..size).any(|y| {
                            oracle::truth(
                                &formula,
                                &[("r", r), ("s", s), ("flag", flag), ("x", x), ("y", y)],
                            )
                        })
                    });
                    assert_eq!(
                        oracle::truth(&projected, &[("r", r), ("s", s), ("flag", flag)]),
                        exists
                    );
                }
            }
        }
    }
}

#[test]
fn width_128_wraparound_keeps_the_unique_witness_and_every_observation() {
    for form in FORMS {
        for orientation in ORIENTATIONS {
            let (formula, keep) = fixture(128, form, orientation);
            let projected = closed(&formula, &keep);
            for x in [0u128, 1, 1 << 127, u128::MAX - 1, u128::MAX] {
                for other in [0u128, 1, 1 << 127, u128::MAX] {
                    let result = match form {
                        Form::AddLeft | Form::AddRight => x.wrapping_add(other),
                        Form::SubLeft => x.wrapping_sub(other),
                        Form::SubRight => other.wrapping_sub(x),
                    };
                    for flag in 0..2 {
                        let values = [("result", result), ("other", other), ("flag", flag)];
                        assert_eq!(
                            oracle::truth(&projected, &values),
                            oracle::truth(&formula, &[values[0], values[1], values[2], ("x", x),])
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn more_than_eight_independent_inverse_bindings_use_structural_progress() {
    let locals: Vec<_> = (0..12).map(|i| var(&format!("x{i}"), 4)).collect();
    let keep: Vec<_> = (0..12).map(|i| var(&format!("r{i}"), 4)).collect();
    let formula = op(
        ChcOp::And,
        locals
            .iter()
            .zip(&keep)
            .map(|(x, r)| {
                eq(
                    expr(r),
                    op(ChcOp::BvSub, vec![ChcExpr::BitVec(15, 4), expr(x)]),
                )
            })
            .collect(),
    );
    let projected = closed(&formula, &keep);
    assert_eq!(projected, ChcExpr::Bool(true));
}
