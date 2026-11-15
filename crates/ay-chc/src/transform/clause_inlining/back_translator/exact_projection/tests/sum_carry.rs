// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod resources;
mod source;

#[derive(Clone, Copy)]
enum CarryOperand {
    Left,
    Right,
}

fn sum(x: &ChcVar, y: &ChcVar) -> ChcExpr {
    op(ChcOp::BvAdd, vec![expr(x), expr(y)])
}

fn carry(x: &ChcVar, y: &ChcVar, operand: CarryOperand) -> ChcExpr {
    let operand = match operand {
        CarryOperand::Left => x,
        CarryOperand::Right => y,
    };
    op(ChcOp::BvULt, vec![sum(x, y), expr(operand)])
}

fn fixture(width: u32, operand: CarryOperand) -> (ChcExpr, Vec<ChcVar>) {
    let x = var("x", width);
    let y = var("y", width);
    let r = var("sum", width);
    let f = ChcVar::new("carry", ChcSort::Bool);
    (
        op(
            ChcOp::And,
            vec![
                eq(expr(&r), sum(&x, &y)),
                eq(expr(&f), carry(&x, &y, operand)),
            ],
        ),
        vec![r, f],
    )
}

fn assert_closed_matches_existential_operands(formula: &ChcExpr, keep: &[ChcVar]) {
    let projected = closed(formula, keep);
    for sum in 0..16 {
        for carry in 0..2 {
            let exists = (0..16).any(|x| {
                (0..16).any(|y| {
                    oracle::truth(
                        formula,
                        &[("x", x), ("y", y), ("sum", sum), ("carry", carry)],
                    )
                })
            });
            assert_eq!(
                oracle::truth(&projected, &[("sum", sum), ("carry", carry)]),
                exists,
                "sum={sum}, carry={carry}"
            );
        }
    }
}

#[test]
fn complete_joint_image_matches_every_small_width_operand_pair() {
    for width in 1..=4 {
        let size = 1u128 << width;
        for operand in [CarryOperand::Left, CarryOperand::Right] {
            let (formula, keep) = fixture(width, operand);
            let projected = closed(&formula, &keep);
            for sum in 0..size {
                for carry in 0..2 {
                    let exists = (0..size).any(|x| {
                        (0..size).any(|y| {
                            oracle::truth(
                                &formula,
                                &[("x", x), ("y", y), ("sum", sum), ("carry", carry)],
                            )
                        })
                    });
                    assert_eq!(
                        oracle::truth(&projected, &[("sum", sum), ("carry", carry)]),
                        exists,
                        "width={width}, sum={sum}, carry={carry}"
                    );
                }
            }
            assert!(!oracle::truth(
                &projected,
                &[("sum", size - 1), ("carry", 1)]
            ));
        }
    }
}

#[test]
fn repeated_sum_and_symmetric_carry_observations_remain_correlated() {
    let (binding, mut keep) = fixture(2, CarryOperand::Left);
    let x = var("x", 2);
    let y = var("y", 2);
    let r2 = var("sum2", 2);
    let f2 = ChcVar::new("carry2", ChcSort::Bool);
    let formula = op(
        ChcOp::And,
        vec![
            binding,
            eq(sum(&x, &y), expr(&r2)),
            eq(carry(&x, &y, CarryOperand::Right), expr(&f2)),
        ],
    );
    keep.extend([r2, f2]);
    let projected = closed(&formula, &keep);
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..2 {
                for d in 0..2 {
                    assert_eq!(
                        oracle::truth(
                            &projected,
                            &[("sum", a), ("sum2", b), ("carry", c), ("carry2", d)]
                        ),
                        a == b && c == d && (c == 0 || a != 3)
                    );
                }
            }
        }
    }
}

#[test]
fn alias_raw_operand_and_additional_constraints_prevent_image_elimination() {
    let (binding, keep) = fixture(4, CarryOperand::Left);
    let x = var("x", 4);
    let y = var("y", 4);
    for extra in [
        op(ChcOp::BvULt, vec![expr(&x), ChcExpr::BitVec(3, 4)]),
        op(ChcOp::BvULt, vec![expr(&y), ChcExpr::BitVec(3, 4)]),
        eq(expr(&x), expr(&y)),
    ] {
        declined(&op(ChcOp::And, vec![binding.clone(), extra]), &keep);
    }
    assert_closed_matches_existential_operands(
        &op(
            ChcOp::And,
            vec![binding.clone(), eq(expr(&x), ChcExpr::BitVec(1, 4))],
        ),
        &keep,
    );
    let aliased = op(
        ChcOp::And,
        vec![
            eq(expr(&keep[0]), sum(&x, &x)),
            eq(expr(&keep[1]), carry(&x, &x, CarryOperand::Left)),
        ],
    );
    declined(&aliased, &keep);
    let mut one_kept_operand = keep;
    one_kept_operand.push(x);
    let projected = closed(&binding, &one_kept_operand);
    for sum in 0..16 {
        for carry in 0..2 {
            for x in 0..16 {
                let exists = (0..16).any(|y| {
                    oracle::truth(
                        &binding,
                        &[("x", x), ("y", y), ("sum", sum), ("carry", carry)],
                    )
                });
                assert_eq!(
                    oracle::truth(&projected, &[("x", x), ("sum", sum), ("carry", carry)]),
                    exists,
                    "sum={sum}, carry={carry}, x={x}"
                );
            }
        }
    }
}

#[test]
fn mismatched_observations_missing_bindings_and_partial_branches_decline() {
    let (binding, keep) = fixture(4, CarryOperand::Left);
    let x = var("x", 4);
    let y = var("y", 4);
    let z = var("z", 4);
    for bad_carry in [
        op(ChcOp::BvSLt, vec![sum(&x, &y), expr(&x)]),
        op(ChcOp::BvULe, vec![sum(&x, &y), expr(&x)]),
        op(ChcOp::BvULt, vec![expr(&x), sum(&x, &y)]),
        op(ChcOp::BvULt, vec![sum(&x, &z), expr(&x)]),
        op(ChcOp::BvULt, vec![sum(&x, &y), expr(&z)]),
    ] {
        declined(
            &op(
                ChcOp::And,
                vec![
                    eq(expr(&keep[0]), sum(&x, &y)),
                    eq(expr(&keep[1]), bad_carry),
                ],
            ),
            &keep,
        );
    }
    assert_closed_matches_existential_operands(&eq(expr(&keep[0]), sum(&x, &y)), &keep);
    declined(
        &eq(expr(&keep[1]), carry(&x, &y, CarryOperand::Left)),
        &keep,
    );
    let extra = eq(expr(&keep[0]), sum(&y, &x));
    // This implementation deliberately requires identical sum syntax.
    declined(&op(ChcOp::And, vec![binding.clone(), extra]), &keep);
    let unsupported = op(ChcOp::BvULt, vec![expr(&x), expr(&keep[0])]);
    declined(&op(ChcOp::Or, vec![binding, unsupported]), &keep);
}

#[test]
fn typed_sum_carry_admission_rejects_malformed_widths_sorts_and_arities() {
    let (binding, keep) = fixture(4, CarryOperand::Left);
    let x = var("x", 4);
    for bad_sum in [
        sum(&x, &var("y", 3)),
        op(ChcOp::BvAdd, vec![expr(&x), ChcExpr::Bool(false)]),
        op(ChcOp::BvAdd, vec![expr(&x)]),
    ] {
        declined(
            &op(
                ChcOp::And,
                vec![binding.clone(), eq(expr(&keep[0]), bad_sum)],
            ),
            &keep,
        );
    }
    declined(
        &op(
            ChcOp::And,
            vec![binding, eq(expr(&keep[1]), ChcExpr::BitVec(0, 4))],
        ),
        &keep,
    );
}

#[test]
fn full_u128_sum_carry_boundary_does_not_overflow_host_arithmetic() {
    let (formula, keep) = fixture(128, CarryOperand::Right);
    let projected = closed(&formula, &keep);
    for sum in [0, 1, u128::MAX - 1, u128::MAX] {
        for carry in 0..2 {
            assert_eq!(
                oracle::truth(&projected, &[("sum", sum), ("carry", carry)]),
                carry == 0 || sum != u128::MAX
            );
        }
    }
}
