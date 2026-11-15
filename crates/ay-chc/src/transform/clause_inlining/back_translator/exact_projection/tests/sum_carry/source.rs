// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-shaped checked/ordinary arithmetic fields before and after equality
//! lifting over an ITE. No source-specific field or predicate is recognized by
//! the implementation.

use super::*;

#[derive(Clone, Copy)]
enum Conditional {
    Value,
    Boolean,
}

fn formals(width: u32) -> Vec<ChcVar> {
    (0..24)
        .map(|index| match index {
            0 => ChcVar::new("valid", ChcSort::Bool),
            1 => var("checked", width),
            3 => var("sum", width),
            4 => ChcVar::new("carry", ChcSort::Bool),
            _ => ChcVar::new(
                format!("unused_{index}"),
                if [8, 10, 13, 17, 19, 22].contains(&index) {
                    ChcSort::Bool
                } else {
                    ChcSort::BitVec(width)
                },
            ),
        })
        .collect()
}

fn source(width: u32, conditional: Conditional) -> (ChcExpr, Vec<ChcVar>) {
    let keep = formals(width);
    let x = var("x", width);
    let y = var("y", width);
    let s = sum(&x, &y);
    let c = carry(&x, &y, CarryOperand::Left);
    let no_carry = op(ChcOp::Not, vec![c.clone()]);
    let zero = ChcExpr::BitVec(0, width);
    let checked = match conditional {
        Conditional::Value => eq(
            expr(&keep[1]),
            op(ChcOp::Ite, vec![no_carry.clone(), s.clone(), zero]),
        ),
        Conditional::Boolean => op(
            ChcOp::Ite,
            vec![
                no_carry.clone(),
                eq(expr(&keep[1]), s.clone()),
                eq(expr(&keep[1]), zero),
            ],
        ),
    };
    (
        op(
            ChcOp::And,
            vec![
                eq(expr(&keep[3]), s),
                eq(expr(&keep[4]), c),
                no_carry.clone(),
                eq(expr(&keep[0]), no_carry),
                checked,
                expr(&keep[0]),
            ],
        ),
        keep,
    )
}

#[test]
fn both_source_conditionals_preserve_exact_checked_result_correlation() {
    assert_eq!(source(8, Conditional::Value).0.node_count(1000), 41);
    assert_eq!(source(8, Conditional::Boolean).0.node_count(1000), 43);
    for width in 1..=3 {
        let size = 1u128 << width;
        for conditional in [Conditional::Value, Conditional::Boolean] {
            let (formula, keep) = source(width, conditional);
            assert_eq!(keep.len(), 24);
            let projected = closed(&formula, &keep);
            for sum in 0..size {
                for checked in 0..size {
                    for valid in 0..2 {
                        for carry in 0..2 {
                            let values = [
                                ("sum", sum),
                                ("checked", checked),
                                ("valid", valid),
                                ("carry", carry),
                            ];
                            let exists = (0..size).any(|x| {
                                (0..size).any(|y| {
                                    let mut values = values.to_vec();
                                    values.extend([("x", x), ("y", y)]);
                                    oracle::truth(&formula, &values)
                                })
                            });
                            assert_eq!(oracle::truth(&projected, &values), exists);
                            assert_eq!(exists, valid == 1 && carry == 0 && checked == sum);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn source_result_fields_cannot_take_distinct_values_after_projection() {
    for conditional in [Conditional::Value, Conditional::Boolean] {
        let (formula, keep) = source(8, conditional);
        let projected = closed(&formula, &keep);
        for checked in [127, 255] {
            assert_eq!(
                oracle::truth(
                    &projected,
                    &[
                        ("valid", 1),
                        ("carry", 0),
                        ("checked", checked),
                        ("sum", 255)
                    ],
                ),
                checked == 255
            );
        }
    }
}
