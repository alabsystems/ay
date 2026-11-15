// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]
#![allow(clippy::unwrap_used)]

mod boundaries;
mod source;

use super::*;
use crate::expr::evaluate_expr;
use crate::smt::SmtValue;
use crate::ChcVar;
use ay_core::kani_compat::DetHashMap as Map;

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn array_sort(width: u32) -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(width)), Box::new(ChcSort::Bool))
}

fn read(name: &str, width: u32) -> ChcExpr {
    op(
        ChcOp::Select,
        vec![
            var(name, array_sort(width)),
            var("i", ChcSort::BitVec(width)),
        ],
    )
}

fn compare(operator: ChcOp, value: u128, width: u32) -> ChcExpr {
    op(
        operator,
        vec![
            var("i", ChcSort::BitVec(width)),
            ChcExpr::BitVec(value, width),
        ],
    )
}

fn resize(old: u128, new: u128, width: u32, fill: bool) -> ChcExpr {
    let prefix = op(
        ChcOp::Implies,
        vec![
            compare(ChcOp::BvULt, old, width),
            op(ChcOp::Eq, vec![read("a", width), read("b", width)]),
        ],
    );
    if !fill {
        return prefix;
    }
    let suffix = op(
        ChcOp::Implies,
        vec![
            op(
                ChcOp::And,
                vec![
                    compare(ChcOp::BvUGe, old, width),
                    compare(ChcOp::BvULt, new, width),
                ],
            ),
            op(
                ChcOp::Eq,
                vec![read("a", width), var("fill", ChcSort::Bool)],
            ),
        ],
    );
    op(ChcOp::And, vec![prefix, suffix])
}

fn array(width: u32, values: impl IntoIterator<Item = bool>) -> SmtValue {
    SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: values
            .into_iter()
            .enumerate()
            .map(|(i, value)| (SmtValue::BitVec(i as u128, width), SmtValue::Bool(value)))
            .collect(),
    }
}

fn environment(width: u32, a: u16, b: u16, fill: bool) -> Map<String, SmtValue> {
    let mut env = Map::default();
    let end = 1usize << width;
    env.insert(
        "a".into(),
        array(width, (0..end).map(|i| a & (1 << i) != 0)),
    );
    env.insert(
        "b".into(),
        array(width, (0..end).map(|i| b & (1 << i) != 0)),
    );
    env.insert("fill".into(), SmtValue::Bool(fill));
    env
}

#[test]
fn exhaustive_two_bit_arrays_match_universal_resize_semantics() {
    for old in 0..4 {
        for new in 0..4 {
            for with_fill in [false, true] {
                let rewritten =
                    eliminate(&resize(old, new, 2, with_fill), "i", &ChcSort::BitVec(2)).unwrap();
                for a in 0..16u16 {
                    for b in 0..16u16 {
                        for fill in [false, true] {
                            let expected = (0..4).all(|i| {
                                let av = a & (1 << i) != 0;
                                let bv = b & (1 << i) != 0;
                                (i >= old || av == bv)
                                    && (!with_fill || i < old || i >= new || av == fill)
                            });
                            assert_eq!(
                                evaluate_expr(&rewritten, &environment(2, a, b, fill)),
                                Some(SmtValue::Bool(expected))
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn unsigned_orientations_and_inclusive_endpoints_match_direct_comparisons() {
    for operator in [ChcOp::BvULt, ChcOp::BvULe, ChcOp::BvUGt, ChcOp::BvUGe] {
        for bound in 0..4 {
            for reversed in [false, true] {
                let mut guard = compare(operator, bound, 2);
                if reversed {
                    let ChcExpr::Op(_, args) = &mut guard else {
                        unreachable!()
                    };
                    args.reverse();
                }
                let body = op(
                    ChcOp::Implies,
                    vec![
                        guard,
                        op(ChcOp::Eq, vec![read("a", 2), ChcExpr::Bool(true)]),
                    ],
                );
                let rewritten = eliminate(&body, "i", &ChcSort::BitVec(2)).unwrap();
                for bits in 0..16 {
                    let mut env = environment(2, bits, 0, false);
                    let expected = (0..4).all(|index| {
                        env.insert("i".into(), SmtValue::BitVec(index, 2));
                        evaluate_expr(&body, &env) == Some(SmtValue::Bool(true))
                    });
                    env.remove("i");
                    assert_eq!(
                        evaluate_expr(&rewritten, &env),
                        Some(SmtValue::Bool(expected))
                    );
                }
            }
        }
    }
}
