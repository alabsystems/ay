// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use crate::{Expr, ExprValue};
use num_traits::ToPrimitive;

#[derive(Clone, Copy, Debug)]
pub(super) struct Model {
    pub(super) a: u8,
    pub(super) b: u8,
    pub(super) x: u8,
    pub(super) y: u8,
    pub(super) fill: bool,
    pub(super) index: u8,
}

pub(super) fn bit(array: u8, index: u8) -> bool {
    assert!(index < 4);
    array & (1 << index) != 0
}

fn bits(expr: &Expr, model: Model) -> u8 {
    assert_eq!(expr.sort().bitvec_width(), Some(2));
    match expr.value() {
        ExprValue::Var { name } => match name.as_str() {
            "i" => model.index,
            "x" => model.x,
            "y" => model.y,
            _ => panic!("unexpected index variable"),
        },
        ExprValue::BitVecConst { value, width: 2 } => value.to_u8().unwrap(),
        ExprValue::BvAdd(left, right) => bits(left, model).wrapping_add(bits(right, model)) & 3,
        ExprValue::BvSub(left, right) => bits(left, model).wrapping_sub(bits(right, model)) & 3,
        other => panic!("unexpected BV2 oracle node: {other:?}"),
    }
}

pub(super) fn truth(expr: &Expr, model: Model) -> bool {
    assert!(expr.sort().is_bool());
    match expr.value() {
        ExprValue::BoolConst(value) => *value,
        ExprValue::Var { name } if name == "fill" => model.fill,
        ExprValue::And(args) => args.iter().all(|arg| truth(arg, model)),
        ExprValue::Or(args) => args.iter().any(|arg| truth(arg, model)),
        ExprValue::Not(arg) => !truth(arg, model),
        ExprValue::Implies(left, right) => !truth(left, model) || truth(right, model),
        ExprValue::Eq(left, right) => {
            if left.sort().is_bool() {
                truth(left, model) == truth(right, model)
            } else {
                bits(left, model) == bits(right, model)
            }
        }
        ExprValue::BvULt(left, right) => bits(left, model) < bits(right, model),
        ExprValue::BvULe(left, right) => bits(left, model) <= bits(right, model),
        ExprValue::BvUGt(left, right) => bits(left, model) > bits(right, model),
        ExprValue::BvUGe(left, right) => bits(left, model) >= bits(right, model),
        ExprValue::Select { array, index } => {
            let ExprValue::Var { name } = array.value() else {
                panic!("oracle requires a source array variable")
            };
            let data = match name.as_str() {
                "a" => model.a,
                "b" => model.b,
                _ => panic!("unknown source array"),
            };
            bit(data, bits(index, model))
        }
        ExprValue::Forall {
            vars,
            body,
            triggers,
        } => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "i");
            assert_eq!(vars[0].1.bitvec_width(), Some(2));
            assert_eq!(triggers.as_slice(), &[] as &[Vec<Expr>]);
            (0..4).all(|index| truth(body, Model { index, ..model }))
        }
        other => panic!("unexpected Boolean oracle node: {other:?}"),
    }
}
