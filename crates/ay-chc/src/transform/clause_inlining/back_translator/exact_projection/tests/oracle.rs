// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent tiny finite evaluator, not a solver or the projection code.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(u128, u32),
    BoolArray([bool; 2]),
}

impl Value {
    fn boolean(self) -> bool {
        let Self::Bool(value) = self else {
            panic!("expected Boolean")
        };
        value
    }

    fn bits(self) -> (u128, u32) {
        let Self::Bv(value, width) = self else {
            panic!("expected bitvector")
        };
        (value, width)
    }
}

pub(super) fn truth(expr: &ChcExpr, values: &[(&str, u128)]) -> bool {
    eval(expr, values).boolean()
}

fn eval(expr: &ChcExpr, values: &[(&str, u128)]) -> Value {
    match expr {
        ChcExpr::Bool(value) => Value::Bool(*value),
        ChcExpr::BitVec(value, width) => Value::Bv(*value, *width),
        ChcExpr::Var(var) => {
            let value = values.iter().find(|(name, _)| *name == var.name).unwrap().1;
            match var.sort {
                ChcSort::Bool => Value::Bool(value != 0),
                ChcSort::BitVec(width) => Value::Bv(value, width),
                ChcSort::Array(ref key, ref element)
                    if **key == ChcSort::BitVec(1) && **element == ChcSort::Bool =>
                {
                    assert!(value < 4);
                    Value::BoolArray([value & 1 != 0, value & 2 != 0])
                }
                _ => panic!("unsupported fixture sort"),
            }
        }
        ChcExpr::ConstArray(key, value) => {
            assert_eq!(*key, ChcSort::BitVec(1));
            Value::BoolArray([eval(value, values).boolean(); 2])
        }
        ChcExpr::Op(operation, args) => {
            let args: Vec<_> = args.iter().map(|arg| eval(arg, values)).collect();
            match operation {
                ChcOp::And => Value::Bool(args.iter().all(|v| v.boolean())),
                ChcOp::Or => Value::Bool(args.iter().any(|v| v.boolean())),
                ChcOp::Not => Value::Bool(!args[0].boolean()),
                ChcOp::Eq => Value::Bool(args[0] == args[1]),
                ChcOp::Ne => Value::Bool(args[0] != args[1]),
                ChcOp::Select => {
                    let Value::BoolArray(array) = args[0] else {
                        panic!("expected array")
                    };
                    let (index, width) = args[1].bits();
                    assert_eq!(width, 1);
                    Value::Bool(array[index as usize])
                }
                ChcOp::Store => {
                    let Value::BoolArray(mut array) = args[0] else {
                        panic!("expected array")
                    };
                    let (index, width) = args[1].bits();
                    assert_eq!(width, 1);
                    array[index as usize] = args[2].boolean();
                    Value::BoolArray(array)
                }
                ChcOp::Ite => {
                    if args[0].boolean() {
                        args[1]
                    } else {
                        args[2]
                    }
                }
                ChcOp::BvAdd | ChcOp::BvSub | ChcOp::BvMul | ChcOp::BvUDiv | ChcOp::BvLShr => {
                    arithmetic(*operation, &args)
                }
                ChcOp::BvZeroExtend(extra) => {
                    let (value, width) = args[0].bits();
                    let width = width.checked_add(*extra).unwrap();
                    assert!(width <= 128);
                    Value::Bv(value, width)
                }
                ChcOp::BvExtract(high, low) => {
                    let (value, width) = args[0].bits();
                    assert!(low <= high && *high < width);
                    let width = *high - *low + 1;
                    let mask = if width == 128 {
                        u128::MAX
                    } else {
                        (1u128 << width) - 1
                    };
                    Value::Bv((value >> *low) & mask, width)
                }
                ChcOp::BvULt | ChcOp::BvULe | ChcOp::BvUGt => {
                    let (a, width) = args[0].bits();
                    let (b, other_width) = args[1].bits();
                    assert_eq!(width, other_width);
                    Value::Bool(match operation {
                        ChcOp::BvULt => a < b,
                        ChcOp::BvULe => a <= b,
                        ChcOp::BvUGt => a > b,
                        _ => unreachable!(),
                    })
                }
                _ => panic!("unsupported fixture operation {operation:?}"),
            }
        }
        _ => panic!("unsupported fixture expression"),
    }
}

fn arithmetic(operation: ChcOp, args: &[Value]) -> Value {
    let (a, width) = args[0].bits();
    let (b, other_width) = args[1].bits();
    assert_eq!(width, other_width);
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let value = match operation {
        ChcOp::BvAdd => a.wrapping_add(b) & mask,
        ChcOp::BvSub => a.wrapping_sub(b) & mask,
        ChcOp::BvMul => a.wrapping_mul(b) & mask,
        ChcOp::BvUDiv if b == 0 => mask,
        ChcOp::BvUDiv => a / b,
        ChcOp::BvLShr if b >= u128::from(width) => 0,
        ChcOp::BvLShr => a >> b,
        _ => unreachable!(),
    };
    Value::Bv(value, width)
}

#[test]
fn every_small_width_nonzero_divisor_has_exact_image() {
    for width in 1..=5 {
        let size = 1u128 << width;
        for divisor in 1..size {
            let x = var("x", width);
            let a = var("a", width);
            let formula = eq(expr(&a), quotient(&x, divisor));
            let projected = closed(&formula, &[a]);
            for a in 0..size {
                let exists = (0..size).any(|x| truth(&formula, &[("x", x), ("a", a)]));
                assert_eq!(
                    truth(&projected, &[("a", a)]),
                    exists,
                    "w={width}, d={divisor}, a={a}"
                );
            }
        }
    }
}

#[test]
fn full_u128_range_uses_no_overflowing_shift_or_truncated_bound() {
    let x = var("x", 128);
    let a = var("a", 128);
    for divisor in [1, 2, 3, u128::MAX] {
        let projected = closed(
            &eq(expr(&a), quotient(&x, divisor)),
            std::slice::from_ref(&a),
        );
        let bound = u128::MAX / divisor;
        assert!(truth(&projected, &[("a", bound)]));
        if let Some(next) = bound.checked_add(1) {
            assert!(!truth(&projected, &[("a", next)]));
        }
    }
}
