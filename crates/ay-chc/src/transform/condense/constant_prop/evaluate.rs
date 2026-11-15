// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact, deliberately small evaluator; unsupported syntax supplies no pin.

use std::sync::Arc;

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::ground::{mask, BoolArray, Budget, Stopped, Value, MAX_DEPTH};

pub(super) type Pins = FxHashMap<ChcVar, Value>;

pub(super) fn evaluate(
    expr: &ChcExpr,
    pins: &Pins,
    budget: &mut Budget,
    depth: usize,
) -> Result<Option<Value>, Stopped> {
    budget.charge(1)?;
    if depth >= MAX_DEPTH {
        return Err(budget.stop());
    }
    let value = match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) => Some(Value::Scalar(expr.clone())),
        ChcExpr::Real(_, denominator) if *denominator != 0 => Some(Value::Scalar(expr.clone())),
        ChcExpr::BitVec(value, width) => {
            mask(*width).map(|mask| Value::Scalar(ChcExpr::BitVec(value & mask, *width)))
        }
        ChcExpr::Var(var) => {
            budget.charge(var.name.len())?;
            pins.get(var).cloned()
        }
        ChcExpr::ConstArray(ChcSort::BitVec(width), value) => {
            match evaluate(value, pins, budget, depth + 1)? {
                Some(Value::Scalar(ChcExpr::Bool(value))) => {
                    BoolArray::constant(*width, value).map(|array| Value::Array(Arc::new(array)))
                }
                _ => None,
            }
        }
        ChcExpr::Op(op, args) => evaluate_op(*op, args, pins, budget, depth + 1)?,
        _ => None,
    };
    Ok(value)
}

fn evaluate_op(
    op: ChcOp,
    args: &[Arc<ChcExpr>],
    pins: &Pins,
    budget: &mut Budget,
    depth: usize,
) -> Result<Option<Value>, Stopped> {
    // Check shape BEFORE descending: arbitrary application trees are not an
    // invitation to traverse an unsupported theory or to invent its value.
    if !matches!(
        (op, args.len()),
        (ChcOp::Store, 3)
            | (ChcOp::Select, 2)
            | (ChcOp::BvConcat, 2)
            | (ChcOp::BvExtract(_, _), 1)
            | (ChcOp::BvAdd | ChcOp::BvSub, 2)
    ) {
        return Ok(None);
    }
    let mut values = Vec::with_capacity(args.len());
    for arg in args {
        let Some(value) = evaluate(arg, pins, budget, depth)? else {
            return Ok(None);
        };
        values.push(value);
    }
    match (op, values.as_slice()) {
        (
            ChcOp::Store,
            [Value::Array(array), Value::Scalar(ChcExpr::BitVec(index, width)), Value::Scalar(ChcExpr::Bool(value))],
        ) if *width == array.width => Ok(Some(Value::Array(array.store(*index, *value, budget)?))),
        (ChcOp::Select, [Value::Array(array), Value::Scalar(ChcExpr::BitVec(index, width))])
            if *width == array.width =>
        {
            Ok(Some(Value::Scalar(ChcExpr::Bool(array.select(*index)))))
        }
        (ChcOp::BvExtract(high, low), [Value::Scalar(ChcExpr::BitVec(value, width))])
            if low <= high && high < *width =>
        {
            let result_width = high - low + 1;
            Ok(mask(result_width)
                .map(|mask| Value::Scalar(ChcExpr::BitVec((value >> low) & mask, result_width))))
        }
        (_, [Value::Scalar(ChcExpr::BitVec(a, aw)), Value::Scalar(ChcExpr::BitVec(b, bw))]) => {
            Ok(evaluate_bv_pair(op, *a, *aw, *b, *bw))
        }
        _ => Ok(None),
    }
}

fn evaluate_bv_pair(op: ChcOp, a: u128, aw: u32, b: u128, bw: u32) -> Option<Value> {
    let (value, width) = match op {
        ChcOp::BvConcat => {
            let width = aw.checked_add(bw)?;
            mask(width)?;
            (a.checked_shl(bw)? | b, width)
        }
        ChcOp::BvAdd if aw == bw => (a.wrapping_add(b), aw),
        ChcOp::BvSub if aw == bw => (a.wrapping_sub(b), aw),
        _ => return None,
    };
    Some(Value::Scalar(ChcExpr::BitVec(value & mask(width)?, width)))
}
