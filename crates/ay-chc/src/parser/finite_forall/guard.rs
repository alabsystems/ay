// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::{children, Budget};
use crate::{ChcExpr, ChcOp, ChcSort};

pub(super) fn support(
    root: &ChcExpr,
    binder: &str,
    width: u32,
    budget: &mut Budget,
) -> Option<(u128, u128)> {
    budget.work(1)?;
    let mut pending = vec![(root, 0)];
    let mut lower = 0;
    let mut upper = 1u128.checked_shl(width)?;
    while let Some((node, depth)) = pending.pop() {
        if let ChcExpr::Op(ChcOp::And, args) = node {
            if args.is_empty() {
                return None;
            }
            children(&mut pending, args, depth, budget)?;
        } else {
            let (lo, hi) = comparison(node, binder, width, budget)?;
            lower = lower.max(lo);
            upper = upper.min(hi);
        }
    }
    // Do not stop at an empty intersection: later guards still need validation.
    Some((lower, upper.max(lower)))
}

fn comparison(
    node: &ChcExpr,
    binder: &str,
    width: u32,
    budget: &mut Budget,
) -> Option<(u128, u128)> {
    let ChcExpr::Op(op, args) = node else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    budget.work(2)?;
    let (op, literal) = if is_binder(&args[0], binder, width, budget)? {
        (*op, &args[1])
    } else if is_binder(&args[1], binder, width, budget)? {
        (reverse(*op)?, &args[0])
    } else {
        return None;
    };
    let ChcExpr::BitVec(value, literal_width) = literal.as_ref() else {
        return None;
    };
    let end = 1u128.checked_shl(width)?;
    if *literal_width != width || *value >= end {
        return None;
    }
    match op {
        ChcOp::BvULt => Some((0, *value)),
        ChcOp::BvULe => Some((0, value.checked_add(1)?)),
        ChcOp::BvUGt => Some((value.checked_add(1)?, end)),
        ChcOp::BvUGe => Some((*value, end)),
        _ => None,
    }
}

fn reverse(op: ChcOp) -> Option<ChcOp> {
    match op {
        ChcOp::BvULt => Some(ChcOp::BvUGt),
        ChcOp::BvULe => Some(ChcOp::BvUGe),
        ChcOp::BvUGt => Some(ChcOp::BvULt),
        ChcOp::BvUGe => Some(ChcOp::BvULe),
        _ => None,
    }
}

pub(super) fn is_binder(
    node: &ChcExpr,
    binder: &str,
    width: u32,
    budget: &mut Budget,
) -> Option<bool> {
    let ChcExpr::Var(var) = node else {
        return Some(false);
    };
    budget.name(&var.name)?;
    if var.name != binder {
        return Some(false);
    }
    if !matches!(&var.sort, ChcSort::BitVec(w) if *w == width) {
        return None;
    }
    Some(true)
}
