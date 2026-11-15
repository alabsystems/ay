// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::{children, Budget, Expr, ExprValue};
use num_bigint::Sign;
use num_traits::ToPrimitive;

#[derive(Clone, Copy)]
enum Comparison {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl Comparison {
    fn reverse(self) -> Self {
        match self {
            Self::Less => Self::Greater,
            Self::LessEqual => Self::GreaterEqual,
            Self::Greater => Self::Less,
            Self::GreaterEqual => Self::LessEqual,
        }
    }
}

pub(super) fn support(
    root: &Expr,
    binder: &str,
    width: u32,
    budget: &mut Budget<'_>,
) -> Option<(u128, u128)> {
    budget.work(1)?;
    let mut pending = Vec::new();
    pending.try_reserve_exact(1).ok()?;
    pending.push((root, 0));
    let mut lower = 0;
    let mut upper = 1u128.checked_shl(width)?;
    while let Some((node, depth)) = pending.pop() {
        if !node.sort().is_bool() {
            return None;
        }
        if let ExprValue::And(args) = node.value() {
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
    // Continue validating even after the intersection becomes empty.
    Some((lower, upper.max(lower)))
}

fn comparison(
    node: &Expr,
    binder: &str,
    width: u32,
    budget: &mut Budget<'_>,
) -> Option<(u128, u128)> {
    let (op, left, right) = match node.value() {
        ExprValue::BvULt(left, right) => (Comparison::Less, left, right),
        ExprValue::BvULe(left, right) => (Comparison::LessEqual, left, right),
        ExprValue::BvUGt(left, right) => (Comparison::Greater, left, right),
        ExprValue::BvUGe(left, right) => (Comparison::GreaterEqual, left, right),
        _ => return None,
    };
    budget.work(2)?;
    let (op, literal) = if is_binder(left, binder, width, budget)? {
        (op, right)
    } else if is_binder(right, binder, width, budget)? {
        (op.reverse(), left)
    } else {
        return None;
    };
    let ExprValue::BitVecConst {
        value,
        width: literal_width,
    } = literal.value()
    else {
        return None;
    };
    if *literal_width != width
        || literal.sort().bitvec_width() != Some(width)
        || value.sign() == Sign::Minus
        || value.bits() > u64::from(width)
    {
        return None;
    }
    // Authentication above limits conversion to at most 64 value bits.
    let value = u128::from(value.to_u64()?);
    let end = 1u128.checked_shl(width)?;
    match op {
        Comparison::Less => Some((0, value)),
        Comparison::LessEqual => Some((0, value.checked_add(1)?)),
        Comparison::Greater => Some((value.checked_add(1)?, end)),
        Comparison::GreaterEqual => Some((value, end)),
    }
}

pub(super) fn is_binder(
    node: &Expr,
    binder: &str,
    width: u32,
    budget: &mut Budget<'_>,
) -> Option<bool> {
    let ExprValue::Var { name } = node.value() else {
        return Some(false);
    };
    budget.name(name)?;
    if name != binder {
        return Some(false);
    }
    if node.sort().bitvec_width() != Some(width) {
        return None;
    }
    Some(true)
}
