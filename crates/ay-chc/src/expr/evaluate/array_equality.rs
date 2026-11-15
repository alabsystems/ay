// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed completeness fallback for finite-store arrays over integer indices.

use super::{ChcExpr, ChcOp, SmtValue};
use crate::ChcSort;
use num_traits::ToPrimitive;

mod finite_bool;

pub(super) fn typed_array_equality(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    lhs_value: &SmtValue,
    rhs_value: &SmtValue,
) -> Option<bool> {
    integer_array_equality(lhs, rhs, lhs_value, rhs_value)
        .or_else(|| finite_bool::equality(lhs, rhs, lhs_value, rhs_value))
}

/// Shared by both source walks and both complete value representations.
/// Big integers additionally cost one unit per 64 payload bits before comparison.
const MAX_WORK: usize = 4096;

#[derive(Clone, Copy)]
enum Expected {
    Integer,
    IntegerArray,
}

fn spend(remaining: &mut usize, amount: usize) -> Option<()> {
    *remaining = remaining.checked_sub(amount)?;
    Some(())
}

fn declared_sort_matches(sort: &ChcSort, expected: Expected) -> bool {
    match (sort, expected) {
        (ChcSort::Int, Expected::Integer) => true,
        (ChcSort::Array(key, value), Expected::IntegerArray) => {
            matches!(key.as_ref(), ChcSort::Int) && matches!(value.as_ref(), ChcSort::Int)
        }
        _ => false,
    }
}

/// Borrow the exact carrier metadata, checking supported computed carriers
/// instead of treating `ChcExpr::sort()` (which follows a store's base) as a
/// type validator. Unsupported source shapes retain the old indeterminate result.
fn source_sorts_match(lhs: &ChcExpr, rhs: &ChcExpr, remaining: &mut usize) -> Option<()> {
    let mut stack = vec![(lhs, Expected::IntegerArray), (rhs, Expected::IntegerArray)];
    while let Some((expr, expected)) = stack.pop() {
        spend(remaining, 1)?;
        match (expr, expected) {
            (ChcExpr::Var(var), _) if declared_sort_matches(&var.sort, expected) => {}
            (ChcExpr::FuncApp(_, sort, _), _) if declared_sort_matches(sort, expected) => {}
            (ChcExpr::Int(_), Expected::Integer) => {}
            (ChcExpr::ConstArray(ChcSort::Int, value), Expected::IntegerArray) => {
                if stack.len() >= *remaining {
                    return None;
                }
                stack.push((value, Expected::Integer));
            }
            (ChcExpr::Op(ChcOp::Store, args), Expected::IntegerArray) if args.len() == 3 => {
                if stack.len().checked_add(3)? > *remaining {
                    return None;
                }
                stack.push((&args[0], Expected::IntegerArray));
                stack.push((&args[1], Expected::Integer));
                stack.push((&args[2], Expected::Integer));
            }
            (ChcExpr::Op(ChcOp::Select, args), Expected::Integer) if args.len() == 2 => {
                if stack.len().checked_add(2)? > *remaining {
                    return None;
                }
                stack.push((&args[0], Expected::IntegerArray));
                stack.push((&args[1], Expected::Integer));
            }
            (ChcExpr::Op(op, args), Expected::Integer)
                if match op {
                    ChcOp::Add | ChcOp::Mul => true,
                    ChcOp::Sub => !args.is_empty(),
                    ChcOp::Div | ChcOp::Mod => args.len() == 2,
                    ChcOp::Neg => args.len() == 1,
                    _ => false,
                } =>
            {
                if stack.len().checked_add(args.len())? > *remaining {
                    return None;
                }
                stack.extend(args.iter().map(|arg| (arg.as_ref(), Expected::Integer)));
            }
            _ => return None,
        }
    }
    Some(())
}

fn canonical_integer(value: &SmtValue, remaining: &mut usize) -> Option<()> {
    spend(remaining, 1)?;
    match value {
        SmtValue::Int(_) => Some(()),
        SmtValue::BigInt(value) => {
            spend(remaining, usize::try_from(value.bits().div_ceil(64)).ok()?)?;
            // The untyped comparator relies on this representation invariant.
            value.to_i128().is_none().then_some(())
        }
        _ => None,
    }
}

fn integer_array_default<'a>(value: &'a SmtValue, remaining: &mut usize) -> Option<&'a SmtValue> {
    spend(remaining, 1)?;
    let (default, entries) = match value {
        SmtValue::ConstArray(default) => (default.as_ref(), &[][..]),
        SmtValue::ArrayMap { default, entries } => (default.as_ref(), entries.as_slice()),
        _ => return None,
    };
    if entries.len().checked_mul(2)?.checked_add(1)? > *remaining {
        return None;
    }
    canonical_integer(default, remaining)?;
    for (key, element) in entries {
        canonical_integer(key, remaining)?;
        canonical_integer(element, remaining)?;
    }
    Some(default)
}

/// Called only after untyped comparison abstains. A finite union of store
/// keys cannot cover the infinite integer domain. Thus differing integer
/// defaults exhibit a disequality at an index outside that union, regardless
/// of duplicate stores or write order. No corresponding inference is made for
/// Bool, BV, datatype, uninterpreted, or otherwise unsupported index sorts.
pub(super) fn integer_array_equality(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    lhs_value: &SmtValue,
    rhs_value: &SmtValue,
) -> Option<bool> {
    let mut remaining = MAX_WORK;
    source_sorts_match(lhs, rhs, &mut remaining)?;
    let lhs_default = integer_array_default(lhs_value, &mut remaining)?;
    let rhs_default = integer_array_default(rhs_value, &mut remaining)?;
    (super::smt_values_equal(lhs_default, rhs_default) == Some(false)).then_some(false)
}

#[cfg(test)]
mod tests;
