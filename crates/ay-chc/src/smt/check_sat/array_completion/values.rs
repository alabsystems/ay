// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked primitive/array carriers for original-model reconstruction.

use super::{Budget, ChcSort, SmtValue};
use num_traits::ToPrimitive;

pub(super) fn sort(sort: &ChcSort, budget: &mut Budget<'_>) -> Option<()> {
    let mut stack = vec![(sort, 0usize)];
    while let Some((sort, depth)) = stack.pop() {
        budget.charge(1)?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH / 2 {
            return None;
        }
        match sort {
            ChcSort::Bool | ChcSort::Int | ChcSort::Real => {}
            ChcSort::BitVec(width) if *width > 0 && *width <= crate::MAX_BITVECTOR_WIDTH => {}
            ChcSort::Array(key, value) => {
                if stack.len().checked_add(2)? > budget.remaining {
                    return None;
                }
                stack.try_reserve(2).ok()?;
                stack.push((key, depth + 1));
                stack.push((value, depth + 1));
            }
            _ => return None,
        }
    }
    Some(())
}

pub(super) fn typed(value: &SmtValue, sort: &ChcSort, budget: &mut Budget<'_>) -> Option<()> {
    let mut stack = vec![(value, sort)];
    while let Some((value, sort)) = stack.pop() {
        budget.charge(1)?;
        match (value, sort) {
            (SmtValue::Bool(_), ChcSort::Bool) | (SmtValue::Int(_), ChcSort::Int) => {}
            (SmtValue::BigInt(value), ChcSort::Int) if value.to_i128().is_none() => {
                budget.charge(usize::try_from(value.bits().div_ceil(64)).ok()?)?;
            }
            (SmtValue::Real(value), ChcSort::Real) => {
                budget.charge(usize::try_from(value.numer().bits().div_ceil(64)).ok()?)?;
                budget.charge(usize::try_from(value.denom().bits().div_ceil(64)).ok()?)?;
            }
            (SmtValue::BitVec(value, width), ChcSort::BitVec(expected))
                if width == expected
                    && *width > 0
                    && *width <= 128
                    && (*width == 128 || *value >> *width == 0) => {}
            (SmtValue::BigBitVec(value, width), ChcSort::BitVec(expected))
                if width == expected
                    && *width > 128
                    && *width <= crate::MAX_BITVECTOR_WIDTH
                    && value.bits() <= u64::from(*width) =>
            {
                budget.charge(usize::try_from(value.bits().div_ceil(64)).ok()?)?;
            }
            (SmtValue::ConstArray(default), ChcSort::Array(_, element)) => {
                stack.try_reserve(1).ok()?;
                stack.push((default, element));
            }
            (SmtValue::ArrayMap { default, entries }, ChcSort::Array(key, element)) => {
                let needed = entries.len().checked_mul(2)?.checked_add(1)?;
                if stack.len().checked_add(needed)? > budget.remaining {
                    return None;
                }
                stack.try_reserve(needed).ok()?;
                stack.push((default, element));
                for (index, value) in entries {
                    stack.push((index, key));
                    stack.push((value, element));
                }
            }
            _ => return None,
        }
    }
    Some(())
}

/// Logical copy/comparison payload, bounded without cloning it.
pub(super) fn size(value: &SmtValue, budget: &mut Budget<'_>) -> Option<usize> {
    let mut stack = vec![value];
    let mut size = 0usize;
    while let Some(value) = stack.pop() {
        budget.charge(1)?;
        size = size.checked_add(1)?;
        if size > crate::expr::MAX_PREPROCESSING_NODES {
            return None;
        }
        let bits = match value {
            SmtValue::BigInt(value) => value.bits(),
            SmtValue::BigBitVec(value, _) => value.bits(),
            SmtValue::Real(value) => value.numer().bits().checked_add(value.denom().bits())?,
            _ => 0,
        };
        let words = usize::try_from(bits.div_ceil(64)).ok()?;
        budget.charge(words)?;
        size = size.checked_add(words)?;
        if size > crate::expr::MAX_PREPROCESSING_NODES {
            return None;
        }
        match value {
            SmtValue::ConstArray(default) => {
                stack.try_reserve(1).ok()?;
                stack.push(default);
            }
            SmtValue::ArrayMap { default, entries } => {
                let needed = entries.len().checked_mul(2)?.checked_add(1)?;
                if stack.len().checked_add(needed)? > crate::expr::MAX_PREPROCESSING_NODES - size {
                    return None;
                }
                stack.try_reserve(needed).ok()?;
                stack.push(default);
                for (key, value) in entries {
                    stack.push(key);
                    stack.push(value);
                }
            }
            SmtValue::Bool(_)
            | SmtValue::Int(_)
            | SmtValue::BigInt(_)
            | SmtValue::Real(_)
            | SmtValue::BitVec(..)
            | SmtValue::BigBitVec(..) => {}
            _ => return None,
        }
    }
    Some(size)
}

/// Admit the shape/payload of an auxiliary value before discarding it.
/// This is cleanup accounting, not a typed model witness or source premise.
pub(super) fn discarded(value: &SmtValue, budget: &mut Budget<'_>) -> Option<()> {
    let mut stack = vec![(value, 0usize)];
    while let Some((value, depth)) = stack.pop() {
        budget.charge(1)?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH / 2 {
            return None;
        }
        let bits = match value {
            SmtValue::BigInt(value) => value.bits(),
            SmtValue::BigBitVec(value, _) => value.bits(),
            SmtValue::Real(value) => value.numer().bits().checked_add(value.denom().bits())?,
            _ => 0,
        };
        budget.charge(usize::try_from(bits.div_ceil(64)).ok()?)?;
        match value {
            SmtValue::Opaque(text) => budget.charge(text.len())?,
            SmtValue::Datatype(name, fields) => {
                budget.charge(name.len())?;
                if stack.len().checked_add(fields.len())? > budget.remaining {
                    return None;
                }
                stack.try_reserve(fields.len()).ok()?;
                stack.extend(fields.iter().map(|field| (field, depth + 1)));
            }
            SmtValue::ConstArray(default) => {
                if stack.len().checked_add(1)? > budget.remaining {
                    return None;
                }
                stack.try_reserve(1).ok()?;
                stack.push((default, depth + 1));
            }
            SmtValue::ArrayMap { default, entries } => {
                let needed = entries.len().checked_mul(2)?.checked_add(1)?;
                if stack.len().checked_add(needed)? > budget.remaining {
                    return None;
                }
                stack.try_reserve(needed).ok()?;
                stack.push((default, depth + 1));
                for (key, value) in entries {
                    stack.push((key, depth + 1));
                    stack.push((value, depth + 1));
                }
            }
            SmtValue::Bool(_)
            | SmtValue::Int(_)
            | SmtValue::BigInt(_)
            | SmtValue::Real(_)
            | SmtValue::BitVec(..)
            | SmtValue::BigBitVec(..) => {}
        }
    }
    Some(())
}
