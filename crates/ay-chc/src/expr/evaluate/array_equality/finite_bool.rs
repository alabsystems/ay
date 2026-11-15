// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact finite-domain fallback; a different default need not be observable.

use std::collections::BTreeMap;

use super::{spend, ChcExpr, ChcOp, ChcSort, SmtValue, MAX_WORK};

#[derive(Clone, Copy)]
enum Slot {
    Array,
    Index,
    Boolean,
}

fn sort_matches(sort: &ChcSort, slot: Slot, width: u32) -> bool {
    match (slot, sort) {
        (Slot::Array, ChcSort::Array(key, value)) => {
            **key == ChcSort::BitVec(width) && **value == ChcSort::Bool
        }
        (Slot::Index, ChcSort::BitVec(actual)) => *actual == width,
        (Slot::Boolean, ChcSort::Bool) => true,
        _ => false,
    }
}

fn source_matches(expr: &ChcExpr, width: u32, remaining: &mut usize) -> Option<()> {
    let mut pending = vec![(expr, Slot::Array)];
    while let Some((expr, slot)) = pending.pop() {
        spend(remaining, 1)?;
        match (expr, slot) {
            (ChcExpr::Var(var), _) if sort_matches(&var.sort, slot, width) => {}
            (ChcExpr::FuncApp(_, sort, _), _) if sort_matches(sort, slot, width) => {}
            (ChcExpr::BitVec(_, actual), Slot::Index) if *actual == width => {}
            (ChcExpr::Bool(_), Slot::Boolean) => {}
            (ChcExpr::ConstArray(ChcSort::BitVec(actual), value), Slot::Array)
                if *actual == width =>
            {
                pending.push((value, Slot::Boolean));
            }
            (ChcExpr::Op(ChcOp::Store, args), Slot::Array) if args.len() == 3 => {
                if pending.len().checked_add(3)? > *remaining {
                    return None;
                }
                pending.push((&args[0], Slot::Array));
                pending.push((&args[1], Slot::Index));
                pending.push((&args[2], Slot::Boolean));
            }
            _ => return None,
        }
    }
    Some(())
}

fn declared_width(sort: &ChcSort) -> Option<u32> {
    let ChcSort::Array(key, value) = sort else {
        return None;
    };
    match (key.as_ref(), value.as_ref()) {
        (ChcSort::BitVec(width), ChcSort::Bool) => Some(*width),
        _ => None,
    }
}

/// Borrow terminal metadata while charging every base-chain visit. Calling
/// `sort()` first would recursively inspect/clone unsupported input before
/// this fallback's allowance could refuse it.
fn source_width(mut expression: &ChcExpr, remaining: &mut usize) -> Option<u32> {
    loop {
        spend(remaining, 1)?;
        match expression {
            ChcExpr::Var(var) => return declared_width(&var.sort),
            ChcExpr::FuncApp(_, sort, _) => return declared_width(sort),
            ChcExpr::ConstArray(ChcSort::BitVec(width), _) => return Some(*width),
            ChcExpr::Op(ChcOp::Store, arguments) if arguments.len() == 3 => {
                expression = &arguments[0];
            }
            _ => return None,
        }
    }
}

fn canonical(
    value: &SmtValue,
    width: u32,
    mask: u128,
    remaining: &mut usize,
) -> Option<(bool, BTreeMap<u128, bool>)> {
    spend(remaining, 1)?;
    let (default, entries) = match value {
        SmtValue::ConstArray(default) => (default.as_ref(), &[][..]),
        SmtValue::ArrayMap { default, entries } => (default.as_ref(), entries.as_slice()),
        _ => return None,
    };
    let SmtValue::Bool(default) = default else {
        return None;
    };
    if entries.len().checked_mul(3)? > *remaining {
        return None;
    }
    let mut normalized = BTreeMap::new();
    for (key, element) in entries {
        spend(remaining, 3)?;
        let (SmtValue::BitVec(key, actual), SmtValue::Bool(element)) = (key, element) else {
            return None;
        };
        if *actual != width || *key > mask {
            return None;
        }
        // Model entries follow store order. Remove overwritten defaults too.
        if element == default {
            normalized.remove(key);
        } else {
            normalized.insert(*key, *element);
        }
    }
    Some((*default, normalized))
}

pub(super) fn equality(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    lhs_value: &SmtValue,
    rhs_value: &SmtValue,
) -> Option<bool> {
    let mut remaining = MAX_WORK;
    let width = source_width(lhs, &mut remaining)?;
    if !(1..=128).contains(&width) {
        return None;
    }
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    source_matches(lhs, width, &mut remaining)?;
    source_matches(rhs, width, &mut remaining)?;
    let (a_default, a) = canonical(lhs_value, width, mask, &mut remaining)?;
    let (b_default, b) = canonical(rhs_value, width, mask, &mut remaining)?;
    let mut union = a.len();
    for (key, value) in &a {
        spend(&mut remaining, 1)?;
        if *value != b.get(key).copied().unwrap_or(b_default) {
            return Some(false);
        }
    }
    for (key, value) in &b {
        spend(&mut remaining, 1)?;
        if *value != a.get(key).copied().unwrap_or(a_default) {
            return Some(false);
        }
        union += usize::from(!a.contains_key(key));
    }
    // No enumeration or overflowing shift: a bounded union cannot cover a
    // domain larger than usize. Defaults matter exactly off this union.
    Some(a_default == b_default || 1usize.checked_shl(width).is_some_and(|size| size == union))
}

#[cfg(test)]
mod tests;
