// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete checked correspondence, never a claim of equivalent source clauses.
//! Map keys must be typed literal observations, not free variables or renderings.

use super::{
    admission::{bounded_sort, MAX_ARITY},
    projection::Projection,
};
use crate::problem::ArrayScalarizedArg;
use crate::{ChcExpr, ChcSort};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Key {
    Int(i128),
    BitVec(u128, u32),
}

fn key(index: &ChcExpr, sort: &ChcSort) -> Option<Key> {
    match (index, sort) {
        (ChcExpr::Int(value), ChcSort::Int) => Some(Key::Int(*value)),
        (ChcExpr::BitVec(value, width), ChcSort::BitVec(expected))
            if width == expected
                && *width > 0
                && *width <= 128
                && (*width >= 128 || *value < (1u128 << width)) =>
        {
            Some(Key::BitVec(*value, *width))
        }
        _ => None,
    }
}

pub(super) fn authenticate(
    projected: &Projection<'_>,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let original = projected.original.predicates();
    let reduced = projected.reduced.predicates();
    if !poll()
        || original.len() != reduced.len()
        || projected.map.original_predicates.len() != original.len()
        || projected.map.pred_args.len() != original.len()
    {
        return None;
    }
    for ((old, new), recorded) in original
        .iter()
        .zip(reduced)
        .zip(&projected.map.original_predicates)
    {
        if recorded.name.len() > 1024
            || new.name.len() > 1024
            || recorded.arg_sorts.len() != old.arg_sorts.len()
            || new.arg_sorts.len() > MAX_ARITY
            || !recorded.arg_sorts.iter().all(bounded_sort)
            || !new.arg_sorts.iter().all(bounded_sort)
        {
            return None;
        }
        if !poll()
            || old.id != new.id
            || old.id != recorded.id
            || old.name != new.name
            || old.name != recorded.name
            || old.arg_sorts != recorded.arg_sorts
            || projected.reduced.lookup_predicate(&old.name) != Some(old.id)
        {
            return None;
        }
        let mappings = projected.map.pred_args.get(&old.id)?;
        if mappings.len() != new.arg_sorts.len() || mappings.len() > MAX_ARITY {
            return None;
        }
        correspondence(&old.arg_sorts, &new.arg_sorts, mappings, poll)?;
    }
    poll().then_some(())
}

fn correspondence(
    original: &[ChcSort],
    reduced: &[ChcSort],
    mappings: &[ArrayScalarizedArg],
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let mut cursor = 0usize;
    for (position, sort) in original.iter().enumerate() {
        if !poll() {
            return None;
        }
        let first = mappings.get(cursor)?;
        if let ArrayScalarizedArg::Original(index) = first {
            if *index != position || reduced.get(cursor)? != sort {
                return None;
            }
            cursor = cursor.checked_add(1)?;
            continue;
        }
        let ChcSort::Array(key_sort, value_sort) = sort else {
            return None;
        };
        let mut seen = Vec::new();
        seen.try_reserve_exact(MAX_ARITY).ok()?;
        while let Some(ArrayScalarizedArg::Select {
            original_arg,
            index,
        }) = mappings.get(cursor)
        {
            if *original_arg != position {
                break;
            }
            if !poll() || reduced.get(cursor)? != value_sort.as_ref() {
                return None;
            }
            let current = key(index, key_sort)?;
            for previous in &seen {
                if !poll() || previous == &current {
                    return None;
                }
            }
            seen.push(current);
            cursor = cursor.checked_add(1)?;
        }
        if seen.is_empty() {
            return None;
        }
    }
    (cursor == mappings.len() && poll()).then_some(())
}
