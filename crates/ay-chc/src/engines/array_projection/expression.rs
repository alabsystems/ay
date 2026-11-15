// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Iterative, fallible typing for the private candidate slice. Unsupported
//! functions, datatypes and nested array sorts decline; this is not a general
//! CHC source validator. No expression or variable discovery recurses.

use ay_core::kani_compat::DetHashMap;

use crate::expr::dag::children;
use crate::{ChcExpr, ChcSort, ChcVar};

pub(super) fn scalar(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::Real)
        || matches!(sort, ChcSort::BitVec(width) if *width > 0 && *width <= crate::MAX_BITVECTOR_WIDTH)
}

pub(super) fn supported_sort(sort: &ChcSort) -> bool {
    scalar(sort) || matches!(sort, ChcSort::Array(key, value) if scalar(key) && scalar(value))
}

/// Check every child, including expressions in erased argument positions.
/// `variable` authenticates clause-local names or a model's closed binders.
pub(super) fn checked_sort(
    root: &ChcExpr,
    poll: &mut dyn FnMut() -> bool,
    variable: &mut dyn FnMut(&ChcVar) -> bool,
) -> Option<ChcSort> {
    checked_sort_with_bound(root, poll, variable, &mut |_| true)
}

/// Extra candidate admission on EVERY computed node sort, not only the root.
/// This private callback is a resource/type bound, never proof authority.
/// Existing checked_sort retains its original broad supported-sort behavior.
pub(in crate::engines) fn checked_sort_with_bound(
    root: &ChcExpr,
    poll: &mut dyn FnMut() -> bool,
    variable: &mut dyn FnMut(&ChcVar) -> bool,
    bound: &mut dyn FnMut(&ChcSort) -> bool,
) -> Option<ChcSort> {
    if !poll() {
        return None;
    }
    let mut sorts = DetHashMap::<*const ChcExpr, ChcSort>::default();
    let mut pending = Vec::new();
    pending.try_reserve(1).ok()?;
    pending.push((root, false));
    while let Some((node, expanded)) = pending.pop() {
        if !poll() {
            return None;
        }
        let key = node as *const ChcExpr;
        if sorts.contains_key(&key) {
            continue;
        }
        if !expanded {
            // Reject unsupported nodes before allocating their child census.
            if matches!(
                node,
                ChcExpr::PredicateApp(..)
                    | ChcExpr::FuncApp(..)
                    | ChcExpr::ConstArrayMarker(..)
                    | ChcExpr::IsTesterMarker(..)
            ) {
                return None;
            }
            pending.try_reserve(1).ok()?;
            pending.push((node, true));
            for child in children(node).iter().rev() {
                if !poll() {
                    return None;
                }
                pending.try_reserve(1).ok()?;
                pending.push((child.as_ref(), false));
            }
            continue;
        }
        let result = node_sort(node, &sorts, variable, poll)?;
        if !supported_sort(&result) || !bound(&result) {
            return None;
        }
        sorts.insert(key, result);
    }
    let result = sorts.remove(&(root as *const ChcExpr))?;
    drop(pending);
    drop(sorts);
    poll().then_some(result)
}

fn node_sort(
    node: &ChcExpr,
    sorts: &DetHashMap<*const ChcExpr, ChcSort>,
    variable: &mut dyn FnMut(&ChcVar) -> bool,
    poll: &mut dyn FnMut() -> bool,
) -> Option<ChcSort> {
    match node {
        ChcExpr::ArrayLambda(_) => None,
        ChcExpr::Bool(_) => Some(ChcSort::Bool),
        ChcExpr::Int(_) => Some(ChcSort::Int),
        ChcExpr::Real(_, denominator) => (*denominator != 0).then_some(ChcSort::Real),
        ChcExpr::BitVec(value, width) => {
            let sort = ChcSort::BitVec(*width);
            (scalar(&sort) && (*width >= 128 || *value < (1u128 << width))).then_some(sort)
        }
        ChcExpr::Var(var) => (supported_sort(&var.sort) && variable(var)).then(|| var.sort.clone()),
        ChcExpr::ConstArray(key, value) => {
            if !scalar(key) {
                return None;
            }
            let value_sort = sorts.get(&(value.as_ref() as *const ChcExpr))?;
            scalar(value_sort)
                .then(|| ChcSort::Array(Box::new(key.clone()), Box::new(value_sort.clone())))
        }
        ChcExpr::Op(op, arguments) => {
            let mut argument_sorts = Vec::new();
            argument_sorts.try_reserve_exact(arguments.len()).ok()?;
            for argument in arguments {
                if !poll() {
                    return None;
                }
                argument_sorts.push(sorts.get(&(argument.as_ref() as *const ChcExpr))?.clone());
            }
            crate::pdr::validate_qf_operation(*op, &argument_sorts).ok()
        }
        ChcExpr::PredicateApp(..)
        | ChcExpr::FuncApp(..)
        | ChcExpr::ConstArrayMarker(..)
        | ChcExpr::IsTesterMarker(..) => None,
    }
}
