// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact scalar-variable accounting for query-anchored candidates.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar};

use super::GhostPredSpec;

/// A directly observed clause-local BV index and its reserved source slot.
pub(super) struct LocalIndexRead {
    pub(super) index: ChcVar,
    pub(super) array_position: usize,
    pub(super) slot: usize,
}

/// Authenticate local indices before rewriting any guard. This separate,
/// batch-wide census budget does not renew the per-target rewrite allowance.
/// Only direct BV1--64 indices gain support; an unobserved scalar local, mixed
/// name/sort use, or exhausted slot set still makes the query unsupported.
pub(super) fn local_index_reads(
    constraint: &ChcExpr,
    positions: &FxHashMap<ChcVar, usize>,
    layout: &GhostPredSpec,
    pairs_per_array: usize,
    remaining: &mut usize,
    stopped: &mut dyn FnMut() -> bool,
) -> Option<Vec<LocalIndexRead>> {
    let mut names = FxHashMap::default();
    for variable in positions.keys() {
        charge_controlled(remaining, stopped)?;
        register_query_name(variable, &mut names, remaining)?;
    }
    let mut locals = FxHashSet::default();
    let mut reads = Vec::new();
    let mut stack = vec![(constraint, 0usize)];
    while let Some((expr, depth)) = stack.pop() {
        charge_controlled(remaining, stopped)?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        match expr {
            ChcExpr::Var(variable) => {
                register_query_name(variable, &mut names, remaining)?;
                if !positions.contains_key(variable) {
                    locals.insert(variable);
                    if locals.len() > super::MAX_SLOTS_PER_PREDICATE {
                        return None;
                    }
                }
            }
            ChcExpr::Op(op, args) => {
                if *op == ChcOp::Select {
                    observe_local_index(
                        args,
                        positions,
                        layout,
                        pairs_per_array,
                        &mut reads,
                        remaining,
                    )?;
                }
                if stack.len().checked_add(args.len())? > *remaining {
                    *remaining = 0;
                    return None;
                }
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
                if stack.len().checked_add(args.len())? > *remaining {
                    *remaining = 0;
                    return None;
                }
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::ConstArray(_, value) => stack.push((value.as_ref(), depth + 1)),
            _ => {}
        }
    }
    for variable in locals {
        charge_controlled(remaining, stopped)?;
        if !reads.iter().any(|read| read.index == *variable) {
            return None;
        }
    }
    (!stopped()).then_some(reads)
}

fn register_query_name<'a>(
    variable: &'a ChcVar,
    names: &mut FxHashMap<&'a str, &'a ChcSort>,
    remaining: &mut usize,
) -> Option<()> {
    // Charge before hashing a possibly hostile name, including repeated uses.
    let Some(rest) = remaining.checked_sub(variable.name.len()) else {
        *remaining = 0;
        return None;
    };
    *remaining = rest;
    match names.get(variable.name.as_str()) {
        Some(sort) if **sort != variable.sort => None,
        Some(_) => Some(()),
        None => {
            names.insert(variable.name.as_str(), &variable.sort);
            Some(())
        }
    }
}

fn observe_local_index(
    args: &[std::sync::Arc<ChcExpr>],
    positions: &FxHashMap<ChcVar, usize>,
    layout: &GhostPredSpec,
    pairs_per_array: usize,
    reads: &mut Vec<LocalIndexRead>,
    remaining: &mut usize,
) -> Option<()> {
    let [array, index] = args else {
        return Some(());
    };
    let (ChcExpr::Var(array), ChcExpr::Var(index)) = (array.as_ref(), index.as_ref()) else {
        return Some(());
    };
    // Preorder observes this read before visiting its two variable children.
    // Charge their names before this early hash/clone, as well as charging
    // their later ordinary occurrence visits.
    let Some(left) = remaining
        .checked_sub(array.name.len())
        .and_then(|left| left.checked_sub(index.name.len()))
    else {
        *remaining = 0;
        return None;
    };
    *remaining = left;
    if positions.contains_key(index) {
        return Some(());
    }
    if !matches!(index.sort, ChcSort::BitVec(1..=64)) {
        return None;
    }
    let position = *positions.get(array)?;
    let ordinal = layout.array_positions.iter().position(|p| *p == position)?;
    if layout.index_sorts.get(ordinal) != Some(&index.sort) {
        return None;
    }
    if reads
        .iter()
        .any(|read| read.array_position == position && read.index == *index)
    {
        return Some(());
    }
    let slot = reads
        .iter()
        .filter(|read| read.array_position == position)
        .count();
    if slot >= pairs_per_array || reads.len() >= super::MAX_SLOTS_PER_PREDICATE {
        return None;
    }
    reads.push(LocalIndexRead {
        index: index.clone(),
        array_position: position,
        slot,
    });
    Some(())
}

/// Return the exact query-variable to argument-position map. A repeated name,
/// non-variable argument, wrong sort, or wrong arity is ambiguous.
pub(super) fn query_argument_positions(
    args: &[ChcExpr],
    declared_sorts: &[ChcSort],
) -> Option<FxHashMap<ChcVar, usize>> {
    if args.len() != declared_sorts.len() {
        return None;
    }
    let mut positions = FxHashMap::default();
    let mut names = FxHashSet::default();
    for (position, (argument, declared_sort)) in args.iter().zip(declared_sorts).enumerate() {
        let ChcExpr::Var(variable) = argument else {
            return None;
        };
        if variable.sort != *declared_sort || !names.insert(variable.name.clone()) {
            return None;
        }
        positions.insert(variable.clone(), position);
    }
    Some(positions)
}

/// Charge every used ghost field to the original array column that owns it.
/// This permits unrelated CFG columns to be projected away during transport.
pub(super) fn required_original_positions(
    vars: &[ChcVar],
    formula: &ChcExpr,
    layout: &GhostPredSpec,
    pairs_per_array: usize,
) -> Option<FxHashSet<usize>> {
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    required_original_positions_bounded(
        vars,
        formula,
        layout,
        pairs_per_array,
        &mut remaining,
        &mut || false,
    )
}

/// The controlled form shares one work budget with its caller and polls while
/// accounting both formula nodes and formal-variable scans.
pub(super) fn required_original_positions_bounded(
    vars: &[ChcVar],
    formula: &ChcExpr,
    layout: &GhostPredSpec,
    pairs_per_array: usize,
    remaining: &mut usize,
    stopped: &mut dyn FnMut() -> bool,
) -> Option<FxHashSet<usize>> {
    if pairs_per_array == 0
        || vars.len()
            != layout
                .original_arity
                .checked_add(layout.slots(pairs_per_array).checked_mul(2)?)?
    {
        return None;
    }
    let mut allowed = FxHashSet::default();
    for variable in vars {
        charge_controlled(remaining, stopped)?;
        allowed.insert(variable.clone());
    }
    let mut used = FxHashSet::default();
    exact_scalar_walk_collect_controlled(formula, &allowed, 0, remaining, &mut used, stopped)?;
    let mut required = FxHashSet::default();
    for (position, variable) in vars.iter().enumerate() {
        charge_controlled(remaining, stopped)?;
        if !used.remove(variable) {
            continue;
        }
        if position < layout.original_arity {
            required.insert(position);
            continue;
        }
        let ghost_offset = position.checked_sub(layout.original_arity)?;
        let slot = ghost_offset.checked_div(2)?;
        let array_ordinal = slot.checked_div(pairs_per_array)?;
        required.insert(*layout.array_positions.get(array_ordinal)?);
    }
    (!stopped() && used.is_empty()).then_some(required)
}

pub(super) fn scalar_candidate_node_count(
    problem: &ChcProblem,
    vars: &[ChcVar],
    formula: &ChcExpr,
) -> Option<usize> {
    let allowed: FxHashSet<ChcVar> = vars.iter().cloned().collect();
    let mut used = FxHashSet::default();
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    exact_scalar_walk_collect(formula, &allowed, 0, &mut remaining, &mut used)?;
    if !matches!(
        crate::pdr::validate_qf_expression(problem, vars, formula),
        Ok(ChcSort::Bool)
    ) {
        return None;
    }
    Some(crate::expr::MAX_PREPROCESSING_NODES - remaining)
}

#[cfg(test)]
pub(super) fn exact_scalar_walk(
    expr: &ChcExpr,
    allowed: &FxHashSet<ChcVar>,
    depth: usize,
    remaining: &mut usize,
) -> Option<()> {
    exact_scalar_walk_collect(expr, allowed, depth, remaining, &mut FxHashSet::default())
}

fn charge_controlled(remaining: &mut usize, stopped: &mut dyn FnMut() -> bool) -> Option<()> {
    if *remaining == 0 || stopped() {
        return None;
    }
    *remaining -= 1;
    Some(())
}

fn exact_scalar_walk_collect(
    expr: &ChcExpr,
    allowed: &FxHashSet<ChcVar>,
    depth: usize,
    remaining: &mut usize,
    used: &mut FxHashSet<ChcVar>,
) -> Option<()> {
    exact_scalar_walk_collect_controlled(expr, allowed, depth, remaining, used, &mut || false)
}

fn exact_scalar_walk_collect_controlled(
    expr: &ChcExpr,
    allowed: &FxHashSet<ChcVar>,
    depth: usize,
    remaining: &mut usize,
    used: &mut FxHashSet<ChcVar>,
    stopped: &mut dyn FnMut() -> bool,
) -> Option<()> {
    if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    charge_controlled(remaining, stopped)?;
    crate::expr::maybe_grow_expr_stack(|| {
        if matches!(expr.sort(), ChcSort::Array(_, _) | ChcSort::Datatype { .. }) {
            return None;
        }
        match expr {
            ChcExpr::ArrayLambda(_) => return None,
            ChcExpr::Var(var)
                if allowed.contains(var) && !matches!(var.sort, ChcSort::Array(_, _)) =>
            {
                used.insert(var.clone());
            }
            ChcExpr::Var(_) => return None,
            ChcExpr::Op(ChcOp::Select | ChcOp::Store, _)
            | ChcExpr::PredicateApp(_, _, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
            | ChcExpr::ConstArray(_, _) => return None,
            ChcExpr::Real(_, denominator) if *denominator <= 0 => return None,
            ChcExpr::FuncApp(_, _, _) => return None,
            ChcExpr::Op(_, args) => {
                for arg in args {
                    exact_scalar_walk_collect_controlled(
                        arg,
                        allowed,
                        depth + 1,
                        remaining,
                        used,
                        stopped,
                    )?;
                }
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {}
        }
        Some(())
    })
}
