// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact scalar-variable accounting for query-anchored candidates.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar};

use super::GhostPredSpec;

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
