// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reserve substitution growth against the SAME allowance as the analysis.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::{ChcExpr, ChcVar, ClauseHead, HornClause, PredicateId};

use super::ground::{Budget, Stopped, MAX_DEPTH};

pub(super) fn substitutions(
    clause: &HornClause,
    consts: &FxHashMap<PredicateId, Vec<(usize, ChcExpr)>>,
    budget: &mut Budget,
) -> Result<Vec<(ChcVar, ChcExpr)>, Stopped> {
    let mut seen = FxHashSet::default();
    let mut subst = Vec::new();
    // Head pins are justified by EVERY defining clause, not inferred merely
    // from its output syntax. Retain a matching guard for each certificate.
    let occurrences = clause
        .body
        .predicates
        .iter()
        .map(|(predicate, arguments)| (predicate, arguments))
        .chain(
            match &clause.head {
                ClauseHead::Predicate(predicate, arguments) => Some((predicate, arguments)),
                ClauseHead::False => None,
            }
            .into_iter(),
        );
    for (pid, args) in occurrences {
        budget.charge(args.len() + 1)?;
        let Some(positions) = consts.get(pid) else {
            continue;
        };
        for (index, value) in positions {
            budget.charge(1)?;
            if let Some(ChcExpr::Var(var)) = args.get(*index) {
                budget.charge(var.name.len() + 1)?;
                if seen.insert(var) {
                    subst.push((var.clone(), value.clone()));
                }
            }
        }
    }
    Ok(subst)
}

/// Unlike the general node_count helper, reject depth exhaustion instead of
/// silently undercounting the unvisited suffix. Account before stack growth.
fn count(expr: &ChcExpr, limit: usize, budget: &mut Budget) -> Result<usize, Stopped> {
    let mut pending = vec![(expr, 0usize)];
    let mut count = 0;
    while let Some((expr, depth)) = pending.pop() {
        budget.charge(1)?;
        if count >= limit || depth >= MAX_DEPTH {
            return Err(budget.stop());
        }
        count += 1;
        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                budget.charge(args.len())?;
                if args.len() > limit.saturating_sub(count) {
                    return Err(budget.stop());
                }
                pending.extend(args.iter().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::ConstArray(_, value) => pending.push((value.as_ref(), depth + 1)),
            ChcExpr::Var(var) => budget.charge(var.name.len())?,
            _ => {}
        }
    }
    Ok(count)
}

pub(super) fn reserve(
    clause: &HornClause,
    subst: &[(ChcVar, ChcExpr)],
    budget: &mut Budget,
) -> Result<(), Stopped> {
    // Each original node can become at most the largest substitution tree.
    // This deliberately overestimates instead of constructing a large tree
    // first and discovering its cost afterwards. The shared rewriters already
    // have their own DAG/depth guards; this bounds cumulative growth here.
    let mut largest = 1;
    let mut pins = 0usize;
    for (var, expr) in subst {
        let nodes = count(expr, 512, budget)?;
        budget.charge(nodes + var.name.len() + 2)?;
        largest = largest.max(nodes);
        pins = pins.checked_add(nodes + 2).ok_or_else(|| budget.stop())?;
    }
    budget.reserve_output(pins)?;
    if let Some(constraint) = &clause.body.constraint {
        let limit = (budget.remaining() / largest).min(200_000);
        let nodes = count(constraint, limit, budget)?;
        let output_nodes = nodes.checked_mul(largest).ok_or_else(|| budget.stop())?;
        budget.reserve_output(output_nodes)?;
    }
    let arguments = clause
        .body
        .predicates
        .iter()
        .flat_map(|(_, args)| args)
        .chain(
            match &clause.head {
                ClauseHead::Predicate(_, arguments) => arguments.as_slice(),
                ClauseHead::False => &[],
            }
            .iter(),
        );
    for argument in arguments {
        let limit = (budget.remaining() / largest).min(200_000);
        let nodes = count(argument, limit, budget)?;
        let output_nodes = nodes.checked_mul(largest).ok_or_else(|| budget.stop())?;
        budget.reserve_output(output_nodes)?;
    }
    Ok(())
}

pub(super) fn reserve_matching_guard(
    argument: &ChcExpr,
    value: &ChcExpr,
    budget: &mut Budget,
) -> Result<(), Stopped> {
    let argument_nodes = count(argument, 200_000, budget)?;
    let value_nodes = count(value, 512, budget)?;
    let nodes = argument_nodes
        .checked_add(value_nodes)
        .and_then(|nodes| nodes.checked_add(2))
        .ok_or_else(|| budget.stop())?;
    budget.reserve_output(nodes)
}
