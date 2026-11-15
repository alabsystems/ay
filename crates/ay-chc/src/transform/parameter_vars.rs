// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture-free model binders for repeated parameter projections.

use ay_core::kani_compat::DetHashSet;

use crate::{ChcExpr, ChcSort, ChcVar, PredicateInterpretation};

fn spend(remaining: &mut usize, amount: usize) -> Option<()> {
    *remaining = remaining.checked_sub(amount)?;
    Some(())
}

/// `vars()` is deliberately depth-truncated and cannot establish freshness.
/// Inspect the complete DAG, including closed lambda templates and term
/// symbols. Exhaustion declines reconstruction instead of returning a prefix
/// of the namespace. This is a local work bound, not a new caller allowance.
fn collect_names(
    expression: &ChcExpr,
    occupied: &mut DetHashSet<String>,
    remaining: &mut usize,
) -> Option<()> {
    let mut pending = vec![expression];
    let mut visited = DetHashSet::default();
    while let Some(node) = pending.pop() {
        spend(remaining, 1)?;
        if !visited.insert(std::ptr::from_ref(node)) {
            continue;
        }
        let name = match node {
            ChcExpr::Var(var) => Some(&var.name),
            ChcExpr::FuncApp(name, ..)
            | ChcExpr::PredicateApp(name, ..)
            | ChcExpr::IsTesterMarker(name) => Some(name),
            _ => None,
        };
        if let Some(name) = name {
            spend(remaining, name.len())?;
            occupied.insert(name.clone());
        }
        let children = crate::expr::dag::children(node);
        spend(remaining, children.len())?;
        if pending.len().checked_add(children.len())? > *remaining {
            return None;
        }
        pending.extend(children.iter().map(AsRef::as_ref));
        if let ChcExpr::ArrayLambda(lambda) = node {
            spend(remaining, 1)?;
            pending.push(lambda.body().as_ref());
        }
    }
    Some(())
}

/// Restore the original positional signature without capturing a name from
/// this interpretation or an earlier projection's reconstructed binders.
/// Malformed model arity/sorts decline reconstruction; original validation
/// must still authenticate every reconstructed interpretation.
pub(super) fn restore(
    interpretation: &PredicateInterpretation,
    original: &[ChcSort],
    kept: &[usize],
    prefix: &str,
) -> Option<Vec<ChcVar>> {
    if interpretation.vars.len() != kept.len() {
        return None;
    }
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    spend(&mut remaining, original.len())?;
    spend(&mut remaining, prefix.len())?;
    let mut occupied = DetHashSet::default();
    for var in &interpretation.vars {
        spend(&mut remaining, var.name.len().checked_add(1)?)?;
        if !occupied.insert(var.name.clone()) {
            return None;
        }
    }
    collect_names(&interpretation.formula, &mut occupied, &mut remaining)?;
    let mut reduced = 0;
    let mut restored = Vec::with_capacity(original.len());
    for (position, sort) in original.iter().enumerate() {
        if kept.get(reduced) == Some(&position) {
            let var = interpretation.vars.get(reduced)?;
            if &var.sort != sort {
                return None;
            }
            spend(&mut remaining, var.name.len())?;
            restored.push(var.clone());
            reduced += 1;
        } else {
            // At most N occupied names cannot occupy all N+1 distinct
            // candidates. Keep the explicit bound even for hostile names.
            let mut fresh = None;
            for suffix in 0..=occupied.len() {
                spend(&mut remaining, prefix.len().checked_add(42)?)?;
                let name = format!("{prefix}_{position}_{suffix}");
                if !occupied.contains(&name) {
                    fresh = Some(name);
                    break;
                }
            }
            let name = fresh?;
            occupied.insert(name.clone());
            restored.push(ChcVar::new(name, sort.clone()));
        }
    }
    (reduced == kept.len()).then_some(restored)
}

#[cfg(test)]
mod tests;
