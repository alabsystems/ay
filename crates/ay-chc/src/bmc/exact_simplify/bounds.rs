// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{simplify_expression, AcyclicNames, BmcSolver, ChcExpr, FxHashMap, IntInterval};

/// Preserve the existing bounded interval fixpoint, with complete expression
/// admission and caller control between conjuncts and equality-graph edges.
pub(super) fn collect_bounds(
    conjuncts: &[ChcExpr],
    env: &mut FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<bool> {
    names.check_all(conjuncts)?;
    let mut simplified = Vec::with_capacity(conjuncts.len());
    for conjunct in conjuncts {
        simplified.push(simplify_expression(conjunct.clone(), names)?);
    }
    names.check_all(&simplified)?;
    let rounds = conjuncts.len().saturating_add(4).clamp(1, 32);
    for _ in 0..rounds {
        names.poll()?;
        let mut next = env.clone();
        let mut equalities = Vec::new();
        for conjunct in &simplified {
            names.poll()?;
            if let Some(equality) = BmcSolver::collect_int_var_equality(conjunct) {
                equalities.push(equality);
            }
            if !BmcSolver::collect_conjunct_interval_bound(conjunct, &mut next) {
                names.poll()?;
                return Some(false);
            }
        }
        if !propagate(&equalities, &mut next, names)? {
            return Some(false);
        }
        names.poll()?;
        if *env == next {
            return Some(true);
        }
        *env = next;
    }
    names.poll()?;
    Some(true)
}

fn propagate(
    equalities: &[(String, String)],
    env: &mut FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<bool> {
    for _ in 0..=equalities.len() {
        names.poll()?;
        let mut changed = false;
        for (lhs, rhs) in equalities {
            names.poll()?;
            let lhs_interval = env.get(lhs).copied();
            let rhs_interval = env.get(rhs).copied();
            let updates = match (lhs_interval, rhs_interval) {
                (Some(lhs_interval), Some(rhs_interval)) => {
                    let merged = lhs_interval.intersect(rhs_interval);
                    if merged.is_empty() {
                        names.poll()?;
                        return Some(false);
                    }
                    [(lhs, Some(merged)), (rhs, Some(merged))]
                }
                (Some(interval), None) if interval.has_bound() => {
                    [(lhs, None), (rhs, Some(interval))]
                }
                (None, Some(interval)) if interval.has_bound() => {
                    [(lhs, Some(interval)), (rhs, None)]
                }
                _ => [(lhs, None), (rhs, None)],
            };
            for (name, interval) in updates {
                if let Some(interval) = interval {
                    let Some(updated) = BmcSolver::add_interval_bound_changed(env, name, interval)
                    else {
                        names.poll()?;
                        return Some(false);
                    };
                    changed |= updated;
                }
            }
        }
        names.poll()?;
        if !changed {
            return Some(true);
        }
    }
    Some(true)
}

#[cfg(test)]
mod tests;
