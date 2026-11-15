// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Legacy substitution/collection/dependency bodies from the parent revision.

use super::*;
use ay_core::kani_compat::DetHashSet;

pub(super) fn substitute(conjuncts: &mut Vec<ChcExpr>) -> usize {
    let max_rounds = conjuncts.len().saturating_add(1).min(1024);
    let mut total_changed = 0usize;
    for _ in 0..max_rounds {
        let subst = collect(conjuncts);
        if subst.is_empty() {
            break;
        }
        let old = std::mem::take(conjuncts);
        let mut out = Vec::with_capacity(old.len());
        let mut changed = false;
        for conjunct in old {
            let substituted = BmcSolver::simplify_bmc_expr(conjunct.substitute_name_map(&subst));
            if substituted != conjunct {
                changed = true;
                total_changed += 1;
            }
            match substituted {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => {
                    conjuncts.clear();
                    conjuncts.push(ChcExpr::Bool(false));
                    return total_changed;
                }
                other => out.push(other),
            }
        }
        *conjuncts = out;
        if !changed {
            break;
        }
    }
    total_changed
}

fn collect(conjuncts: &[ChcExpr]) -> FxHashMap<String, ChcExpr> {
    let mut candidates: FxHashMap<String, Option<ChcExpr>> = FxHashMap::default();
    for conjunct in conjuncts {
        let simplified = BmcSolver::simplify_bmc_expr(conjunct.clone());
        let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let Some((name, expr)) =
            BmcSolver::orient_definitional_equality(args[0].as_ref(), args[1].as_ref())
        else {
            continue;
        };
        if expr.vars().iter().any(|var| var.name == name) || expr.node_count(4096) >= 4096 {
            continue;
        }
        match candidates.get_mut(&name) {
            Some(slot) if slot.as_ref() == Some(&expr) => {}
            Some(slot) => *slot = None,
            None => {
                candidates.insert(name, Some(expr));
            }
        }
    }
    let mut subst: FxHashMap<String, ChcExpr> = candidates
        .into_iter()
        .filter_map(|(name, expr)| expr.map(|expr| (name, expr)))
        .collect();
    let keys: Vec<_> = subst.keys().cloned().collect();
    for name in keys {
        let remove = subst
            .get(&name)
            .is_some_and(|expr| depends_on(&name, expr, &subst, &mut DetHashSet::default()));
        if remove {
            subst.remove(&name);
        }
    }
    subst
}

fn depends_on(
    name: &str,
    expr: &ChcExpr,
    subst: &FxHashMap<String, ChcExpr>,
    visiting: &mut DetHashSet<String>,
) -> bool {
    for var in expr.vars() {
        if var.name == name {
            return true;
        }
        if let Some(next) = subst.get(&var.name) {
            if visiting.insert(var.name.clone()) {
                if depends_on(name, next, subst, visiting) {
                    return true;
                }
                visiting.remove(&var.name);
            }
        }
    }
    false
}
