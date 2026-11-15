// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Frozen 0883923f8 definitional round/candidate/dependency algorithm.
//! Unchanged pure orientation and expression simplification remain shared.

use super::*;

pub(super) fn substitute(conjuncts: &mut Vec<ChcExpr>) -> usize {
    let max_rounds = conjuncts.len().saturating_add(1).min(1024);
    let mut total_changed = 0usize;
    for _ in 0..max_rounds {
        let substitutions = collect(conjuncts);
        if substitutions.is_empty() {
            break;
        }
        let old = std::mem::take(conjuncts);
        let mut output = Vec::with_capacity(old.len());
        let mut changed = false;
        for conjunct in old {
            let replaced =
                BmcSolver::simplify_bmc_expr(conjunct.substitute_name_map(&substitutions));
            if replaced != conjunct {
                changed = true;
                total_changed += 1;
            }
            match replaced {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => {
                    conjuncts.clear();
                    conjuncts.push(ChcExpr::Bool(false));
                    return total_changed;
                }
                other => output.push(other),
            }
        }
        *conjuncts = output;
        if !changed {
            break;
        }
    }
    total_changed
}

pub(super) fn collect(conjuncts: &[ChcExpr]) -> DetHashMap<String, ChcExpr> {
    let mut candidates: DetHashMap<String, Option<ChcExpr>> = DetHashMap::default();
    for conjunct in conjuncts {
        let simplified = BmcSolver::simplify_bmc_expr(conjunct.clone());
        let ChcExpr::Op(ChcOp::Eq, arguments) = &simplified else {
            continue;
        };
        if arguments.len() != 2 {
            continue;
        }
        let Some((name, expression)) =
            BmcSolver::orient_definitional_equality(arguments[0].as_ref(), arguments[1].as_ref())
        else {
            continue;
        };
        if BmcSolver::expr_mentions_var(&expression, &name) || expression.node_count(4096) >= 4096 {
            continue;
        }
        match candidates.get_mut(&name) {
            Some(slot) if slot.as_ref() == Some(&expression) => {}
            Some(slot) => *slot = None,
            None => {
                candidates.insert(name, Some(expression));
            }
        }
    }
    let mut substitutions: DetHashMap<String, ChcExpr> = candidates
        .into_iter()
        .filter_map(|(name, expression)| expression.map(|expression| (name, expression)))
        .collect();
    let keys: Vec<_> = substitutions.keys().cloned().collect();
    for name in keys {
        let remove = substitutions.get(&name).is_some_and(|expression| {
            depends_on(
                &name,
                expression,
                &substitutions,
                &mut DetHashSet::default(),
            )
        });
        if remove {
            substitutions.remove(&name);
        }
    }
    substitutions
}

fn depends_on(
    name: &str,
    expression: &ChcExpr,
    substitutions: &DetHashMap<String, ChcExpr>,
    visiting: &mut DetHashSet<String>,
) -> bool {
    for variable in expression.vars() {
        if variable.name == name {
            return true;
        }
        if let Some(next) = substitutions.get(&variable.name) {
            if visiting.insert(variable.name.clone()) {
                if depends_on(name, next, substitutions, visiting) {
                    return true;
                }
                visiting.remove(&variable.name);
            }
        }
    }
    false
}
