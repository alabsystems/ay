// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Legacy literal-substitution orchestration from the same revision as parent.

use super::*;

pub(super) fn substitute(
    conjuncts: &mut Vec<ChcExpr>,
    env: &FxHashMap<String, IntInterval>,
) -> usize {
    let subst: FxHashMap<String, ChcExpr> = env
        .iter()
        .filter_map(|(name, interval)| match (interval.lower, interval.upper) {
            (Some(lower), Some(upper)) if lower == upper => {
                Some((name.clone(), ChcExpr::Int(lower)))
            }
            _ => None,
        })
        .collect();
    if subst.is_empty() {
        return 0;
    }
    let old = std::mem::take(conjuncts);
    let mut changed = 0usize;
    let mut out = Vec::with_capacity(old.len());
    for conjunct in old {
        let simplified = BmcSolver::simplify_bmc_expr(conjunct.substitute_name_map(&subst));
        if simplified != conjunct {
            changed += 1;
        }
        match simplified {
            ChcExpr::Bool(true) => {}
            ChcExpr::Bool(false) => {
                conjuncts.clear();
                conjuncts.push(ChcExpr::Bool(false));
                return changed;
            }
            other => out.push(other),
        }
    }
    *conjuncts = out;
    changed
}
