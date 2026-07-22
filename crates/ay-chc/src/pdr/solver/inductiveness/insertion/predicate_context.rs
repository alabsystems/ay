// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, ChcSort, ChcVar, FxHashMap, FxHashSet, PdrSolver, PredicateId};

pub(super) fn rename_fact_variables(
    fact_constraint: &ChcExpr,
    fact_head_args: &[ChcExpr],
    prefix: &str,
) -> (ChcExpr, Vec<ChcExpr>) {
    let mut all_vars: FxHashMap<String, ChcSort> = FxHashMap::default();
    for var in fact_constraint.vars() {
        all_vars.insert(var.name.clone(), var.sort.clone());
    }
    for arg in fact_head_args {
        for var in arg.vars() {
            all_vars.insert(var.name.clone(), var.sort.clone());
        }
    }

    let subst: Vec<(ChcVar, ChcExpr)> = all_vars
        .into_iter()
        .map(|(name, sort)| {
            let old_var = ChcVar {
                name: name.clone(),
                sort: sort.clone(),
            };
            let new_var = ChcVar {
                name: format!("{prefix}{name}"),
                sort,
            };
            (old_var, ChcExpr::var(new_var))
        })
        .collect();

    let renamed_constraint = fact_constraint.substitute(&subst);
    let renamed_args: Vec<ChcExpr> = fact_head_args
        .iter()
        .map(|arg| arg.substitute(&subst))
        .collect();

    (renamed_constraint, renamed_args)
}

pub(super) fn predicate_has_facts(solver: &PdrSolver, pred: PredicateId) -> bool {
    solver.caches.predicates_with_facts.contains(&pred)
}

pub(super) fn predicate_is_reachable(solver: &PdrSolver, pred: PredicateId) -> bool {
    solver.caches.reachable_predicates.contains(&pred)
}

pub(super) fn has_unrestricted_incoming_inter_predicate_transitions(
    solver: &PdrSolver,
    pred: PredicateId,
) -> bool {
    for clause in solver.problem.clauses_defining(pred) {
        if clause.body.predicates.is_empty() || clause.body.predicates.len() != 1 {
            continue;
        }

        let (body_pred, body_args) = &clause.body.predicates[0];
        if *body_pred == pred {
            continue;
        }

        let is_trivial = clause
            .body
            .constraint
            .as_ref()
            .is_none_or(|c| matches!(c, ChcExpr::Bool(true)));
        if !is_trivial {
            continue;
        }

        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, args) => args,
            crate::ClauseHead::False => continue,
        };

        let body_var_names: FxHashSet<String> = body_args
            .iter()
            .flat_map(|b| b.vars().into_iter().map(|v| v.name))
            .collect();
        let is_identity_like = head_args.iter().all(|h_arg| {
            let vars = h_arg.vars();
            !vars.is_empty() && vars.iter().all(|v| body_var_names.contains(&v.name))
        });

        if is_identity_like {
            return true;
        }
    }
    false
}

pub(super) fn has_any_incoming_inter_predicate_transitions(
    solver: &PdrSolver,
    pred: PredicateId,
) -> bool {
    for clause in solver.problem.clauses_defining(pred) {
        if clause.body.predicates.is_empty() {
            continue;
        }

        for (body_pred, _) in &clause.body.predicates {
            if *body_pred != pred {
                return true;
            }
        }
    }
    false
}

pub(super) fn rename_to_canonical_vars(
    expr: &ChcExpr,
    name_map: &FxHashMap<String, String>,
) -> ChcExpr {
    expr.rename_vars(name_map)
}
