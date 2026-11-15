// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, FxHashMap, FxHashSet, PdrSolver, PredicateId};

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
