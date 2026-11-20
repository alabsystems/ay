// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause-level ART path encoding for LAWI refinement.
//!
//! Golem's LAWI checks the concrete ART path by asserting the selected edge
//! formulas, not the whole transition relation. This module mirrors that
//! behavior for AY's single-predicate transition-system encoding.

use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcVar, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet as FxHashSet;

pub(crate) fn art_edge_formula_at(
    ts: &TransitionSystem,
    problem: &ChcProblem,
    clause_idx: usize,
    step: usize,
) -> Option<ChcExpr> {
    let clause = problem.clauses().get(clause_idx)?;
    match &clause.head {
        ClauseHead::Predicate(_, _) => {
            let formula = translate_transition_clause(ts, clause, clause_idx)?;
            Some(version_transition_expr_at(ts, &formula, step))
        }
        ClauseHead::False => {
            let formula = translate_query_clause(ts, clause, clause_idx)?;
            Some(version_state_expr_at(ts, &formula, step, "q"))
        }
    }
}

fn translate_transition_clause(
    ts: &TransitionSystem,
    clause: &HornClause,
    clause_idx: usize,
) -> Option<ChcExpr> {
    let (body_pred, body_args) = clause.body.predicates.first()?;
    if *body_pred != ts.predicate {
        return None;
    }

    let head_args = match &clause.head {
        ClauseHead::Predicate(pred, args) if *pred == ts.predicate => args,
        _ => return None,
    };

    let canonical_vars = canonical_arg_vars(ts, body_args.len())?;
    let next_vars: Vec<ChcVar> = canonical_vars
        .iter()
        .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
        .collect();
    if head_args.len() != next_vars.len() {
        return None;
    }

    let constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    Some(TransitionSystem::canonicalize_clause_constraint(
        &constraint,
        (body_args, &canonical_vars),
        Some((head_args, &next_vars)),
        &format!("__lawi_tr{clause_idx}_"),
    ))
}

fn translate_query_clause(
    ts: &TransitionSystem,
    clause: &HornClause,
    clause_idx: usize,
) -> Option<ChcExpr> {
    let (body_pred, body_args) = clause.body.predicates.first()?;
    if *body_pred != ts.predicate {
        return None;
    }

    let canonical_vars = canonical_arg_vars(ts, body_args.len())?;
    let constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    Some(TransitionSystem::canonicalize_clause_constraint(
        &constraint,
        (body_args, &canonical_vars),
        None,
        &format!("__lawi_qry{clause_idx}_"),
    ))
}

fn canonical_arg_vars(ts: &TransitionSystem, arity: usize) -> Option<Vec<ChcVar>> {
    let vars = ts.state_vars();
    if vars.len() < arity {
        return None;
    }
    Some(vars[..arity].to_vec())
}

fn version_transition_expr_at(ts: &TransitionSystem, expr: &ChcExpr, step: usize) -> ChcExpr {
    let mut substitutions: Vec<_> = ts
        .state_vars()
        .iter()
        .map(|v| {
            (
                v.clone(),
                ChcExpr::var(TransitionSystem::version_var(v, step)),
            )
        })
        .collect();

    let mut canonical_names: FxHashSet<String> =
        ts.state_vars().iter().map(|v| v.name.clone()).collect();
    for v in ts.state_vars() {
        let next_var = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
        canonical_names.insert(next_var.name.clone());
        substitutions.push((
            next_var,
            ChcExpr::var(TransitionSystem::version_var(v, step + 1)),
        ));
        canonical_names.insert(TransitionSystem::version_var(v, step).name);
        canonical_names.insert(TransitionSystem::version_var(v, step + 1).name);
    }

    for v in expr.vars() {
        if !canonical_names.contains(&v.name) {
            let versioned = ChcVar::new(format!("{}__t{step}", v.name), v.sort.clone());
            substitutions.push((v, ChcExpr::var(versioned)));
        }
    }

    expr.substitute(&substitutions)
}

fn version_state_expr_at(ts: &TransitionSystem, expr: &ChcExpr, step: usize, tag: &str) -> ChcExpr {
    let versioned = TransitionSystem::version_expr(expr, ts.state_vars(), step);
    version_local_vars(&versioned, ts.state_vars(), None, step, tag)
}

fn version_local_vars(
    expr: &ChcExpr,
    canonical_vars: &[ChcVar],
    next_vars: Option<&[ChcVar]>,
    step: usize,
    tag: &str,
) -> ChcExpr {
    let all_vars = expr.vars();
    let canonical_base_names: FxHashSet<&str> =
        canonical_vars.iter().map(|v| v.name.as_str()).collect();

    let is_canonical = |name: &str| -> bool {
        if canonical_base_names.contains(name) {
            return true;
        }
        if let Some((base, suffix)) = name.rsplit_once('_') {
            if suffix.chars().all(|c| c.is_ascii_digit()) && canonical_base_names.contains(base) {
                return true;
            }
        }
        false
    };

    let substitutions: Vec<(ChcVar, ChcExpr)> = all_vars
        .into_iter()
        .filter(|v| {
            if is_canonical(&v.name) {
                return false;
            }
            if let Some(nvars) = next_vars {
                if nvars.iter().any(|nv| nv.name == v.name) {
                    return false;
                }
            }
            true
        })
        .map(|v| {
            let versioned = ChcVar::new(format!("{}__{tag}{step}", v.name), v.sort.clone());
            (v, ChcExpr::var(versioned))
        })
        .collect();

    if substitutions.is_empty() {
        expr.clone()
    } else {
        expr.substitute(&substitutions)
    }
}
