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

    let constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    let (mut constraint, mut extra_eqs, body_subst) =
        substitute_args_to_canonical_vars(constraint, body_args, &canonical_vars);

    for (i, head_arg) in head_args.iter().enumerate() {
        if let ChcExpr::Var(v) = head_arg {
            if let Some((_, canonical_expr)) = body_subst.iter().find(|(bv, _)| bv == v) {
                extra_eqs.push(ChcExpr::eq(
                    ChcExpr::var(next_vars[i].clone()),
                    canonical_expr.clone(),
                ));
            } else {
                constraint =
                    constraint.substitute(&[(v.clone(), ChcExpr::var(next_vars[i].clone()))]);
            }
        } else {
            let substituted_head_arg = head_arg.substitute(&body_subst);
            extra_eqs.push(ChcExpr::eq(
                ChcExpr::var(next_vars[i].clone()),
                substituted_head_arg,
            ));
        }
    }

    let combined = finalize_constraint(constraint, extra_eqs);
    Some(rename_local_vars(
        combined,
        &canonical_vars,
        Some(&next_vars),
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
    let (constraint, extra_eqs, _) =
        substitute_args_to_canonical_vars(constraint, body_args, &canonical_vars);
    let combined = finalize_constraint(constraint, extra_eqs);
    Some(rename_local_vars(
        combined,
        &canonical_vars,
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

fn substitute_args_to_canonical_vars(
    constraint: ChcExpr,
    args: &[ChcExpr],
    canonical_vars: &[ChcVar],
) -> (ChcExpr, Vec<ChcExpr>, Vec<(ChcVar, ChcExpr)>) {
    let subst_map: Vec<(ChcVar, ChcExpr)> = args
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| {
            if let ChcExpr::Var(v) = arg {
                Some((v.clone(), ChcExpr::var(canonical_vars[i].clone())))
            } else {
                None
            }
        })
        .collect();

    let mut result = constraint;
    let mut extra_eqs = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        if let ChcExpr::Var(v) = arg {
            result = result.substitute(&[(v.clone(), ChcExpr::var(canonical_vars[i].clone()))]);
        } else {
            let substituted_arg = arg.substitute(&subst_map);
            extra_eqs.push(ChcExpr::eq(
                ChcExpr::var(canonical_vars[i].clone()),
                substituted_arg,
            ));
        }
    }

    (result, extra_eqs, subst_map)
}

fn finalize_constraint(constraint: ChcExpr, extra_eqs: Vec<ChcExpr>) -> ChcExpr {
    if extra_eqs.is_empty() {
        constraint
    } else {
        let mut all = extra_eqs;
        all.insert(0, constraint);
        ChcExpr::and_all(all)
    }
}

fn rename_local_vars(
    constraint: ChcExpr,
    canonical_vars: &[ChcVar],
    next_vars: Option<&[ChcVar]>,
    prefix: &str,
) -> ChcExpr {
    let all_vars = constraint.vars();
    let mut canonical_names: FxHashSet<String> =
        canonical_vars.iter().map(|v| v.name.clone()).collect();
    if let Some(nvars) = next_vars {
        for v in nvars {
            canonical_names.insert(v.name.clone());
        }
    }

    let substitutions: Vec<(ChcVar, ChcExpr)> = all_vars
        .into_iter()
        .filter(|v| !canonical_names.contains(&v.name))
        .map(|v| {
            let renamed = ChcVar::new(format!("{prefix}{}", v.name), v.sort.clone());
            (v, ChcExpr::var(renamed))
        })
        .collect();

    if substitutions.is_empty() {
        constraint
    } else {
        constraint.substitute(&substitutions)
    }
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
