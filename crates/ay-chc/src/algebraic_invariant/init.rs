// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{ChcExpr, ChcOp, ChcProblem, ClauseHead, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Extract init values from fact clauses.
pub(super) fn extract_init_values(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
) -> Option<FxHashMap<String, i128>> {
    let mut visiting = FxHashSet::default();
    extract_init_values_inner(problem, pred, pre_vars, &mut visiting)
}

fn extract_init_values_inner(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
    visiting: &mut FxHashSet<PredicateId>,
) -> Option<FxHashMap<String, i128>> {
    if !visiting.insert(pred) {
        return None;
    }

    let result = extract_direct_init_values(problem, pred, pre_vars)
        .or_else(|| extract_transferred_init_values(problem, pred, pre_vars, visiting));
    visiting.remove(&pred);
    result
}

fn extract_direct_init_values(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
) -> Option<FxHashMap<String, i128>> {
    let fact = problem
        .clauses()
        .iter()
        .find(|c| c.is_fact() && c.head.predicate_id() == Some(pred))?;

    let head_args = match &fact.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
    let var_defs = extract_init_var_defs(&constraint);
    let var_values = FxHashMap::default();
    Some(map_head_init_values(
        pre_vars,
        head_args,
        &var_values,
        &var_defs,
    ))
}

fn extract_transferred_init_values(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
    visiting: &mut FxHashSet<PredicateId>,
) -> Option<FxHashMap<String, i128>> {
    let mut best: Option<FxHashMap<String, i128>> = None;

    for clause in problem.clauses().iter().filter(|clause| {
        clause.head.predicate_id() == Some(pred)
            && clause.body.predicates.len() == 1
            && clause.body.predicates[0].0 != pred
    }) {
        let candidate = extract_transfer_clause_init_values(problem, clause, pre_vars, visiting);
        let Some(candidate) = candidate else {
            continue;
        };
        if candidate.len() == pre_vars.len() {
            return Some(candidate);
        }
        if best
            .as_ref()
            .is_none_or(|current| candidate.len() > current.len())
        {
            best = Some(candidate);
        }
    }

    best.filter(|init| !init.is_empty())
}

fn extract_transfer_clause_init_values(
    problem: &ChcProblem,
    clause: &crate::HornClause,
    pre_vars: &[String],
    visiting: &mut FxHashSet<PredicateId>,
) -> Option<FxHashMap<String, i128>> {
    let (source_pred, source_args) = clause.body.predicates.first()?;
    if predicate_has_self_loop(problem, *source_pred) {
        return None;
    }
    let head_args = match &clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let source_slots: Vec<String> = source_args
        .iter()
        .enumerate()
        .map(|(idx, _)| format!("__arg{idx}"))
        .collect();
    let source_values = extract_init_values_inner(problem, *source_pred, &source_slots, visiting)
        .unwrap_or_default();
    let mut var_values = FxHashMap::default();
    for (idx, arg) in source_args.iter().enumerate() {
        let Some(value) = source_values.get(&source_slots[idx]).copied() else {
            continue;
        };
        if let ChcExpr::Var(var) = arg {
            var_values.insert(var.name.clone(), value);
        }
    }

    let constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    let var_defs = extract_init_var_defs(&constraint);
    Some(map_head_init_values(
        pre_vars,
        head_args,
        &var_values,
        &var_defs,
    ))
}

fn predicate_has_self_loop(problem: &ChcProblem, pred: PredicateId) -> bool {
    problem.clauses().iter().any(|clause| {
        clause.head.predicate_id() == Some(pred)
            && clause
                .body
                .predicates
                .iter()
                .any(|(body_pred, _)| *body_pred == pred)
    })
}

fn map_head_init_values(
    pre_vars: &[String],
    head_args: &[ChcExpr],
    var_values: &FxHashMap<String, i128>,
    var_defs: &FxHashMap<String, ChcExpr>,
) -> FxHashMap<String, i128> {
    let mut init = FxHashMap::default();
    for (i, pre_var) in pre_vars.iter().enumerate() {
        if let Some(head_arg) = head_args.get(i) {
            if let Some(value) =
                eval_init_int_expr(head_arg, var_values, var_defs, &mut FxHashSet::default())
            {
                init.insert(pre_var.clone(), value);
            }
        }
    }
    init
}

fn extract_init_var_defs(expr: &ChcExpr) -> FxHashMap<String, ChcExpr> {
    let mut var_defs = FxHashMap::default();
    for conj in expr.conjuncts() {
        let ChcExpr::Op(ChcOp::Eq, args) = conj else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        maybe_add_init_var_def(&mut var_defs, args[0].as_ref(), args[1].as_ref());
        maybe_add_init_var_def(&mut var_defs, args[1].as_ref(), args[0].as_ref());
    }
    var_defs
}

fn maybe_add_init_var_def(var_defs: &mut FxHashMap<String, ChcExpr>, lhs: &ChcExpr, rhs: &ChcExpr) {
    let ChcExpr::Var(var) = lhs else {
        return;
    };
    if rhs.vars().iter().any(|rhs_var| rhs_var.name == var.name) {
        return;
    }
    var_defs
        .entry(var.name.clone())
        .or_insert_with(|| rhs.clone());
}

fn eval_init_int_expr(
    expr: &ChcExpr,
    var_values: &FxHashMap<String, i128>,
    var_defs: &FxHashMap<String, ChcExpr>,
    resolving: &mut FxHashSet<String>,
) -> Option<i128> {
    match expr {
        ChcExpr::Int(value) => Some(*value),
        ChcExpr::Var(var) => {
            if let Some(value) = var_values.get(&var.name) {
                return Some(*value);
            }
            if !resolving.insert(var.name.clone()) {
                return None;
            }
            let result = var_defs
                .get(&var.name)
                .and_then(|def| eval_init_int_expr(def, var_values, var_defs, resolving));
            resolving.remove(&var.name);
            result
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut acc = 0i128;
            for arg in args {
                acc = acc.checked_add(eval_init_int_expr(
                    arg.as_ref(),
                    var_values,
                    var_defs,
                    resolving,
                )?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut iter = args.iter();
            let first = eval_init_int_expr(iter.next()?.as_ref(), var_values, var_defs, resolving)?;
            if args.len() == 1 {
                return first.checked_neg();
            }
            let mut acc = first;
            for arg in iter {
                acc = acc.checked_sub(eval_init_int_expr(
                    arg.as_ref(),
                    var_values,
                    var_defs,
                    resolving,
                )?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut acc = 1i128;
            for arg in args {
                acc = acc.checked_mul(eval_init_int_expr(
                    arg.as_ref(),
                    var_values,
                    var_defs,
                    resolving,
                )?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => crate::expr::smt_euclid_div(
            eval_init_int_expr(args[0].as_ref(), var_values, var_defs, resolving)?,
            eval_init_int_expr(args[1].as_ref(), var_values, var_defs, resolving)?,
        ),
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => crate::expr::smt_euclid_mod(
            eval_init_int_expr(args[0].as_ref(), var_values, var_defs, resolving)?,
            eval_init_int_expr(args[1].as_ref(), var_values, var_defs, resolving)?,
        ),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            eval_init_int_expr(args[0].as_ref(), var_values, var_defs, resolving)?.checked_neg()
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let branch = if eval_init_bool_expr(args[0].as_ref(), var_values, var_defs, resolving)?
            {
                args[1].as_ref()
            } else {
                args[2].as_ref()
            };
            eval_init_int_expr(branch, var_values, var_defs, resolving)
        }
        _ => expr.simplify_constants().as_i128(),
    }
}

fn eval_init_bool_expr(
    expr: &ChcExpr,
    var_values: &FxHashMap<String, i128>,
    var_defs: &FxHashMap<String, ChcExpr>,
    resolving: &mut FxHashSet<String>,
) -> Option<bool> {
    match expr {
        ChcExpr::Bool(value) => Some(*value),
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => Some(!eval_init_bool_expr(
            args[0].as_ref(),
            var_values,
            var_defs,
            resolving,
        )?),
        ChcExpr::Op(ChcOp::And, args) => {
            for arg in args {
                if !eval_init_bool_expr(arg.as_ref(), var_values, var_defs, resolving)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        ChcExpr::Op(ChcOp::Or, args) => {
            for arg in args {
                if eval_init_bool_expr(arg.as_ref(), var_values, var_defs, resolving)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Ne), args) if args.len() == 2 => {
            let lhs = eval_init_int_expr(args[0].as_ref(), var_values, var_defs, resolving)?;
            let rhs = eval_init_int_expr(args[1].as_ref(), var_values, var_defs, resolving)?;
            Some((lhs == rhs) ^ matches!(*op, ChcOp::Ne))
        }
        ChcExpr::Op(op @ (ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge), args)
            if args.len() == 2 =>
        {
            let lhs = eval_init_int_expr(args[0].as_ref(), var_values, var_defs, resolving)?;
            let rhs = eval_init_int_expr(args[1].as_ref(), var_values, var_defs, resolving)?;
            Some(match op {
                ChcOp::Lt => lhs < rhs,
                ChcOp::Le => lhs <= rhs,
                ChcOp::Gt => lhs > rhs,
                ChcOp::Ge => lhs >= rhs,
                _ => unreachable!(),
            })
        }
        _ => None,
    }
}
