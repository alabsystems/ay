// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, PredicateId};

pub(super) fn push_entry_domain_context(
    solver: &PdrSolver,
    conjuncts: &mut Vec<ChcExpr>,
    body_pred: PredicateId,
    body_args: &[ChcExpr],
    prev_level: usize,
) {
    // #1545/#1398: constrain no-fact phase-chain predicates with entry-domain over-approx.
    if !solver.predicate_has_facts(body_pred) && prev_level > 0 {
        if let Some(entry_domain) = solver.entry_domain_constraint(body_pred, prev_level) {
            if let Some(applied) = solver.apply_to_args(body_pred, &entry_domain, body_args) {
                conjuncts.push(applied);
            }
        }
    }
}

pub(super) fn push_prev_level_zero_body_context(
    solver: &PdrSolver,
    conjuncts: &mut Vec<ChcExpr>,
    body_pred: PredicateId,
    body_args: &[ChcExpr],
) {
    // At prev_level 0 use must-summary (init + loop-closure) to avoid vacuous UNSAT.
    if let Some(must_summary) = solver.reachability.must_summaries.get(0, body_pred) {
        if let Some(applied) = solver.apply_to_args(body_pred, &must_summary, body_args) {
            conjuncts.push(applied);
        }
        // #1391: frame[1] may contain stronger inductive bounds than must-summary.
        if solver.frames.len() > 1 {
            push_prev_level_frame_context(solver, conjuncts, body_pred, body_args, 1);
        }
    } else if !solver.predicate_has_facts(body_pred) {
        // No must-summary and no facts: unreachable predecessor
        conjuncts.push(ChcExpr::Bool(false));
    } else {
        // Fallback when must-summary is unavailable.
        let facts_on_body = build_fact_fallback_disjunction(solver, body_pred, body_args);
        conjuncts.push(facts_on_body);

        // #1391: retain frame[1] strengthening in fallback path.
        if solver.frames.len() > 1 {
            push_prev_level_frame_context(solver, conjuncts, body_pred, body_args, 1);
        }
    }
}

pub(super) fn push_prev_level_frame_context(
    solver: &PdrSolver,
    conjuncts: &mut Vec<ChcExpr>,
    body_pred: PredicateId,
    body_args: &[ChcExpr],
    frame_level: usize,
) {
    let frame_constraint = solver.frames[frame_level]
        .get_predicate_constraint(body_pred)
        .unwrap_or(ChcExpr::Bool(true));
    if let Some(applied) = solver.apply_to_args(body_pred, &frame_constraint, body_args) {
        conjuncts.push(applied);
    }
}

pub(super) fn build_fact_fallback_disjunction(
    solver: &PdrSolver,
    body_pred: PredicateId,
    body_args: &[ChcExpr],
) -> ChcExpr {
    let mut fact_disjuncts: Vec<ChcExpr> = Vec::new();
    for (fact_idx, fact) in solver
        .problem
        .facts()
        .filter(|f| f.head.predicate_id() == Some(body_pred))
        .enumerate()
    {
        let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let fact_head_args = match &fact.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => continue,
        };
        if fact_head_args.len() != body_args.len() {
            continue;
        }

        let prefix = format!("__entry_fact_{fact_idx}_");
        let (renamed_fact_constraint, renamed_fact_args) =
            PdrSolver::rename_fact_variables(&fact_constraint, fact_head_args, &prefix);

        let eqs: Vec<ChcExpr> = body_args
            .iter()
            .cloned()
            .zip(renamed_fact_args)
            .map(|(a, b)| ChcExpr::eq(a, b))
            .collect();

        fact_disjuncts.push(ChcExpr::and_all([
            renamed_fact_constraint,
            ChcExpr::and_all(eqs),
        ]));
    }

    ChcExpr::or_all(fact_disjuncts)
}
