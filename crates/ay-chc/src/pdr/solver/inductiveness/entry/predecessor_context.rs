// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::{fact_names::SourceNames, PdrSolver};
use crate::{ChcExpr, HornClause, PredicateId};

#[cfg(test)]
#[path = "predecessor_context/tests.rs"]
mod tests;

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

/// The body context of an entry check at prev_level 0 for body position
/// `occurrence` of the entry clause.
///
/// The level-0 must-summary keeps its fact's local variables, renamed apart
/// from every source clause at construction (`init_must_summaries_from_facts`).
/// Two body positions of the SAME predicate would still share those locals,
/// so every position after the first gets them freshened
/// (`{name}__o{occurrence}`, `freshen_locals`): otherwise the two copies of
/// the existential init locals would be equated and the entry query
/// over-constrained (a spurious "entry-inductive").
pub(super) fn push_prev_level_zero_body_context(
    solver: &PdrSolver,
    conjuncts: &mut Vec<ChcExpr>,
    body_pred: PredicateId,
    body_args: &[ChcExpr],
    occurrence: usize,
) {
    // At prev_level 0 use must-summary (init + loop-closure) to avoid vacuous UNSAT.
    if let Some(must_summary) = solver.reachability.must_summaries.get(0, body_pred) {
        let must_summary = freshen_locals(solver, body_pred, &must_summary, occurrence);
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
        // Fact joins are appended after all fixed contexts are present, so
        // fresh names are checked against later bodies' frame/summary names.
        // #1391: retain frame[1] strengthening in fallback path.
        if solver.frames.len() > 1 {
            push_prev_level_frame_context(solver, conjuncts, body_pred, body_args, 1);
        }
    }
}

/// Rename the non-canonical variables of a canonical-state formula of `pred`
/// with the suffix `__o{occurrence}` (occurrence 0 keeps its names). The
/// summary's locals already carry a fresh, source-unique allocation
/// (`fact_names::SourceNames`), so suffixing it cannot meet a source name.
fn freshen_locals(
    solver: &PdrSolver,
    pred: PredicateId,
    formula: &ChcExpr,
    occurrence: usize,
) -> ChcExpr {
    if occurrence == 0 {
        return formula.clone();
    }
    let canonical: Vec<&str> = solver
        .canonical_vars(pred)
        .map(|vars| vars.iter().map(|v| v.name.as_str()).collect())
        .unwrap_or_default();
    let subst: Vec<(crate::ChcVar, ChcExpr)> = formula
        .vars()
        .into_iter()
        .filter(|v| !canonical.contains(&v.name.as_str()))
        .map(|v| {
            let fresh = crate::ChcVar::new(format!("{}__o{occurrence}", v.name), v.sort.clone());
            (v, ChcExpr::var(fresh))
        })
        .collect();
    if subst.is_empty() {
        formula.clone()
    } else {
        formula.substitute(&subst)
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

pub(super) fn append_fact_fallbacks(
    solver: &PdrSolver,
    conjuncts: &mut Vec<ChcExpr>,
    clause_index: usize,
    clause: &HornClause,
) -> Option<()> {
    let mut names = None;
    let mut fact_contexts = Vec::new();
    for (body_index, (body_pred, body_args)) in clause.body.predicates.iter().enumerate() {
        if solver
            .reachability
            .must_summaries
            .get(0, *body_pred)
            .is_some()
            || !solver.predicate_has_facts(*body_pred)
        {
            continue;
        }
        if names.is_none() {
            // #lvl1-repeat: cached per-solver census (`source_names()`)
            // instead of a fresh `SourceNames::collect` walk — this runs once
            // per (clause, no-summary/no-fact body position) during entry
            // checks, which PDR revisits constantly; an uncached walk here
            // re-paid the full-problem census on every entry check.
            names = Some(solver.source_names()?);
        }
        let mut query_roots: Vec<_> = conjuncts.iter().chain(&fact_contexts).collect();
        for (_, args) in &clause.body.predicates {
            query_roots.extend(args);
        }
        if let crate::ClauseHead::Predicate(_, args) = &clause.head {
            query_roots.extend(args);
        }
        let facts = build_fact_fallback_disjunction(
            solver,
            names.as_ref()?,
            (clause_index, body_index),
            *body_pred,
            body_args,
            &query_roots,
        )?;
        fact_contexts.push(facts);
    }
    conjuncts.extend(fact_contexts);
    Some(())
}

fn build_fact_fallback_disjunction(
    solver: &PdrSolver,
    names: &SourceNames,
    join: (usize, usize),
    body_pred: PredicateId,
    body_args: &[ChcExpr],
    query_roots: &[&ChcExpr],
) -> Option<ChcExpr> {
    let mut fact_disjuncts: Vec<ChcExpr> = Vec::new();
    for (fact_idx, fact) in solver
        .problem
        .clauses_defining_with_index(body_pred)
        .filter(|(_, fact)| fact.is_fact())
    {
        let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let fact_head_args = match &fact.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => return None,
        };
        if fact_head_args.len() != body_args.len() {
            return None;
        }

        // Occurrences, not merely predicates or facts, own independent locals.
        // A single source census covers this whole admission query; earlier
        // generated contexts are checked too. Refusal must not omit a fact.
        let prefix = format!("__entry_fact_{}_{}_{fact_idx}_", join.0, join.1);
        let (renamed_fact_constraint, renamed_fact_args) = names.rename(
            &fact_constraint,
            fact_head_args,
            &prefix,
            query_roots.iter().copied().chain(fact_disjuncts.iter()),
            &mut || !solver.is_cancelled(),
        )?;

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

    Some(ChcExpr::or_all(fact_disjuncts))
}
