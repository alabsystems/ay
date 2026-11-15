// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reproduce the captured consumer's one-level ReachFact composition, not
//! reachability search. Consumer 4b18310a33a75fde702bfd3dd8c733eaebd1d0de,
//! model-checker-consumer-driver/src/call_ay/chc/native_nullary.rs, appends each fact's
//! constraint, each ordered body/head equality, then the clause constraint.
//! Only a unique earlier source fact is reconstructible without a selected
//! predecessor ledger. Ambiguous, recursive or later definitions still refuse.
//! The caller additionally authenticates the COMPLETE resulting query bytes.

use super::*;
use ay_chc::{ChcExpr, ClauseHead, PredicateId};

pub(super) enum Recipe {
    Ready {
        formula: ChcExpr,
        predecessors: Vec<usize>,
    },
    Missing,
    Stopped,
}

pub(super) fn reconstruct(
    problem: &ChcProblem,
    index: usize,
    progress: &mut dyn FnMut() -> bool,
) -> Result<Recipe> {
    if !progress() {
        return Ok(Recipe::Stopped);
    }
    let clause = problem
        .clauses()
        .get(index)
        .ok_or_else(|| BenchError::msg("R34 witness clause is absent"))?;
    let mut constraints = Vec::new();
    let mut predecessors = Vec::new();
    for (predicate, body_args) in &clause.body.predicates {
        let fact_index = match unique_fact(problem, *predicate, index, progress) {
            Ok(Some(index)) => index,
            Ok(None) => return Ok(Recipe::Missing),
            Err(()) => return Ok(Recipe::Stopped),
        };
        let fact = &problem.clauses()[fact_index];
        let ClauseHead::Predicate(_, fact_args) = &fact.head else {
            return Ok(Recipe::Missing);
        };
        let declared = problem
            .get_predicate(*predicate)
            .ok_or_else(|| BenchError::msg("R34 witness predicate declaration missing"))?;
        if body_args.len() != fact_args.len() || body_args.len() != declared.arg_sorts.len() {
            return Ok(Recipe::Missing);
        }
        if !progress() {
            return Ok(Recipe::Stopped);
        }
        constraints.extend(fact.body.constraint.iter().cloned());
        for ((body_arg, fact_arg), sort) in body_args.iter().zip(fact_args).zip(&declared.arg_sorts)
        {
            if !progress() {
                return Ok(Recipe::Stopped);
            }
            if body_arg.sort() != *sort || fact_arg.sort() != *sort {
                return Ok(Recipe::Missing);
            }
            // Do not replace equal names with true or erase the equality here:
            // the actual typed AST and argument order feed the consumer recipe.
            constraints.push(ChcExpr::eq(body_arg.clone(), fact_arg.clone()));
        }
        predecessors.push(fact_index);
    }
    if !progress() {
        return Ok(Recipe::Stopped);
    }
    constraints.extend(clause.body.constraint.iter().cloned());
    Ok(Recipe::Ready {
        formula: ChcExpr::and_all(constraints),
        predecessors,
    })
}

fn unique_fact(
    problem: &ChcProblem,
    predicate: PredicateId,
    before: usize,
    progress: &mut dyn FnMut() -> bool,
) -> std::result::Result<Option<usize>, ()> {
    let mut found = None;
    for (index, clause) in problem.clauses().iter().enumerate() {
        if !progress() {
            return Err(());
        }
        if matches!(&clause.head, ClauseHead::Predicate(id, _) if *id == predicate) {
            if found.is_some() || index >= before || !clause.body.predicates.is_empty() {
                return Ok(None);
            }
            found = Some(index);
        }
    }
    Ok(found)
}
