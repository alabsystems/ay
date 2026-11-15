// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete ground refutation search for the variable-free nullary fragment.
//!
//! # Why this exists
//!
//! [`ChcProblem::query_obligations`](crate::ChcProblem::query_obligations)
//! unfolds a nullary error marker one level, so a propositional safety
//! encoding
//!
//! ```text
//! reached          (fact)
//! reached => error_p0
//! error_p0 => false
//! ```
//!
//! becomes an independent obligation whose refutation is a three-clause ground
//! derivation. Both proof-grade engines DECIDE such an obligation Unsafe, but
//! neither attaches a [`GroundDerivation`], and the only other Unsafe replay
//! export — the single-predicate transition-system trace — cannot encode a
//! two-predicate clause system at all. The refutation is therefore real but
//! carries no evidence any replay consumer can re-check, so it can never be
//! admitted to the Trust full verifier.
//!
//! This module closes that gap at the source: for the fragment where every
//! clause is variable-free and every predicate occurrence is nullary, forward
//! chaining IS the decision procedure, and the chain it walks is exactly a
//! ground derivation. Nothing new is claimed — the derivation is handed to
//! [`super::validate_ground_derivation`], the same fail-closed checker every
//! other producer answers to, and only a derivation that validates is used.
//!
//! # Soundness
//!
//! Search failure is never evidence of safety: `None` simply means the caller
//! keeps its existing behavior. A derivation that this module builds wrongly
//! is REJECTED by the validator, so the worst outcome of a bug here is the
//! status quo. Clauses outside the fragment are skipped rather than
//! interpreted, which can only lose derivations, never invent one.

use super::{
    eval_ground_with_control, GroundDerivation, GroundDerivationError, GroundDerivationStep,
    GroundValidationControl,
};
use crate::clause::{ClauseHead, HornClause};
use crate::smt::SmtValue;
use crate::{ChcProblem, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

// This bounds clauses/rounds, not expression size or aggregate premise work.
// Polls delimit opaque variable collection, evaluation and normalization; they
// do not provide a hard cancellation-latency or process-memory guarantee.
const MAX_GROUND_REFUTATION_CLAUSES: usize = 4096;

fn is_ground_nullary(
    clause: &HornClause,
    control: &mut GroundValidationControl<'_>,
) -> Result<bool, GroundDerivationError> {
    control.poll()?;
    // Retain the cheap arity checks before the opaque variable walk.
    for (_, arguments) in &clause.body.predicates {
        control.poll()?;
        if !arguments.is_empty() {
            return Ok(false);
        }
    }
    if let ClauseHead::Predicate(_, arguments) = &clause.head {
        if !arguments.is_empty() {
            return Ok(false);
        }
    }
    control.poll()?;
    let ground = clause.vars().is_empty();
    control.poll()?;
    Ok(ground)
}

fn constraint_is_ground_true(
    clause: &HornClause,
    control: &mut GroundValidationControl<'_>,
) -> Result<bool, GroundDerivationError> {
    control.poll()?;
    Ok(match &clause.body.constraint {
        None => true,
        Some(constraint) => matches!(
            eval_ground_with_control(constraint, &FxHashMap::default(), control)?,
            Some(SmtValue::Bool(true))
        ),
    })
}

fn usable_clauses(
    problem: &ChcProblem,
    clauses: &[HornClause],
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<Vec<bool>>, GroundDerivationError> {
    control.poll()?;
    if clauses.is_empty() || clauses.len() > MAX_GROUND_REFUTATION_CLAUSES {
        return Ok(None);
    }
    // Preserve the existing short-circuit order of the exactness guard.
    let mut refutable_shape_possible = false;
    for predicate in problem.predicates() {
        control.poll()?;
        if predicate.arg_sorts.is_empty() {
            refutable_shape_possible = true;
            break;
        }
    }
    if !refutable_shape_possible {
        for clause in clauses {
            control.poll()?;
            if matches!(clause.head, ClauseHead::False) && clause.body.predicates.is_empty() {
                refutable_shape_possible = true;
                break;
            }
        }
    }
    if !refutable_shape_possible {
        return Ok(None);
    }
    let mut usable = Vec::with_capacity(clauses.len());
    for clause in clauses {
        control.poll()?;
        usable.push(
            is_ground_nullary(clause, control)? && constraint_is_ground_true(clause, control)?,
        );
    }
    Ok(Some(usable))
}

fn premises_available(
    clause: &HornClause,
    position: &FxHashMap<PredicateId, usize>,
    control: &mut GroundValidationControl<'_>,
) -> Result<bool, GroundDerivationError> {
    for (predicate, _) in &clause.body.predicates {
        control.poll()?;
        if !position.contains_key(predicate) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Append each predicate only after all its premises: the order is topological.
fn derive_nullary_facts(
    clauses: &[HornClause],
    usable: &[bool],
    control: &mut GroundValidationControl<'_>,
) -> Result<(Vec<(PredicateId, usize)>, FxHashMap<PredicateId, usize>), GroundDerivationError> {
    let mut order = Vec::new();
    let mut position = FxHashMap::default();
    let mut changed = true;
    while changed {
        control.poll()?;
        changed = false;
        for (index, clause) in clauses.iter().enumerate() {
            control.poll()?;
            if !usable[index] {
                continue;
            }
            let ClauseHead::Predicate(head, _) = &clause.head else {
                continue;
            };
            if position.contains_key(head) {
                continue;
            }
            if premises_available(clause, &position, control)? {
                position.insert(*head, order.len());
                order.push((*head, index));
                changed = true;
            }
        }
    }
    Ok((order, position))
}

fn materialize_step(
    clause_index: usize,
    clause: &HornClause,
    emitted: &FxHashMap<PredicateId, usize>,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<GroundDerivationStep>, GroundDerivationError> {
    control.poll()?;
    let mut premises = Vec::with_capacity(clause.body.predicates.len());
    for (premise, _) in &clause.body.predicates {
        control.poll()?;
        let Some(position) = emitted.get(premise).copied() else {
            return Ok(None);
        };
        premises.push(position);
    }
    Ok(Some(GroundDerivationStep {
        clause_index,
        env: FxHashMap::default(),
        premises,
    }))
}

/// Emit only steps reachable from the query, as required by the validator.
fn materialize_refutation(
    clauses: &[HornClause],
    order: &[(PredicateId, usize)],
    position: &FxHashMap<PredicateId, usize>,
    query_index: usize,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    control.poll()?;
    let mut needed = vec![false; order.len()];
    let mut frontier = Vec::new();
    for (predicate, _) in &clauses[query_index].body.predicates {
        control.poll()?;
        frontier.push(*predicate);
    }
    while let Some(predicate) = frontier.pop() {
        control.poll()?;
        let Some(&slot) = position.get(&predicate) else {
            return Ok(None);
        };
        if needed[slot] {
            continue;
        }
        needed[slot] = true;
        for (premise, _) in &clauses[order[slot].1].body.predicates {
            control.poll()?;
            frontier.push(*premise);
        }
    }

    let mut steps = Vec::new();
    let mut emitted = FxHashMap::default();
    for (slot, (predicate, clause_index)) in order.iter().enumerate() {
        control.poll()?;
        if !needed[slot] {
            continue;
        }
        let Some(step) =
            materialize_step(*clause_index, &clauses[*clause_index], &emitted, control)?
        else {
            return Ok(None);
        };
        emitted.insert(*predicate, steps.len());
        steps.push(step);
    }
    let query_step = steps.len();
    let Some(step) = materialize_step(query_index, &clauses[query_index], &emitted, control)?
    else {
        return Ok(None);
    };
    steps.push(step);
    Ok(Some(GroundDerivation { steps, query_step }))
}

fn search(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    let clauses = problem.clauses();
    let Some(usable) = usable_clauses(problem, clauses, control)? else {
        return Ok(None);
    };
    let (order, position) = derive_nullary_facts(clauses, &usable, control)?;
    for (index, clause) in clauses.iter().enumerate() {
        control.poll()?;
        if usable[index]
            && matches!(clause.head, ClauseHead::False)
            && premises_available(clause, &position, control)?
        {
            return materialize_refutation(clauses, &order, &position, index, control);
        }
    }
    Ok(None)
}

/// Propose an original-clause ground refutation; it still requires validation.
///
/// Ordinary `Ok(None)` permits fallback. `Interrupted` is terminal for this
/// attempt, even if a later callback could recover. No partial derivation is
/// returned. Variable collection, evaluator internals and cleanup remain
/// opaque cooperative intervals, not a hard deadline.
pub(crate) fn ground_nullary_refutation(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    let mut control = GroundValidationControl::new(progress);
    control.poll()?;
    let result = search(problem, &mut control)?;
    control.poll()?;
    Ok(result)
}

#[cfg(test)]
mod tests;
