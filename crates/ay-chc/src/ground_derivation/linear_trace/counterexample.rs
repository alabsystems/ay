// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexamples wrapping a validated linear-trace derivation.

use super::{eval_args, ground_derivation_from_linear_trace, trace_witness_deadline, LinearTrace};
use crate::clause::ClauseHead;
use crate::ground_derivation::{canonical_scalar_value_matches_sort, GroundDerivation};
use crate::pdr::counterexample::{
    Counterexample, CounterexampleStep, DerivationWitness, DerivationWitnessEntry,
};
use crate::smt::SmtValue;
use crate::{CancellationToken, ChcExpr, ChcProblem, ChcSort, ChcVar, PredicateId};
use ay_core::time::Instant;
use num_traits::ToPrimitive;

/// The existing scalar trace row is i64, independently of predicate width.
/// Keep exact unsigned BV values that fit it; a missing/out-of-range value must
/// remain absent, never normalized, truncated or fabricated for playback.
fn scalar_assignment(value: &SmtValue, sort: &ChcSort) -> Option<i64> {
    match (sort, value) {
        (ChcSort::Int, SmtValue::Int(value)) => i64::try_from(*value).ok(),
        (ChcSort::Bool, SmtValue::Bool(value)) => Some(i64::from(*value)),
        (ChcSort::BitVec(_), SmtValue::BitVec(raw, _))
            if canonical_scalar_value_matches_sort(value, sort) =>
        {
            i64::try_from(*raw).ok()
        }
        (ChcSort::BitVec(_), SmtValue::BigBitVec(raw, _))
            if canonical_scalar_value_matches_sort(value, sort) =>
        {
            raw.to_i64()
        }
        _ => None,
    }
}

/// Literal for a canonical state value, when `ChcExpr` can spell it.
fn value_literal(value: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
    match (sort, value) {
        (ChcSort::Int, SmtValue::Int(i)) => Some(ChcExpr::int(*i)),
        (ChcSort::Int, SmtValue::BigInt(i)) => Some(ChcExpr::from_bigint(i.as_ref().clone())),
        (ChcSort::Real, SmtValue::Real(r)) => Some(ChcExpr::Real(
            i64::try_from(r.numer()).ok()?,
            i64::try_from(r.denom()).ok()?,
        )),
        (ChcSort::Bool, SmtValue::Bool(b)) => Some(ChcExpr::Bool(*b)),
        (ChcSort::BitVec(w), SmtValue::BitVec(_, vw) | SmtValue::BigBitVec(_, vw)) if w == vw => {
            value.bitvec_to_chc_expr()
        }
        _ => None,
    }
}

/// Wrap a validated linear derivation (fact, transitions, query — the shape
/// [`ground_derivation_from_linear_trace`] builds) as a counterexample: one
/// step per state, a derivation witness whose entries carry each fired
/// clause's full instance, and the ground derivation itself.
///
/// The witness is the fallback evidence for a transform stack that cannot map
/// the ground derivation back; it is re-verified like any other witness.
fn counterexample_from_linear_derivation(
    problem: &ChcProblem,
    predicate: PredicateId,
    derivation: GroundDerivation,
) -> Option<Counterexample> {
    let pred = problem.get_predicate(predicate)?;
    let clauses = problem.clauses();
    let (query, chain) = derivation.steps.split_last()?;
    if chain.is_empty() {
        return None;
    }
    // Head value tuple of every non-query step (the state it derives).
    let mut states: Vec<Vec<SmtValue>> = Vec::with_capacity(chain.len());
    for step in chain {
        let ClauseHead::Predicate(_, head_args) = &clauses.get(step.clause_index)?.head else {
            return None;
        };
        states.push(eval_args(head_args, &pred.arg_sorts, &step.env)?);
    }
    let canonical = |idx: usize| crate::lemma_hints::canonical_var_name(predicate, idx);

    let cex_steps: Vec<CounterexampleStep> = chain
        .iter()
        .zip(&states)
        .map(|(step, state)| {
            let assignments = state
                .iter()
                .zip(&pred.arg_sorts)
                .enumerate()
                .filter_map(|(idx, (value, sort))| {
                    scalar_assignment(value, sort).map(|raw| (canonical(idx), raw))
                })
                .collect();
            CounterexampleStep::new(predicate, assignments).with_clause(step.clause_index)
        })
        .collect();

    // Witness entries root-first: entry 0 is the last state.
    let last = chain.len() - 1;
    let mut entries = Vec::with_capacity(chain.len());
    let mut witness_ok = true;
    for (entry_idx, level) in (0..=last).rev().enumerate() {
        let step = &chain[level];
        let mut instances = step.env.clone();
        let mut conjuncts = Vec::with_capacity(states[level].len());
        for (idx, (value, sort)) in states[level].iter().zip(&pred.arg_sorts).enumerate() {
            let name = canonical(idx);
            match value_literal(value, sort) {
                Some(literal) => conjuncts.push(ChcExpr::eq(
                    ChcExpr::var(ChcVar::new(name.clone(), sort.clone())),
                    literal,
                )),
                None => witness_ok = false,
            }
            instances.insert(name, value.clone());
        }
        entries.push(DerivationWitnessEntry {
            predicate,
            level,
            state: ChcExpr::and_all(conjuncts),
            incoming_clause: Some(step.clause_index),
            premises: if level == 0 {
                Vec::new()
            } else {
                vec![entry_idx + 1]
            },
            instances,
        });
    }
    let query_clause = query.clause_index;
    let cex = if witness_ok {
        Counterexample::with_witness(
            cex_steps,
            DerivationWitness {
                query_clause: Some(query_clause),
                root: 0,
                entries,
            },
        )
    } else {
        Counterexample::new(cex_steps)
    };
    Some(cex.with_ground_derivation(derivation))
}

/// The counterexample an engine reports for a concrete trace it found:
/// ground-evidenced when the trace validates on `problem`, otherwise a
/// skeleton of `depth` (the pre-witness behaviour). Consumers re-validate
/// either on their own clauses.
pub(crate) fn engine_trace_counterexample(
    problem: &ChcProblem,
    trace: &LinearTrace,
    depth: usize,
    cancellation: Option<&CancellationToken>,
    engine: &str,
) -> Counterexample {
    let token = cancellation.cloned().unwrap_or_default();
    match counterexample_from_linear_trace(problem, trace, Some(trace_witness_deadline()), &token) {
        Some(cex) => {
            tracing::debug!(
                "{engine}: counterexample ground-validated from its own model ({} states)",
                trace.states.len()
            );
            cex
        }
        None => {
            tracing::debug!(
                "{engine}: model trace did not ground-validate; reporting a skeleton (depth {depth})"
            );
            crate::engine_result::skeleton_counterexample(problem, depth)
        }
    }
}

/// Build the ground-evidenced counterexample for `trace` over `problem`, or
/// `None` when the trace does not ground-validate.
pub(crate) fn counterexample_from_linear_trace(
    problem: &ChcProblem,
    trace: &LinearTrace,
    deadline: Option<Instant>,
    cancellation: &CancellationToken,
) -> Option<Counterexample> {
    let derivation = ground_derivation_from_linear_trace(problem, trace, deadline, cancellation)?;
    counterexample_from_linear_derivation(problem, trace.predicate, derivation)
}

#[cfg(test)]
mod tests;
