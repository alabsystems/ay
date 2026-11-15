// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Re-expressing a ground derivation over the clauses a case split came from.
//!
//! PDR splits input clauses on disjunctions and `ite`s. Each resulting clause
//! instance must be re-attributed to a target clause with the same predicates
//! and evaluated head/body values whose constraint holds. The result is only
//! returned after independent native validation on the target problem.
//!
//! A borrowed original stop owner covers each candidate and evaluation phase.
//! Equality propagation, value comparison, structural comparison, allocations,
//! and individual evaluator/simplifier operations remain opaque intervals;
//! these polls do not promise a hard deadline or introduce a fresh work budget.

use super::complete::propagate_env_for_clause;
use super::{
    eval_ground_with_control, validate_ground_derivation_with_control, GroundDerivation,
    GroundDerivationError, GroundDerivationStep, GroundValidationControl,
};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcProblem, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;

type GroundResult<T> = Result<T, GroundDerivationError>;

/// The values `args` take under `env` (`None` when one does not evaluate).
fn arg_values(
    args: &[ChcExpr],
    env: &FxHashMap<String, SmtValue>,
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<Option<Vec<SmtValue>>> {
    control.poll()?;
    let mut values = Vec::with_capacity(args.len());
    for arg in args {
        let Some(value) = eval_ground_with_control(arg, env, control)? else {
            return Ok(None);
        };
        values.push(value);
    }
    control.poll()?;
    Ok(Some(values))
}

fn same_values(
    a: &[SmtValue],
    b: &[SmtValue],
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<bool> {
    control.poll()?;
    if a.len() != b.len() {
        return Ok(false);
    }
    for (x, y) in a.iter().zip(b) {
        control.poll()?;
        let same = crate::expr::evaluate::smt_values_equal(x, y) == Some(true);
        control.poll()?;
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// What one fired clause derived and consumed: head predicate and values
/// (`None` for a query), and each body premise's predicate and values.
struct Instance {
    head: Option<(crate::PredicateId, Vec<SmtValue>)>,
    body: Vec<(crate::PredicateId, Vec<SmtValue>)>,
}

fn instance(
    clause: &HornClause,
    env: &FxHashMap<String, SmtValue>,
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<Option<Instance>> {
    control.poll()?;
    let head = match &clause.head {
        ClauseHead::Predicate(pred, args) => {
            let Some(values) = arg_values(args, env, control)? else {
                return Ok(None);
            };
            Some((*pred, values))
        }
        ClauseHead::False => None,
    };
    let mut body = Vec::with_capacity(clause.body.predicates.len());
    for (pred, args) in &clause.body.predicates {
        let Some(values) = arg_values(args, env, control)? else {
            return Ok(None);
        };
        body.push((*pred, values));
    }
    control.poll()?;
    Ok(Some(Instance { head, body }))
}

/// Whether `clause` fires under `env` with exactly `source`'s instance.
fn reproduces(
    clause: &HornClause,
    env: &FxHashMap<String, SmtValue>,
    source: &Instance,
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<bool> {
    control.poll()?;
    if let Some(constraint) = &clause.body.constraint {
        if !matches!(
            eval_ground_with_control(constraint, env, control)?,
            Some(SmtValue::Bool(true))
        ) {
            return Ok(false);
        }
    }
    let Some(candidate) = instance(clause, env, control)? else {
        return Ok(false);
    };
    let heads_agree = match (&candidate.head, &source.head) {
        (Some((p, a)), Some((q, b))) => p == q && same_values(a, b, control)?,
        (None, None) => true,
        _ => false,
    };
    if !heads_agree || candidate.body.len() != source.body.len() {
        return Ok(false);
    }
    for ((p, a), (q, b)) in candidate.body.iter().zip(&source.body) {
        control.poll()?;
        if p != q || !same_values(a, b, control)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_shape(
    clause: &HornClause,
    source_clause: &HornClause,
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<bool> {
    control.poll()?;
    if clause.head.predicate_id() != source_clause.head.predicate_id()
        || clause.body.predicates.len() != source_clause.body.predicates.len()
    {
        return Ok(false);
    }
    for ((p, _), (q, _)) in clause
        .body
        .predicates
        .iter()
        .zip(&source_clause.body.predicates)
    {
        control.poll()?;
        if p != q {
            return Ok(false);
        }
    }
    Ok(true)
}

fn find_clause(
    step: &GroundDerivationStep,
    source_clause: &HornClause,
    source: &Instance,
    onto: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<Option<GroundDerivationStep>> {
    for (index, clause) in onto.clauses().iter().enumerate() {
        if !same_shape(clause, source_clause, control)? {
            continue;
        }
        control.poll()?;
        let mut env = step.env.clone();
        control.poll()?;
        // Recover variables simplified away by splitting using only the
        // original clause's own equalities, never guessed/default values.
        propagate_env_for_clause(clause, &mut env);
        control.poll()?;
        if reproduces(clause, &env, source, control)? {
            control.poll()?;
            return Ok(Some(GroundDerivationStep {
                clause_index: index,
                env,
                premises: step.premises.clone(),
            }));
        }
    }
    Ok(None)
}

fn reresolve(
    derivation: &GroundDerivation,
    from: &ChcProblem,
    onto: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> GroundResult<Option<GroundDerivation>> {
    control.poll()?;
    let mut steps = Vec::with_capacity(derivation.steps.len());
    for step in &derivation.steps {
        control.poll()?;
        let Some(source_clause) = from.clauses().get(step.clause_index) else {
            return Ok(None);
        };
        let Some(source) = instance(source_clause, &step.env, control)? else {
            return Ok(None);
        };
        let Some(fired) = find_clause(step, source_clause, &source, onto, control)? else {
            return Ok(None);
        };
        steps.push(fired);
    }
    let reresolved = GroundDerivation {
        steps,
        query_step: derivation.query_step,
    };
    match validate_ground_derivation_with_control(onto, &reresolved, control) {
        Ok(()) => Ok(Some(reresolved)),
        Err(GroundDerivationError::Interrupted) => Err(GroundDerivationError::Interrupted),
        Err(_) => Ok(None),
    }
}

/// Re-attribution under the original owner. Semantic refusal is `Ok(None)`;
/// interruption is an error, never permission to try another evidence route.
pub(crate) fn reresolve_ground_derivation_with_progress(
    derivation: &GroundDerivation,
    from: &ChcProblem,
    onto: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> GroundResult<Option<GroundDerivation>> {
    let mut control = GroundValidationControl::new_native(progress);
    let result = reresolve(derivation, from, onto, &mut control);
    // Candidate temporaries and failed evidence are gone before this fence.
    control.poll()?;
    result
}

#[cfg(test)]
fn reresolve_ground_derivation(
    derivation: &GroundDerivation,
    from: &ChcProblem,
    onto: &ChcProblem,
) -> Option<GroundDerivation> {
    reresolve_ground_derivation_with_progress(derivation, from, onto, &mut || true)
        .ok()
        .flatten()
}

#[cfg(test)]
#[path = "reresolve_tests.rs"]
mod tests;
