// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded concrete forward chaining over ORIGINAL linear Horn clauses.
//!
//! This is the ordinary immediate-consequence construction, not a projected
//! safety decision: failure/unsupported syntax produces no candidate. Full
//! concrete tuples, including array defaults and ordered stores, travel across
//! predicate edges. Every environment comes from the real body tuple; missing
//! variables are never completed. The existing independent original validator
//! remains the ONLY verdict authority.
//!
//! The existing source/value replay envelope bounds logical candidate work.
//! Evaluator internals, allocation, aggregate equality and destruction remain
//! opaque intervals bracketed by the same borrowed caller's sticky polls.

use super::{
    artifact, canonical_ground_value_matches_sort, eval_ground_with_control,
    ground_value_storage_profile, GroundDerivation, GroundDerivationError, GroundDerivationStep,
    GroundSourceSurfaceCache, GroundSourceSurfaceError, GroundValidationControl,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS,
};
use crate::clause::{ClauseHead, HornClause};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcProblem, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[cfg(test)]
pub(crate) mod fixtures;
mod step;
#[cfg(test)]
mod tests;
mod trace;

struct Node {
    predicate: PredicateId,
    values: Vec<SmtValue>,
    step: GroundDerivationStep,
    parent: Option<usize>,
    depth: usize,
}

fn surface_error(error: GroundSourceSurfaceError) -> GroundDerivationError {
    match error {
        GroundSourceSurfaceError::Interrupted => GroundDerivationError::Interrupted,
        GroundSourceSurfaceError::SourceWorkLimitExceeded => {
            GroundDerivationError::SourceWorkLimitExceeded
        }
        _ => GroundDerivationError::InvalidSourceProblem,
    }
}

fn source(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), GroundDerivationError> {
    let result = artifact::validate_ground_source_problem_with_control(problem, control);
    let result = result.map_err(|error| match error.reason {
        super::ChcGroundDerivationArtifactErrorReason::Interrupted => {
            GroundDerivationError::Interrupted
        }
        super::ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded => {
            GroundDerivationError::SourceWorkLimitExceeded
        }
        _ => GroundDerivationError::InvalidSourceProblem,
    });
    let terminal = control.poll().map_err(GroundDerivationError::from);
    match result {
        Err(error) => Err(error),
        Ok(()) => terminal,
    }
}

fn push(
    nodes: &mut Vec<Node>,
    node: Node,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), GroundDerivationError> {
    control.poll()?;
    if nodes.len() >= CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS {
        return Err(GroundDerivationError::SourceWorkLimitExceeded);
    }
    // Reserve the retained node/environment and complete value payload before
    // vector growth. This is logical admission, not allocator/RSS closure.
    cache.charge(1).map_err(surface_error)?;
    cache
        .charge_step_scalar_replay(node.step.clause_index, &node.step.env, &node.values)
        .map_err(surface_error)?;
    nodes
        .try_reserve(1)
        .map_err(|_| GroundDerivationError::SourceWorkLimitExceeded)?;
    control.poll()?;
    nodes.push(node);
    Ok(())
}

fn seeds(
    problem: &ChcProblem,
    nodes: &mut Vec<Node>,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        control.poll()?;
        cache.charge(1).map_err(surface_error)?;
        if !clause.body.predicates.is_empty() {
            continue;
        }
        let Some(env) = step::environment(clause_index, None, cache, control)? else {
            continue;
        };
        if !step::enabled(clause_index, clause, &env, cache, control)? {
            continue;
        }
        let step = GroundDerivationStep {
            clause_index,
            env,
            premises: Vec::new(),
        };
        match &clause.head {
            ClauseHead::False => {
                cache.charge(1).map_err(surface_error)?;
                let mut steps = Vec::new();
                steps
                    .try_reserve_exact(1)
                    .map_err(|_| GroundDerivationError::SourceWorkLimitExceeded)?;
                control.poll()?;
                steps.push(step);
                return Ok(Some(GroundDerivation {
                    steps,
                    query_step: 0,
                }));
            }
            ClauseHead::Predicate(predicate, arguments) => {
                if let Some(values) =
                    step::head(problem, *predicate, arguments, &step.env, cache, control)?
                {
                    push(
                        nodes,
                        Node {
                            predicate: *predicate,
                            values,
                            step,
                            parent: None,
                            depth: 0,
                        },
                        cache,
                        control,
                    )?;
                }
            }
        }
    }
    Ok(None)
}

fn successors(
    problem: &ChcProblem,
    cursor: usize,
    max_depth: usize,
    nodes: &mut Vec<Node>,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        control.poll()?;
        cache.charge(1).map_err(surface_error)?;
        let [(predicate, arguments)] = clause.body.predicates.as_slice() else {
            continue;
        };
        let node = &nodes[cursor];
        if *predicate != node.predicate {
            continue;
        }
        if !matches!(clause.head, ClauseHead::False) && node.depth >= max_depth {
            continue;
        }
        let Some(env) = step::environment(
            clause_index,
            Some((arguments, &node.values)),
            cache,
            control,
        )?
        else {
            continue;
        };
        if !step::enabled(clause_index, clause, &env, cache, control)? {
            continue;
        }
        let step = GroundDerivationStep {
            clause_index,
            env,
            premises: Vec::new(),
        };
        if matches!(clause.head, ClauseHead::False) {
            return trace::materialize(nodes, cursor, step, cache, control).map(Some);
        }
        let ClauseHead::Predicate(predicate, arguments) = &clause.head else {
            continue;
        };
        let Some(values) = step::head(problem, *predicate, arguments, &step.env, cache, control)?
        else {
            continue;
        };
        let depth = node
            .depth
            .checked_add(1)
            .ok_or(GroundDerivationError::SourceWorkLimitExceeded)?;
        push(
            nodes,
            Node {
                predicate: *predicate,
                values,
                step,
                parent: Some(cursor),
                depth,
            },
            cache,
            control,
        )?;
    }
    Ok(None)
}

fn search(
    problem: &ChcProblem,
    max_depth: usize,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    source(problem, control)?;
    let mut cache = GroundSourceSurfaceCache::new(problem);
    let mut nodes = Vec::new();
    if let Some(query) = seeds(problem, &mut nodes, &mut cache, control)? {
        return Ok(Some(query));
    }
    let mut cursor = 0usize;
    // Append-only BFS visits each newly constructed tuple once. No semantic
    // equality/dedup oracle, widening, or inferred default state is used.
    while cursor < nodes.len() {
        control.poll()?;
        if let Some(query) =
            successors(problem, cursor, max_depth, &mut nodes, &mut cache, control)?
        {
            return Ok(Some(query));
        }
        cursor += 1;
    }
    Ok(None)
}

/// Only proposes a candidate. The supplied original caller stays borrowed for
/// the complete attempt; no fresh timeout, grant or default model is created.
pub(crate) fn ground_linear_refutation(
    problem: &ChcProblem,
    max_depth: usize,
    progress: &mut dyn FnMut() -> bool,
) -> Result<Option<GroundDerivation>, GroundDerivationError> {
    let mut control = GroundValidationControl::new(progress);
    control.poll()?;
    let result = search(problem, max_depth, &mut control);
    // Search temporaries are gone. Keep the first error; a successful candidate
    // additionally requires the SAME control's terminal observation.
    let terminal = control.poll().map_err(GroundDerivationError::from);
    match result {
        Err(error) => Err(error),
        Ok(value) => terminal.map(|()| value),
    }
}
