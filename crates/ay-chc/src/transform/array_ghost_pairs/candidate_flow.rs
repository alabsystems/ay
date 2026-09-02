// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed, bounded reverse-CFG transport for query-anchored candidates.
//!
//! MODEL_CHECKER_CONSUMER predicates describe live CFG columns, so successor signatures may
//! reorder or project predecessor columns.  For a linear clause
//! `B(body_args) /\ constraint -> H(head_args)`, a query candidate on `H` can
//! be proposed on `B` by following exact, unique clause variables backward.
//! The resulting candidate is still only a heuristic: whole-system Houdini and
//! original-clause certificate sealing remain authoritative.

use std::collections::VecDeque;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;

use crate::{CancellationToken, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, PredicateId};

use super::{GhostPairSpec, GhostPredSpec};

/// Independent bounds matching the admitted MODEL_CHECKER_CONSUMER-scale ghost route.
const MAX_REVERSE_EDGES: usize = 512;
const MAX_EDGE_TRAVERSALS: usize = 65_536;
pub(super) const MAX_PROPAGATED_CANDIDATES: usize = 256;

#[derive(Clone, Copy)]
pub(super) struct CandidateControl<'a> {
    pub(super) cancellation: &'a CancellationToken,
    pub(super) deadline: Instant,
}

impl CandidateControl<'_> {
    pub(super) fn stopped(self) -> bool {
        self.cancellation.is_cancelled()
            || Instant::now() >= self.deadline
            || ay_core::TermStore::global_memory_exceeded()
    }
}

/// One composed map from the query predicate's original formals to a reachable
/// predecessor's original formals.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct CandidateTransport {
    pub(super) predicate: PredicateId,
    pub(super) source_to_target: Vec<Option<usize>>,
}

/// Combine the established compatible-prefix proposals with exact reverse-CFG
/// transports. The identity is omitted because the caller already synthesized
/// the source candidate before it knew which columns that candidate required.
pub(super) fn propagated_transports(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    source: PredicateId,
    source_layout: &GhostPredSpec,
    required: &FxHashSet<usize>,
    control: Option<CandidateControl<'_>>,
) -> Option<Vec<CandidateTransport>> {
    let source_decl = problem.get_predicate(source)?;
    let identity = required_identity(source_decl.arg_sorts.len(), required);
    let mut seen = FxHashSet::default();
    seen.insert((source, identity));
    let mut transports = Vec::new();

    // Store transitions need this legacy proposal when no exact whole-variable
    // edge exists. Houdini and certificate sealing remain the proof authority.
    for target_decl in problem.predicates() {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        let Some(target_layout) = spec.preds.get(&target_decl.id) else {
            continue;
        };
        if !compatible_target_layout(
            &source_decl.arg_sorts,
            source_layout,
            &target_decl.arg_sorts,
            target_layout,
        ) {
            continue;
        }
        let transport = CandidateTransport {
            predicate: target_decl.id,
            source_to_target: required_identity(source_decl.arg_sorts.len(), required),
        };
        if seen.insert((transport.predicate, transport.source_to_target.clone())) {
            if transports.len() >= MAX_PROPAGATED_CANDIDATES.saturating_sub(1) {
                return None;
            }
            transports.push(transport);
        }
    }
    for transport in bounded_reverse_transports(problem, source, required, control)? {
        if seen.insert((transport.predicate, transport.source_to_target.clone())) {
            if transports.len() >= MAX_PROPAGATED_CANDIDATES.saturating_sub(1) {
                return None;
            }
            transports.push(transport);
        }
    }
    Some(transports)
}

fn required_identity(arity: usize, required: &FxHashSet<usize>) -> Vec<Option<usize>> {
    (0..arity)
        .map(|position| required.contains(&position).then_some(position))
        .collect()
}

fn compatible_target_layout(
    source_sorts: &[ChcSort],
    source: &GhostPredSpec,
    target_sorts: &[ChcSort],
    target: &GhostPredSpec,
) -> bool {
    source.original_arity == source_sorts.len()
        && target.original_arity == target_sorts.len()
        && target_sorts.starts_with(source_sorts)
        && source
            .array_positions
            .iter()
            .enumerate()
            .all(|(index, position)| {
                target.array_positions.get(index) == Some(position)
                    && target.index_sorts.get(index) == source.index_sorts.get(index)
            })
}

#[derive(Debug)]
struct ReverseEdge {
    predecessor: PredicateId,
    head_to_body: Vec<Option<usize>>,
}

/// Return the identity map and every usable reverse-CFG composition.
///
/// A partial edge is retained only while every source position actually used
/// by the candidate remains mapped. Unsupported clauses are skipped; malformed
/// problem metadata, resource exhaustion, cancellation, or expiry rejects the
/// whole heuristic pass.
pub(super) fn bounded_reverse_transports(
    problem: &ChcProblem,
    source: PredicateId,
    required_source_positions: &FxHashSet<usize>,
    control: Option<CandidateControl<'_>>,
) -> Option<Vec<CandidateTransport>> {
    if control.is_some_and(CandidateControl::stopped) {
        return None;
    }
    let source_decl = problem.get_predicate(source)?;
    if required_source_positions
        .iter()
        .any(|position| *position >= source_decl.arg_sorts.len())
    {
        return None;
    }

    let reverse = build_reverse_adjacency(problem, control)?;
    // Erase unused columns before traversal so paths that differ only in
    // irrelevant CFG state share one canonical transport state and budget.
    let identity = required_identity(source_decl.arg_sorts.len(), required_source_positions);
    let initial = CandidateTransport {
        predicate: source,
        source_to_target: identity,
    };
    let mut queue = VecDeque::from([initial.clone()]);
    let mut seen = FxHashSet::default();
    seen.insert((source, initial.source_to_target.clone()));
    let mut out = Vec::new();
    let mut traversals = 0usize;

    while let Some(current) = queue.pop_front() {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        if out.len() >= MAX_PROPAGATED_CANDIDATES {
            return None;
        }
        out.push(current.clone());

        let Some(edges) = reverse.get(&current.predicate) else {
            continue;
        };
        for edge in edges {
            traversals = traversals.checked_add(1)?;
            if traversals > MAX_EDGE_TRAVERSALS || control.is_some_and(CandidateControl::stopped) {
                return None;
            }
            let composed = compose_maps(&current.source_to_target, &edge.head_to_body)?;
            if !required_map_is_typed(
                problem,
                source,
                edge.predecessor,
                required_source_positions,
                &composed,
            )? {
                continue;
            }
            let key = (edge.predecessor, composed.clone());
            if seen.insert(key) {
                if seen.len() > MAX_PROPAGATED_CANDIDATES {
                    return None;
                }
                queue.push_back(CandidateTransport {
                    predicate: edge.predecessor,
                    source_to_target: composed,
                });
            }
        }
    }
    Some(out)
}

fn build_reverse_adjacency(
    problem: &ChcProblem,
    control: Option<CandidateControl<'_>>,
) -> Option<FxHashMap<PredicateId, Vec<ReverseEdge>>> {
    let mut reverse: FxHashMap<PredicateId, Vec<ReverseEdge>> = FxHashMap::default();
    let mut edge_count = 0usize;
    for clause in problem.clauses() {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        let [(body_predicate, body_args)] = clause.body.predicates.as_slice() else {
            continue;
        };
        let ClauseHead::Predicate(head_predicate, head_args) = &clause.head else {
            continue;
        };
        let body_decl = problem.get_predicate(*body_predicate)?;
        let head_decl = problem.get_predicate(*head_predicate)?;
        let body_positions = unique_plain_variables(body_args, &body_decl.arg_sorts)?;
        let head_positions = unique_plain_variables(head_args, &head_decl.arg_sorts)?;
        let mut head_to_body = vec![None; head_args.len()];
        for (variable, head_position) in head_positions {
            let Some(body_position) = body_positions.get(&variable).copied() else {
                continue;
            };
            if head_decl.arg_sorts.get(head_position) != body_decl.arg_sorts.get(body_position) {
                return None;
            }
            head_to_body[head_position] = Some(body_position);
        }
        if head_to_body.iter().all(Option::is_none) {
            continue;
        }
        edge_count = edge_count.checked_add(1)?;
        if edge_count > MAX_REVERSE_EDGES {
            return None;
        }
        reverse
            .entry(*head_predicate)
            .or_default()
            .push(ReverseEdge {
                predecessor: *body_predicate,
                head_to_body,
            });
    }
    Some(reverse)
}

/// Extract only variables whose names occur once in the atom. Expressions are
/// valid CHC arguments but cannot establish an exact transport correspondence.
fn unique_plain_variables(
    args: &[ChcExpr],
    declared_sorts: &[ChcSort],
) -> Option<FxHashMap<ChcVar, usize>> {
    if args.len() != declared_sorts.len() {
        return None;
    }
    let mut by_name: FxHashMap<String, (ChcVar, usize, bool)> = FxHashMap::default();
    for (position, (argument, declared_sort)) in args.iter().zip(declared_sorts).enumerate() {
        if argument.sort() != *declared_sort {
            return None;
        }
        let ChcExpr::Var(variable) = argument else {
            continue;
        };
        if variable.sort != *declared_sort {
            return None;
        }
        if let Some((_, _, repeated)) = by_name.get_mut(&variable.name) {
            *repeated = true;
        } else {
            by_name.insert(variable.name.clone(), (variable.clone(), position, false));
        }
    }
    Some(
        by_name
            .into_values()
            .filter_map(|(variable, position, repeated)| {
                (!repeated).then_some((variable, position))
            })
            .collect(),
    )
}

fn compose_maps(
    source_to_head: &[Option<usize>],
    head_to_body: &[Option<usize>],
) -> Option<Vec<Option<usize>>> {
    source_to_head
        .iter()
        .map(|head_position| match head_position {
            Some(position) => head_to_body.get(*position).copied(),
            None => Some(None),
        })
        .collect()
}

fn required_map_is_typed(
    problem: &ChcProblem,
    source: PredicateId,
    target: PredicateId,
    required: &FxHashSet<usize>,
    source_to_target: &[Option<usize>],
) -> Option<bool> {
    let source_decl = problem.get_predicate(source)?;
    let target_decl = problem.get_predicate(target)?;
    if source_to_target.len() != source_decl.arg_sorts.len() {
        return None;
    }
    for source_position in required {
        let Some(target_position) = source_to_target.get(*source_position).copied().flatten()
        else {
            return Some(false);
        };
        if source_decl.arg_sorts.get(*source_position) != target_decl.arg_sorts.get(target_position)
        {
            return Some(false);
        }
    }
    Some(true)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_flow_tests.rs"]
mod tests;

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_flow_resource_tests.rs"]
mod resource_tests;
