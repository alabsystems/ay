// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded discovery of effective queries behind nullary error wrappers.

use std::collections::VecDeque;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::{ChcProblem, ClauseHead, HornClause, PredicateId};

use super::candidate_flow::{CandidateControl, MAX_PROPAGATED_CANDIDATES};

const MAX_INDEXED_CLAUSES: usize = 4_096;
const MAX_QUERY_ROOTS: usize = 16;
const MAX_QUERY_SINK_PREDICATES: usize = MAX_PROPAGATED_CANDIDATES / 2;
const MAX_QUERY_SLICE_EDGES: usize = 512;
const MAX_EFFECTIVE_ANCHORS: usize = MAX_PROPAGATED_CANDIDATES / 2;

pub(super) struct BoundedQuerySlice<'a> {
    pub(super) anchors: Vec<&'a HornClause>,
    pub(super) sink_predicates: Vec<PredicateId>,
}

/// Treat `P() -> false` and `P() -> Q()` as transparent error plumbing.
/// Non-transparent clauses entering that nullary sink closure become effective
/// query anchors, while every sink predicate is later proposed as `false` to
/// Houdini. Unsupported incoming shapes remain obligations on those false sink
/// candidates and therefore fail closed without becoming synthesis anchors.
pub(super) fn bounded_query_slice<'a>(
    problem: &'a ChcProblem,
    control: Option<CandidateControl<'_>>,
) -> Option<BoundedQuerySlice<'a>> {
    if control.is_some_and(CandidateControl::stopped) {
        return None;
    }
    let clauses = problem.clauses();
    let mut incoming: FxHashMap<PredicateId, Vec<usize>> = FxHashMap::default();
    let mut indexed = 0usize;
    for (index, clause) in clauses.iter().enumerate() {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        let ClauseHead::Predicate(predicate, _) = &clause.head else {
            continue;
        };
        indexed = indexed.checked_add(1)?;
        if indexed > MAX_INDEXED_CLAUSES {
            return None;
        }
        incoming.entry(*predicate).or_default().push(index);
    }

    let mut roots = 0usize;
    let mut anchor_indices = Vec::new();
    let mut anchor_seen = FxHashSet::default();
    let mut sink_predicates = Vec::new();
    let mut sink_seen = FxHashSet::default();
    let mut queue = VecDeque::new();
    for (index, clause) in clauses.iter().enumerate() {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        if !matches!(&clause.head, ClauseHead::False) {
            continue;
        }
        roots = roots.checked_add(1)?;
        if roots > MAX_QUERY_ROOTS {
            return None;
        }
        if let Some(predicate) = transparent_nullary_body(problem, clause) {
            push_sink(predicate, &mut sink_predicates, &mut sink_seen, &mut queue)?;
        } else {
            push_anchor(index, &mut anchor_indices, &mut anchor_seen)?;
        }
    }
    if roots == 0 {
        return None;
    }

    let mut traversed = 0usize;
    while let Some(sink) = queue.pop_front() {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        let Some(predecessors) = incoming.get(&sink) else {
            continue;
        };
        for index in predecessors {
            traversed = traversed.checked_add(1)?;
            if traversed > MAX_QUERY_SLICE_EDGES {
                return None;
            }
            let clause = clauses.get(*index)?;
            if let Some(predicate) = transparent_nullary_body(problem, clause) {
                push_sink(predicate, &mut sink_predicates, &mut sink_seen, &mut queue)?;
            } else if is_guarded_anchor(clause) {
                push_anchor(*index, &mut anchor_indices, &mut anchor_seen)?;
            }
        }
    }
    sink_predicates.sort_unstable();
    let anchors = anchor_indices
        .into_iter()
        .map(|index| clauses.get(index))
        .collect::<Option<Vec<_>>>()?;
    Some(BoundedQuerySlice {
        anchors,
        sink_predicates,
    })
}

fn transparent_nullary_body(problem: &ChcProblem, clause: &HornClause) -> Option<PredicateId> {
    if !matches!(
        clause.body.constraint.as_ref(),
        None | Some(crate::ChcExpr::Bool(true))
    ) {
        return None;
    }
    let [(predicate, arguments)] = clause.body.predicates.as_slice() else {
        return None;
    };
    (arguments.is_empty() && problem.get_predicate(*predicate)?.arg_sorts.is_empty())
        .then_some(*predicate)
}

fn is_guarded_anchor(clause: &HornClause) -> bool {
    clause.body.predicates.len() == 1
        && clause
            .body
            .constraint
            .as_ref()
            .is_some_and(|constraint| !matches!(constraint, crate::ChcExpr::Bool(true)))
}

fn push_sink(
    predicate: PredicateId,
    sinks: &mut Vec<PredicateId>,
    seen: &mut FxHashSet<PredicateId>,
    queue: &mut VecDeque<PredicateId>,
) -> Option<()> {
    if seen.insert(predicate) {
        if sinks.len() >= MAX_QUERY_SINK_PREDICATES {
            return None;
        }
        sinks.push(predicate);
        queue.push_back(predicate);
    }
    Some(())
}

fn push_anchor(index: usize, anchors: &mut Vec<usize>, seen: &mut FxHashSet<usize>) -> Option<()> {
    if seen.insert(index) {
        if anchors.len() >= MAX_EFFECTIVE_ANCHORS {
            return None;
        }
        anchors.push(index);
    }
    Some(())
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_query_tests.rs"]
mod tests;
