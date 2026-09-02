// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate-pool construction for bounded whole-system Houdini.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;

use crate::{CancellationToken, ChcExpr, ChcProblem, ChcVar, PredicateId};

use super::candidate::{query_anchored_ghost_candidates_controlled, scalar_candidate_node_count};
use super::candidate_flow::{CandidateControl, MAX_PROPAGATED_CANDIDATES as MAX_CANDIDATES};
use super::candidate_model::CandidateAtom;
use super::candidate_substitute::exact_substitute_scalar_candidate;
use super::candidate_support::demanded_nonzero_supports;
use super::GhostPairSpec;

pub(super) const MAX_HOUDINI_CANDIDATES: usize = MAX_CANDIDATES;

pub(super) fn build_candidate_pools(
    original: &ChcProblem,
    raw_ghost: &ChcProblem,
    spec: &GhostPairSpec,
    canonical: &FxHashMap<PredicateId, Vec<ChcVar>>,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<FxHashMap<PredicateId, Vec<CandidateAtom>>> {
    let control = CandidateControl {
        cancellation,
        deadline,
    };
    let batch = query_anchored_ghost_candidates_controlled(original, spec, cancellation, deadline)?;
    let supports = demanded_nonzero_supports(original, spec, &batch.candidates, Some(control))?;
    let mut pools: FxHashMap<PredicateId, Vec<CandidateAtom>> = FxHashMap::default();
    let mut seen: FxHashSet<(PredicateId, ChcExpr)> = FxHashSet::default();
    let mut rebind_nodes_remaining = crate::expr::MAX_PREPROCESSING_NODES;

    for candidate in batch.candidates {
        if control.stopped() {
            return None;
        }
        let target_vars = canonical.get(&candidate.predicate)?;
        if candidate.vars.len() != target_vars.len()
            || candidate
                .vars
                .iter()
                .zip(target_vars)
                .any(|(source, target)| source.sort != target.sort)
        {
            return None;
        }
        let target_exprs: Vec<_> = target_vars.iter().cloned().map(ChcExpr::var).collect();
        let rebound = exact_substitute_scalar_candidate(
            &candidate.formula,
            &candidate.vars,
            &target_exprs,
            cancellation,
            deadline,
            rebind_nodes_remaining,
        )?;
        rebind_nodes_remaining = rebind_nodes_remaining.checked_sub(rebound.expanded_nodes)?;
        insert_candidate(
            raw_ghost,
            candidate.predicate,
            target_vars,
            rebound.formula,
            &mut pools,
            &mut seen,
        )?;
    }
    for predicate in batch.sink_predicates {
        if control.stopped() {
            return None;
        }
        let vars = canonical.get(&predicate)?;
        if !vars.is_empty() {
            return None;
        }
        insert_candidate(
            raw_ghost,
            predicate,
            vars,
            ChcExpr::Bool(false),
            &mut pools,
            &mut seen,
        )?;
    }

    // Query anchors describe the desired array property but commonly need a
    // small reachability support fact. Demand analysis proposes nonzero only
    // for relevant ORIGINAL scalar BV arguments; appended ghost indices are
    // universally arbitrary and must never be constrained this way. These
    // facts are optional search hints, so truncate them rather than rejecting
    // an otherwise complete mandatory anchor/sink pool at the global cap.
    for (predicate, position, width) in supports {
        if control.stopped() {
            return None;
        }
        if seen.len() >= MAX_HOUDINI_CANDIDATES {
            break;
        }
        let vars = canonical.get(&predicate)?;
        let variable = ChcExpr::var(vars.get(position)?.clone());
        let formula = ChcExpr::ne(variable, ChcExpr::BitVec(0, width));
        insert_candidate(raw_ghost, predicate, vars, formula, &mut pools, &mut seen)?;
    }
    Some(pools)
}

fn insert_candidate(
    problem: &ChcProblem,
    predicate: PredicateId,
    vars: &[ChcVar],
    formula: ChcExpr,
    pools: &mut FxHashMap<PredicateId, Vec<CandidateAtom>>,
    seen: &mut FxHashSet<(PredicateId, ChcExpr)>,
) -> Option<()> {
    if !seen.insert((predicate, formula.clone())) {
        return Some(());
    }
    if seen.len() > MAX_HOUDINI_CANDIDATES {
        return None;
    }
    scalar_candidate_node_count(problem, vars, &formula)?;
    pools
        .entry(predicate)
        .or_default()
        .push(CandidateAtom { formula });
    Some(())
}

pub(super) fn candidate_count(pools: &FxHashMap<PredicateId, Vec<CandidateAtom>>) -> usize {
    pools.values().map(Vec::len).sum()
}
