// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Demand-driven, proof-neutral scalar support for query-anchored candidates.

#[path = "candidate_support_closure.rs"]
mod closure;
#[path = "candidate_support_store.rs"]
mod store_scan;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};

use super::candidate::QueryAnchoredGhostCandidate;
use super::candidate_flow::CandidateControl;
use super::candidate_usage::required_original_positions_bounded;
use super::GhostPairSpec;

use closure::ordered_bounded_closure;
use store_scan::collect_relevant_store_index_vars;

type SupportKey = (PredicateId, usize, u32);

const MAX_NONZERO_BV_WIDTH: u32 = 128;
const MAX_SUPPORT_GRAPH_NODES: usize = 4_096;
const MAX_SUPPORT_GRAPH_EDGES: usize = 65_536;

struct ScanBudget(usize);

struct CandidateDemands {
    active: FxHashSet<PredicateId>,
    arrays: FxHashMap<PredicateId, FxHashSet<usize>>,
    direct: FxHashSet<SupportKey>,
}

#[derive(Default)]
struct SupportScan {
    store_seeds: FxHashSet<SupportKey>,
    graph: FxHashMap<SupportKey, Vec<SupportKey>>,
    graph_nodes: FxHashSet<SupportKey>,
    graph_edges: FxHashSet<(SupportKey, SupportKey)>,
}

struct PredicateColumns<'a> {
    predicate: PredicateId,
    args: &'a [ChcExpr],
    positions: FxHashMap<ChcVar, usize>,
}

impl ScanBudget {
    fn new() -> Self {
        Self(crate::expr::MAX_PREPROCESSING_NODES)
    }

    fn charge(&mut self, control: Option<CandidateControl<'_>>) -> Option<()> {
        if self.0 == 0 || control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        self.0 -= 1;
        Some(())
    }
}

/// Return deterministically capped `(predicate, original position, width)`
/// supports, ordered as direct use, store-index seed, then exact CFG closure.
pub(super) fn demanded_nonzero_supports(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    candidates: &[QueryAnchoredGhostCandidate],
    control: Option<CandidateControl<'_>>,
) -> Option<Vec<(PredicateId, usize, u32)>> {
    if control.is_some_and(CandidateControl::stopped) {
        return None;
    }
    let mut budget = ScanBudget::new();
    let demands = collect_candidate_demands(problem, spec, candidates, &mut budget, control)?;
    let mut scan = collect_support_graph(problem, &demands, &mut budget, control)?;
    for neighbors in scan.graph.values_mut() {
        budget.charge(control)?;
        neighbors.sort_unstable();
        neighbors.dedup();
    }
    ordered_bounded_closure(demands.direct, scan.store_seeds, &scan.graph, control)
}

fn collect_candidate_demands(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    candidates: &[QueryAnchoredGhostCandidate],
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<CandidateDemands> {
    let mut active = FxHashSet::default();
    let mut arrays: FxHashMap<PredicateId, FxHashSet<usize>> = FxHashMap::default();
    let mut direct = FxHashSet::default();
    for candidate in candidates {
        budget.charge(control)?;
        let declaration = problem.get_predicate(candidate.predicate)?;
        let layout = spec.preds.get(&candidate.predicate)?;
        if layout.original_arity != declaration.arg_sorts.len()
            || candidate
                .vars
                .iter()
                .take(layout.original_arity)
                .zip(&declaration.arg_sorts)
                .any(|(variable, sort)| variable.sort != *sort)
        {
            return None;
        }
        active.insert(candidate.predicate);
        let mut stopped = || control.is_some_and(CandidateControl::stopped);
        let required = required_original_positions_bounded(
            &candidate.vars,
            &candidate.formula,
            layout,
            spec.n,
            &mut budget.0,
            &mut stopped,
        )?;
        for position in required {
            budget.charge(control)?;
            match declaration.arg_sorts.get(position)? {
                ChcSort::Array(_, _) => {
                    arrays
                        .entry(candidate.predicate)
                        .or_default()
                        .insert(position);
                }
                ChcSort::BitVec(width @ 1..=MAX_NONZERO_BV_WIDTH) => {
                    direct.insert((candidate.predicate, position, *width));
                }
                _ => {}
            }
        }
    }
    Some(CandidateDemands {
        active,
        arrays,
        direct,
    })
}

fn collect_support_graph(
    problem: &ChcProblem,
    demands: &CandidateDemands,
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<SupportScan> {
    let mut scan = SupportScan::default();
    for clause in problem.clauses() {
        budget.charge(control)?;
        scan_support_clause(problem, clause, demands, &mut scan, budget, control)?;
    }
    Some(scan)
}

fn scan_support_clause(
    problem: &ChcProblem,
    clause: &HornClause,
    demands: &CandidateDemands,
    scan: &mut SupportScan,
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<()> {
    let [(body_predicate, body_args)] = clause.body.predicates.as_slice() else {
        return Some(());
    };
    let body_is_active = demands.active.contains(body_predicate);
    let head_is_active = match &clause.head {
        ClauseHead::Predicate(predicate, _) => demands.active.contains(predicate),
        ClauseHead::False => false,
    };
    if !body_is_active && !head_is_active {
        return Some(());
    }
    let body = predicate_columns(problem, *body_predicate, body_args, budget, control)?;
    let head = match &clause.head {
        ClauseHead::Predicate(predicate, args) => Some(predicate_columns(
            problem, *predicate, args, budget, control,
        )?),
        ClauseHead::False => None,
    };
    if body_is_active && head_is_active {
        add_correspondence_edges(problem, &body, head.as_ref()?, scan)?;
    }
    seed_store_indices(
        problem,
        clause,
        demands,
        &body,
        head.as_ref(),
        body_is_active,
        head_is_active,
        scan,
        budget,
        control,
    )
}

fn predicate_columns<'a>(
    problem: &ChcProblem,
    predicate: PredicateId,
    args: &'a [ChcExpr],
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<PredicateColumns<'a>> {
    let declaration = problem.get_predicate(predicate)?;
    let positions = unique_plain_variables(args, &declaration.arg_sorts, budget, control)?;
    Some(PredicateColumns {
        predicate,
        args,
        positions,
    })
}

fn add_correspondence_edges(
    problem: &ChcProblem,
    body: &PredicateColumns<'_>,
    head: &PredicateColumns<'_>,
    scan: &mut SupportScan,
) -> Option<()> {
    for (variable, body_position) in &body.positions {
        let Some(head_position) = head.positions.get(variable) else {
            continue;
        };
        let Some(body_key) = support_key(problem, body.predicate, *body_position)? else {
            continue;
        };
        let Some(head_key) = support_key(problem, head.predicate, *head_position)? else {
            continue;
        };
        if body_key.2 != head_key.2 {
            return None;
        }
        add_graph_edge(
            body_key,
            head_key,
            &mut scan.graph,
            &mut scan.graph_nodes,
            &mut scan.graph_edges,
        )?;
    }
    Some(())
}

fn seed_store_indices(
    problem: &ChcProblem,
    clause: &HornClause,
    demands: &CandidateDemands,
    body: &PredicateColumns<'_>,
    head: Option<&PredicateColumns<'_>>,
    body_is_active: bool,
    head_is_active: bool,
    scan: &mut SupportScan,
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<()> {
    let tracked_bases =
        demanded_array_variables(demands.arrays.get(&body.predicate), &body.positions);
    let (tracked_results, demanded_head_args) = match head.filter(|_| head_is_active) {
        Some(head) => {
            let demanded_args = match demands.arrays.get(&head.predicate) {
                Some(demanded) => demanded
                    .iter()
                    .map(|position| head.args.get(*position))
                    .collect::<Option<Vec<_>>>()?,
                None => Vec::new(),
            };
            (
                demanded_array_variables(demands.arrays.get(&head.predicate), &head.positions),
                demanded_args,
            )
        }
        None => (FxHashSet::default(), Vec::new()),
    };

    let mut index_variables = FxHashSet::default();
    for expression in demanded_head_args {
        collect_relevant_store_index_vars(
            expression,
            &tracked_bases,
            &tracked_results,
            true,
            &mut index_variables,
            budget,
            control,
        )?;
    }
    if let Some(constraint) = clause.body.constraint.as_ref() {
        collect_relevant_store_index_vars(
            constraint,
            &tracked_bases,
            &tracked_results,
            false,
            &mut index_variables,
            budget,
            control,
        )?;
    }

    for variable in index_variables {
        budget.charge(control)?;
        if body_is_active {
            insert_seed(problem, body, &variable, &mut scan.store_seeds)?;
        }
        if let Some(head) = head.filter(|_| head_is_active) {
            insert_seed(problem, head, &variable, &mut scan.store_seeds)?;
        }
    }
    Some(())
}

fn insert_seed(
    problem: &ChcProblem,
    columns: &PredicateColumns<'_>,
    variable: &ChcVar,
    seeds: &mut FxHashSet<SupportKey>,
) -> Option<()> {
    if let Some(position) = columns.positions.get(variable) {
        if let Some(key) = support_key(problem, columns.predicate, *position)? {
            seeds.insert(key);
        }
    }
    Some(())
}

fn support_key(
    problem: &ChcProblem,
    predicate: PredicateId,
    position: usize,
) -> Option<Option<SupportKey>> {
    let sort = problem.get_predicate(predicate)?.arg_sorts.get(position)?;
    Some(match sort {
        ChcSort::BitVec(width @ 1..=MAX_NONZERO_BV_WIDTH) => Some((predicate, position, *width)),
        _ => None,
    })
}

fn unique_plain_variables(
    args: &[ChcExpr],
    declared_sorts: &[ChcSort],
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<FxHashMap<ChcVar, usize>> {
    if args.len() != declared_sorts.len() {
        return None;
    }
    let mut by_name: FxHashMap<String, (ChcVar, usize, bool)> = FxHashMap::default();
    for (position, (argument, declared_sort)) in args.iter().zip(declared_sorts).enumerate() {
        budget.charge(control)?;
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

fn demanded_array_variables(
    demanded: Option<&FxHashSet<usize>>,
    positions: &FxHashMap<ChcVar, usize>,
) -> FxHashSet<ChcVar> {
    let Some(demanded) = demanded else {
        return FxHashSet::default();
    };
    positions
        .iter()
        .filter_map(|(variable, position)| demanded.contains(position).then_some(variable.clone()))
        .collect()
}

fn add_graph_edge(
    left: SupportKey,
    right: SupportKey,
    graph: &mut FxHashMap<SupportKey, Vec<SupportKey>>,
    nodes: &mut FxHashSet<SupportKey>,
    edges: &mut FxHashSet<(SupportKey, SupportKey)>,
) -> Option<()> {
    if left == right {
        return Some(());
    }
    let edge = if left < right {
        (left, right)
    } else {
        (right, left)
    };
    if !edges.insert(edge) {
        return Some(());
    }
    if edges.len() > MAX_SUPPORT_GRAPH_EDGES {
        return None;
    }
    nodes.insert(left);
    nodes.insert(right);
    if nodes.len() > MAX_SUPPORT_GRAPH_NODES {
        return None;
    }
    graph.entry(left).or_default().push(right);
    graph.entry(right).or_default().push(left);
    Some(())
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_support_tests.rs"]
mod tests;
