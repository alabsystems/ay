// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Query-anchored candidate synthesis for the array ghost-pair route.
//!
//! A transformed query observes an array cell by passing a literal/index term
//! and the corresponding `select` value as ghost arguments.  Generic qualifier
//! mining deliberately accepts only predicate occurrences whose arguments are
//! distinct variables, so it cannot recover the resulting guarded scalar
//! safety formula.  This module performs that one semantic rewrite directly:
//!
//! ```text
//! P(a, x) /\ bad(select(a, t), x) -> false
//!       becomes the candidate
//! ghost_idx = t -> !bad(ghost_val, x)
//! ```
//!
//! The result has no proof authority; Houdini survivors must still be sealed
//! by `GhostPairCertificate` against every original clause.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;

use crate::{CancellationToken, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, PredicateId};

pub(super) use super::candidate_flow::MAX_PROPAGATED_CANDIDATES;
use super::candidate_flow::{propagated_transports, CandidateControl, CandidateTransport};
use super::candidate_query::bounded_query_slice;
#[cfg(test)]
use super::candidate_usage::exact_scalar_walk;
pub(super) use super::candidate_usage::scalar_candidate_node_count;
use super::candidate_usage::{query_argument_positions, required_original_positions};
use super::{GhostPairSpec, GhostPredSpec};

/// One meter shared by every query/target rewrite in a generation attempt.
const MAX_TOTAL_REWRITE_NODES: usize = crate::expr::MAX_PREPROCESSING_NODES;

/// One untrusted query-derived candidate over a ghost-extended signature.
#[derive(Debug, Clone)]
pub(crate) struct QueryAnchoredGhostCandidate {
    /// Predicate whose interpretation may include `formula`.
    pub(crate) predicate: PredicateId,
    /// Exact formal parameter list for the ghost-extended signature.
    pub(crate) vars: Vec<ChcVar>,
    /// Scalar, Boolean candidate over `vars`.
    pub(crate) formula: ChcExpr,
    /// Predicate occurring in the source query that produced this candidate.
    pub(crate) source_query_predicate: PredicateId,
}

pub(super) struct QueryCandidateBatch {
    pub(super) candidates: Vec<QueryAnchoredGhostCandidate>,
    pub(super) sink_predicates: Vec<PredicateId>,
}

/// Derive guarded ghost-value candidates from every query and propagate each
/// one through exact reverse CFG maps, plus the established compatible-prefix
/// fallback used for store-heavy transitions.
///
/// Each accepted query has exactly one body predicate, distinct variable
/// arguments with the declared sorts, and only supported array accesses that
/// fit the configured ghost slots. Unsupported queries are skipped as candidate
/// sources; Houdini still checks every raw query before any model can be sealed.
pub(crate) fn query_anchored_ghost_candidates(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
) -> Option<Vec<QueryAnchoredGhostCandidate>> {
    query_anchored_ghost_candidates_with_budget(problem, spec, MAX_TOTAL_REWRITE_NODES)
}

fn query_anchored_ghost_candidates_with_budget(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    total_rewrite_nodes: usize,
) -> Option<Vec<QueryAnchoredGhostCandidate>> {
    query_anchored_ghost_candidates_impl(problem, spec, total_rewrite_nodes, None)
        .map(|batch| batch.candidates)
}

/// Production entry point. Candidate discovery is heuristic, but its work is
/// still charged to the enclosing route's absolute deadline and cancellation
/// token. Returning `None` merely falls through to the established PDR path.
pub(super) fn query_anchored_ghost_candidates_controlled(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<QueryCandidateBatch> {
    query_anchored_ghost_candidates_impl(
        problem,
        spec,
        MAX_TOTAL_REWRITE_NODES,
        Some(CandidateControl {
            cancellation,
            deadline,
        }),
    )
}

fn query_anchored_ghost_candidates_impl(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    total_rewrite_nodes: usize,
    control: Option<CandidateControl<'_>>,
) -> Option<QueryCandidateBatch> {
    if control.is_some_and(CandidateControl::stopped)
        || spec.is_empty()
        || problem.validate().is_err()
    {
        return None;
    }
    let query_slice = bounded_query_slice(problem, control)?;
    let mut candidates = Vec::new();
    let mut seen: FxHashSet<(PredicateId, ChcExpr)> = FxHashSet::default();
    let mut rewrite_nodes_remaining = total_rewrite_nodes;
    for query in query_slice.anchors {
        if control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        let [(source_predicate, source_args)] = query.body.predicates.as_slice() else {
            continue;
        };
        let Some(constraint) = query.body.constraint.as_ref() else {
            continue;
        };
        let Some(source_decl) = problem.get_predicate(*source_predicate) else {
            continue;
        };
        let Some(source_layout) = spec.preds.get(source_predicate) else {
            continue;
        };
        let Some(source_arg_positions) =
            query_argument_positions(source_args, &source_decl.arg_sorts)
        else {
            continue;
        };

        let identity = CandidateTransport {
            predicate: *source_predicate,
            source_to_target: (0..source_decl.arg_sorts.len()).map(Some).collect(),
        };
        let Some(source_candidate) = rewrite_query_for_target(
            problem,
            spec,
            constraint,
            *source_predicate,
            &source_arg_positions,
            source_layout,
            source_decl.id,
            &source_decl.arg_sorts,
            source_layout,
            &identity.source_to_target,
            &mut rewrite_nodes_remaining,
            control,
        ) else {
            if rewrite_nodes_remaining == 0 || control.is_some_and(CandidateControl::stopped) {
                return None;
            }
            continue;
        };
        let required = required_original_positions(
            &source_candidate.vars,
            &source_candidate.formula,
            source_layout,
            spec.n,
        )?;

        let transports = propagated_transports(
            problem,
            spec,
            *source_predicate,
            source_layout,
            &required,
            control,
        )?;
        let query_candidates = rewrite_transports_for_query(
            QueryTransportSource {
                problem,
                spec,
                constraint,
                predicate: *source_predicate,
                arg_positions: &source_arg_positions,
                layout: source_layout,
                control,
            },
            source_candidate,
            transports,
            &mut rewrite_nodes_remaining,
        )?;
        append_unique_candidates(&mut candidates, &mut seen, query_candidates)?;
    }
    (!candidates.is_empty() || !query_slice.sink_predicates.is_empty()).then_some(
        QueryCandidateBatch {
            candidates,
            sink_predicates: query_slice.sink_predicates,
        },
    )
}

fn append_unique_candidates(
    candidates: &mut Vec<QueryAnchoredGhostCandidate>,
    seen: &mut FxHashSet<(PredicateId, ChcExpr)>,
    additions: Vec<QueryAnchoredGhostCandidate>,
) -> Option<()> {
    for candidate in additions {
        let key = (candidate.predicate, candidate.formula.clone());
        if seen.insert(key) {
            if candidates.len() >= MAX_PROPAGATED_CANDIDATES {
                return None;
            }
            candidates.push(candidate);
        }
    }
    Some(())
}

struct QueryTransportSource<'a> {
    problem: &'a ChcProblem,
    spec: &'a GhostPairSpec,
    constraint: &'a ChcExpr,
    predicate: PredicateId,
    arg_positions: &'a FxHashMap<ChcVar, usize>,
    layout: &'a GhostPredSpec,
    control: Option<CandidateControl<'a>>,
}

fn rewrite_transports_for_query(
    source: QueryTransportSource<'_>,
    source_candidate: QueryAnchoredGhostCandidate,
    transports: Vec<CandidateTransport>,
    rewrite_nodes_remaining: &mut usize,
) -> Option<Vec<QueryAnchoredGhostCandidate>> {
    let mut candidates = vec![source_candidate];
    for transport in transports {
        if source.control.is_some_and(CandidateControl::stopped) {
            return None;
        }
        let target_decl = source.problem.get_predicate(transport.predicate)?;
        let Some(target_layout) = source.spec.preds.get(&transport.predicate) else {
            continue;
        };
        let Some(candidate) = rewrite_query_for_target(
            source.problem,
            source.spec,
            source.constraint,
            source.predicate,
            source.arg_positions,
            source.layout,
            transport.predicate,
            &target_decl.arg_sorts,
            target_layout,
            &transport.source_to_target,
            rewrite_nodes_remaining,
            source.control,
        ) else {
            if *rewrite_nodes_remaining == 0
                || source.control.is_some_and(CandidateControl::stopped)
            {
                return None;
            }
            continue;
        };
        candidates.push(candidate);
    }
    Some(candidates)
}

fn rewrite_query_for_target(
    problem: &ChcProblem,
    spec: &GhostPairSpec,
    constraint: &ChcExpr,
    source_predicate: PredicateId,
    source_arg_positions: &FxHashMap<ChcVar, usize>,
    source_layout: &GhostPredSpec,
    target_predicate: PredicateId,
    target_sorts: &[ChcSort],
    target_layout: &GhostPredSpec,
    source_to_target: &[Option<usize>],
    rewrite_nodes_remaining: &mut usize,
    control: Option<CandidateControl<'_>>,
) -> Option<QueryAnchoredGhostCandidate> {
    if source_to_target.len() != source_layout.original_arity {
        return None;
    }
    let extended_sorts = spec.extended_sorts(target_predicate, target_sorts)?;
    let vars: Vec<ChcVar> = extended_sorts
        .into_iter()
        .enumerate()
        .map(|(position, sort)| {
            ChcVar::new(
                format!("__gqa{}_a{position}", target_predicate.index()),
                sort,
            )
        })
        .collect();
    let mut rewrite = CandidateRewrite {
        source_arg_positions,
        source_layout,
        target_layout,
        source_to_target,
        target_vars: &vars,
        pairs_per_array: spec.n,
        accesses: FxHashMap::default(),
        guards: Vec::new(),
        remaining: rewrite_nodes_remaining,
        control,
    };
    let safe = rewrite.rewrite(&ChcExpr::not(constraint.clone()), 0, false)?;
    if rewrite.accesses.is_empty() {
        return None;
    }
    let formula = ChcExpr::implies(ChcExpr::and_all(rewrite.guards), safe);
    scalar_candidate_is_well_formed(problem, &vars, &formula).then_some(
        QueryAnchoredGhostCandidate {
            predicate: target_predicate,
            vars,
            formula,
            source_query_predicate: source_predicate,
        },
    )
}

struct CandidateRewrite<'a> {
    source_arg_positions: &'a FxHashMap<ChcVar, usize>,
    source_layout: &'a GhostPredSpec,
    target_layout: &'a GhostPredSpec,
    source_to_target: &'a [Option<usize>],
    target_vars: &'a [ChcVar],
    pairs_per_array: usize,
    /// Distinct access term -> local slot within one array's ghost pairs.
    accesses: FxHashMap<(usize, ChcExpr), usize>,
    guards: Vec<ChcExpr>,
    /// Shared across every target and query in one generation attempt.
    remaining: &'a mut usize,
    control: Option<CandidateControl<'a>>,
}

impl CandidateRewrite<'_> {
    fn rewrite(&mut self, expr: &ChcExpr, depth: usize, inside_index: bool) -> Option<ChcExpr> {
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH
            || *self.remaining == 0
            || (*self.remaining & 0x1ff == 0) && self.control.is_some_and(CandidateControl::stopped)
        {
            return None;
        }
        *self.remaining -= 1;
        crate::expr::maybe_grow_expr_stack(|| {
            Some(match expr {
                ChcExpr::Var(var) => {
                    let source_position = *self.source_arg_positions.get(var)?;
                    let target_position = self
                        .source_to_target
                        .get(source_position)
                        .copied()
                        .flatten()?;
                    let target = self.target_vars.get(target_position)?.clone();
                    (target.sort == var.sort).then_some(ChcExpr::var(target))?
                }
                ChcExpr::Op(ChcOp::Select, args) if !inside_index && args.len() == 2 => {
                    self.rewrite_select(args, expr.sort(), depth)?
                }
                ChcExpr::Op(ChcOp::Select | ChcOp::Store, _) => return None,
                ChcExpr::Op(op, args) => ChcExpr::Op(
                    *op,
                    args.iter()
                        .map(|arg| self.rewrite(arg, depth + 1, inside_index).map(Arc::new))
                        .collect::<Option<Vec<_>>>()?,
                ),
                ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                    name.clone(),
                    sort.clone(),
                    args.iter()
                        .map(|arg| self.rewrite(arg, depth + 1, inside_index).map(Arc::new))
                        .collect::<Option<Vec<_>>>()?,
                ),
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Real(_, 1..) => expr.clone(),
                ChcExpr::Real(_, _)
                | ChcExpr::PredicateApp(_, _, _)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_)
                | ChcExpr::ConstArray(_, _) => return None,
            })
        })
    }

    fn rewrite_select(
        &mut self,
        args: &[Arc<ChcExpr>],
        result_sort: ChcSort,
        depth: usize,
    ) -> Option<ChcExpr> {
        let ChcExpr::Var(array_var) = args.first()?.as_ref() else {
            return None;
        };
        let array_position = *self.source_arg_positions.get(array_var)?;
        let source_array_index = self
            .source_layout
            .array_positions
            .iter()
            .position(|position| *position == array_position)?;
        let target_array_position = self
            .source_to_target
            .get(array_position)
            .copied()
            .flatten()?;
        let target_array_index = self
            .target_layout
            .array_positions
            .iter()
            .position(|position| *position == target_array_position)?;
        if self.target_vars.get(target_array_position)?.sort != array_var.sort {
            return None;
        }
        let index = self.rewrite(args.get(1)?.as_ref(), depth + 1, true)?;
        let expected_index_sort = self.source_layout.index_sorts.get(source_array_index)?;
        if index.sort() != *expected_index_sort
            || self.target_layout.index_sorts.get(target_array_index) != Some(expected_index_sort)
        {
            return None;
        }
        let key = (array_position, index.clone());
        let local_slot = match self.accesses.get(&key) {
            Some(slot) => *slot,
            None => {
                let used = self
                    .accesses
                    .keys()
                    .filter(|(position, _)| *position == array_position)
                    .count();
                if used >= self.pairs_per_array {
                    return None;
                }
                self.accesses.insert(key, used);
                used
            }
        };
        let slot = target_array_index
            .checked_mul(self.pairs_per_array)?
            .checked_add(local_slot)?;
        let ghost_index_position = self
            .target_layout
            .original_arity
            .checked_add(slot.checked_mul(2)?)?;
        let ghost_value_position = ghost_index_position.checked_add(1)?;
        let ghost_index = self.target_vars.get(ghost_index_position)?.clone();
        let ghost_value = self.target_vars.get(ghost_value_position)?.clone();
        if ghost_index.sort != *expected_index_sort || ghost_value.sort != result_sort {
            return None;
        }
        let guard = ChcExpr::eq(ChcExpr::var(ghost_index), index);
        if !self.guards.contains(&guard) {
            self.guards.push(guard);
        }
        Some(ChcExpr::var(ghost_value))
    }
}

/// Exact scalar/free-variable boundary for generated formulas.  The generic
/// `vars()` and `contains_array_ops()` helpers are best-effort at their depth
/// limits, so this boundary performs its own bounded all-or-nothing walk and
/// then invokes the normal QF type validator.
fn scalar_candidate_is_well_formed(
    problem: &ChcProblem,
    vars: &[ChcVar],
    formula: &ChcExpr,
) -> bool {
    scalar_candidate_node_count(problem, vars, formula).is_some()
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_tests.rs"]
mod tests;
