// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded whole-system Houdini for query-anchored ghost candidates.
//!
//! This module is deliberately not a proof authority. It constructs and checks
//! a complete model of the raw ghost problem, then hands that model to the
//! original-clause quantified certificate boundary. Only a successfully sealed
//! certificate may leave this module.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;

use crate::expr::evaluate_expr;
use crate::smt::{SmtContext, SmtResult, SmtValue};
use crate::{CancellationToken, ChcExpr, ChcProblem, ChcVar, ClauseHead, PredicateId};

use super::candidate_model::{complete_model, CandidateAtom};
use super::candidate_names::canonical_raw_variables;
use super::candidate_pool::{build_candidate_pools, candidate_count, MAX_HOUDINI_CANDIDATES};
use super::candidate_substitute::exact_substitute_scalar_candidate;
use super::certify::GhostPairCertificate;
use super::GhostPairSpec;

/// Executor calls are the expensive part of Houdini. The candidate route
/// declines beyond this fixed envelope and leaves the existing PDR path intact.
const MAX_HOUDINI_SMT_CALLS: usize = 4_096;
/// Shared charge for formula substitutions across all rounds and query checks.
const MAX_HOUDINI_INSTANTIATED_NODES: usize = 8_000_000;

#[derive(Debug)]
pub(crate) struct QueryAnchoredSeal {
    pub(crate) certificate: Arc<GhostPairCertificate>,
    pub(crate) candidates: usize,
    pub(crate) survivors: usize,
    pub(crate) rounds: usize,
    pub(crate) smt_calls: usize,
}

#[derive(Default)]
struct HoudiniWork {
    smt_calls: usize,
    instantiated_nodes: usize,
}

impl HoudiniWork {
    fn charge_instantiation(&mut self, nodes: usize) -> Option<()> {
        self.instantiated_nodes = self.instantiated_nodes.checked_add(nodes)?;
        (self.instantiated_nodes <= MAX_HOUDINI_INSTANTIATED_NODES).then_some(())
    }

    fn charge_smt_call(&mut self) -> Option<()> {
        self.smt_calls = self.smt_calls.checked_add(1)?;
        (self.smt_calls <= MAX_HOUDINI_SMT_CALLS).then_some(())
    }
}

/// Try the query-anchored candidate lane and return only sealed evidence.
///
/// `synthesis_deadline` bounds candidate generation and Houdini. The later
/// `certificate_deadline` preserves a caller-selected acceptance reserve. Both
/// are absolute and never renewed. A miss is heuristic-only: callers may
/// continue with the existing raw/preprocessed PDR route while time remains.
pub(crate) fn try_query_anchored_and_seal(
    original: &ChcProblem,
    raw_ghost: &ChcProblem,
    spec: &GhostPairSpec,
    synthesis_deadline: Instant,
    certificate_deadline: Instant,
    cancellation: &CancellationToken,
    term_memory_limit: Option<usize>,
) -> Option<QueryAnchoredSeal> {
    if synthesis_deadline > certificate_deadline || stopped(cancellation, synthesis_deadline) {
        return None;
    }

    let canonical =
        canonical_raw_variables(original, raw_ghost, spec, cancellation, synthesis_deadline)?;
    let mut pools = build_candidate_pools(
        original,
        raw_ghost,
        spec,
        &canonical,
        cancellation,
        synthesis_deadline,
    )?;
    let candidates = candidate_count(&pools);
    if candidates == 0 || candidates > MAX_HOUDINI_CANDIDATES {
        return None;
    }

    let mut work = HoudiniWork::default();
    let rounds = houdini_fixpoint(
        raw_ghost,
        &canonical,
        &mut pools,
        &mut work,
        cancellation,
        synthesis_deadline,
    )?;
    check_all_queries(
        raw_ghost,
        &canonical,
        &pools,
        &mut work,
        cancellation,
        synthesis_deadline,
    )?;
    let model = complete_model(raw_ghost, &canonical, &pools, || {
        stopped(cancellation, synthesis_deadline)
    })?;
    let survivors = candidate_count(&pools);

    if stopped(cancellation, certificate_deadline) || SmtContext::new().exact_term_memory_exceeded()
    {
        return None;
    }
    let certificate_budget = certificate_deadline.saturating_duration_since(Instant::now());
    if certificate_budget.is_zero() {
        return None;
    }
    let certificate = GhostPairCertificate::certify_and_seal_with_term_memory_limit(
        original,
        spec.clone(),
        model,
        Some(certificate_budget),
        term_memory_limit,
    )?;
    if stopped(cancellation, certificate_deadline) || SmtContext::new().exact_term_memory_exceeded()
    {
        return None;
    }

    Some(QueryAnchoredSeal {
        certificate,
        candidates,
        survivors,
        rounds,
        smt_calls: work.smt_calls,
    })
}

fn stopped(cancellation: &CancellationToken, deadline: Instant) -> bool {
    cancellation.is_cancelled()
        || Instant::now() >= deadline
        || ay_core::TermStore::global_memory_exceeded()
}

fn houdini_fixpoint(
    problem: &ChcProblem,
    canonical: &FxHashMap<PredicateId, Vec<ChcVar>>,
    pools: &mut FxHashMap<PredicateId, Vec<CandidateAtom>>,
    work: &mut HoudiniWork,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<usize> {
    let initial_count = candidate_count(pools);
    let _synthesis_deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);

    for round in 1..=initial_count.checked_add(1)? {
        let mut drops: FxHashSet<(PredicateId, usize)> = FxHashSet::default();
        for clause in problem.clauses() {
            if stopped(cancellation, deadline) {
                return None;
            }
            let ClauseHead::Predicate(head_predicate, head_args) = &clause.head else {
                continue;
            };
            let Some(head_candidates) = pools.get(head_predicate) else {
                continue;
            };
            if head_candidates.is_empty() {
                continue;
            }

            let body = instantiate_body(
                problem,
                clause,
                canonical,
                pools,
                work,
                cancellation,
                deadline,
            )?;
            let mut instantiated_heads = Vec::with_capacity(head_candidates.len());
            for candidate in head_candidates {
                instantiated_heads.push(instantiate_candidate(
                    candidate,
                    canonical.get(head_predicate)?,
                    head_args,
                    work,
                    cancellation,
                    deadline,
                )?);
            }
            let head_conjunction =
                ChcExpr::and_all_checked(instantiated_heads.iter().cloned(), || {
                    stopped(cancellation, deadline)
                })?;
            let violation = ChcExpr::and(body.clone(), ChcExpr::not(head_conjunction));
            match checked_sat(problem, violation, work, cancellation, deadline)? {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                SmtResult::Unknown => return None,
                SmtResult::Sat(model) => {
                    for (index, head) in instantiated_heads.iter().enumerate() {
                        if stopped(cancellation, deadline) {
                            return None;
                        }
                        if matches!(evaluate_expr(head, &model), Some(SmtValue::Bool(false))) {
                            drops.insert((*head_predicate, index));
                        }
                    }
                    if !drops
                        .iter()
                        .any(|(predicate, _)| predicate == head_predicate)
                    {
                        // Model evaluation can abstain on array-derived terms.
                        // Exact per-candidate checks preserve the all-or-nothing
                        // Houdini boundary without trusting evaluator coverage.
                        for (index, head) in instantiated_heads.into_iter().enumerate() {
                            if stopped(cancellation, deadline) {
                                return None;
                            }
                            let violation = ChcExpr::and(body.clone(), ChcExpr::not(head));
                            match checked_sat(problem, violation, work, cancellation, deadline)? {
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => {}
                                SmtResult::Sat(_) => {
                                    drops.insert((*head_predicate, index));
                                }
                                SmtResult::Unknown => return None,
                            }
                        }
                    }
                }
            }
        }

        if drops.is_empty() {
            return Some(round);
        }
        drop_marked_candidates(pools, &drops);
    }
    None
}

fn drop_marked_candidates(
    pools: &mut FxHashMap<PredicateId, Vec<CandidateAtom>>,
    drops: &FxHashSet<(PredicateId, usize)>,
) {
    for (predicate, candidates) in pools {
        let mut index = 0usize;
        candidates.retain(|_| {
            let keep = !drops.contains(&(*predicate, index));
            index += 1;
            keep
        });
    }
}

fn check_all_queries(
    problem: &ChcProblem,
    canonical: &FxHashMap<PredicateId, Vec<ChcVar>>,
    pools: &FxHashMap<PredicateId, Vec<CandidateAtom>>,
    work: &mut HoudiniWork,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<()> {
    let _synthesis_deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let mut saw_query = false;
    for clause in problem.clauses() {
        if stopped(cancellation, deadline) {
            return None;
        }
        if !matches!(clause.head, ClauseHead::False) {
            continue;
        }
        saw_query = true;
        let body = instantiate_body(
            problem,
            clause,
            canonical,
            pools,
            work,
            cancellation,
            deadline,
        )?;
        match checked_sat(problem, body, work, cancellation, deadline)? {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Sat(_) | SmtResult::Unknown => return None,
        }
    }
    saw_query.then_some(())
}

fn instantiate_body(
    _problem: &ChcProblem,
    clause: &crate::HornClause,
    canonical: &FxHashMap<PredicateId, Vec<ChcVar>>,
    pools: &FxHashMap<PredicateId, Vec<CandidateAtom>>,
    work: &mut HoudiniWork,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<ChcExpr> {
    let mut conjuncts = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        conjuncts.push(constraint.clone());
    }
    for (predicate, args) in &clause.body.predicates {
        if stopped(cancellation, deadline) {
            return None;
        }
        let Some(candidates) = pools.get(predicate) else {
            continue;
        };
        let vars = canonical.get(predicate)?;
        for candidate in candidates {
            conjuncts.push(instantiate_candidate(
                candidate,
                vars,
                args,
                work,
                cancellation,
                deadline,
            )?);
        }
    }
    ChcExpr::and_all_checked(conjuncts, || stopped(cancellation, deadline))
}

fn instantiate_candidate(
    candidate: &CandidateAtom,
    vars: &[ChcVar],
    args: &[ChcExpr],
    work: &mut HoudiniWork,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<ChcExpr> {
    let remaining = MAX_HOUDINI_INSTANTIATED_NODES.checked_sub(work.instantiated_nodes)?;
    let substituted = exact_substitute_scalar_candidate(
        &candidate.formula,
        vars,
        args,
        cancellation,
        deadline,
        remaining,
    )?;
    work.charge_instantiation(substituted.expanded_nodes)?;
    Some(substituted.formula)
}

fn checked_sat(
    problem: &ChcProblem,
    formula: ChcExpr,
    work: &mut HoudiniWork,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Option<SmtResult> {
    if stopped(cancellation, deadline) {
        return None;
    }
    work.charge_smt_call()?;
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        return None;
    }
    let mut smt = problem.make_smt_context();
    if smt.exact_term_memory_exceeded() {
        return None;
    }
    let result = smt.check_sat_with_timeout(&formula, remaining);
    if stopped(cancellation, deadline) || smt.exact_term_memory_exceeded() {
        return None;
    }
    Some(result)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_houdini_tests.rs"]
mod tests;

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_houdini_wide_tests.rs"]
mod wide_tests;
