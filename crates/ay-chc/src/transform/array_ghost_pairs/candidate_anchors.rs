// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate-only positive-disjunction decomposition.
//!
//! NOT(OR bad_i) = AND NOT(bad_i). Every leaf must yield its whole-anchor
//! proposal; a missing leaf discards the entire fallback. The original query,
//! full Houdini checker and original certificate stay intact. Typed synthesis
//! separately case-splits its private raw queries before ghost rewriting.

use super::*;

pub(super) struct Source<'a> {
    pub(super) problem: &'a ChcProblem,
    pub(super) spec: &'a GhostPairSpec,
    pub(super) predicate: PredicateId,
    pub(super) arg_positions: &'a FxHashMap<ChcVar, usize>,
    pub(super) layout: &'a GhostPredSpec,
    pub(super) control: Option<CandidateControl<'a>>,
}

/// Outer None means refusal/stop; inner None means an unsupported anchor.
/// Both the failed whole attempt and all fallback leaves borrow these SAME
/// batch meters. No conjunction distribution or ghost-slot expansion occurs.
pub(super) fn candidates_for_constraint(
    source: Source<'_>,
    constraint: &ChcExpr,
    census_remaining: &mut usize,
    rewrite_remaining: &mut usize,
) -> Option<Option<Vec<QueryAnchoredGhostCandidate>>> {
    if let Some(candidates) = source.anchor(constraint, census_remaining, rewrite_remaining)? {
        return Some(Some(candidates));
    }
    let ChcExpr::Op(ChcOp::Or, _) = constraint else {
        return Some(None);
    };
    let leaves = positive_disjuncts(constraint, census_remaining, source.control)?;
    let mut candidates = Vec::new();
    for leaf in leaves {
        let Some(additions) = source.anchor(leaf, census_remaining, rewrite_remaining)? else {
            // Never return proposals for only a supported subset of the OR.
            return Some(None);
        };
        let count = candidates.len().checked_add(additions.len())?;
        if count > MAX_PROPAGATED_CANDIDATES {
            return None;
        }
        candidates.try_reserve(additions.len()).ok()?;
        candidates.extend(additions);
    }
    if source.control.is_some_and(CandidateControl::stopped) {
        return None;
    }
    Some(Some(candidates))
}

impl Source<'_> {
    fn anchor(
        &self,
        constraint: &ChcExpr,
        census_remaining: &mut usize,
        rewrite_remaining: &mut usize,
    ) -> Option<Option<Vec<QueryAnchoredGhostCandidate>>> {
        let Some(local_reads) = local_index_reads(
            constraint,
            self.arg_positions,
            self.layout,
            self.spec.n,
            census_remaining,
            &mut || self.control.is_some_and(CandidateControl::stopped),
        ) else {
            return self.unsupported(census_remaining);
        };
        let declaration = self.problem.get_predicate(self.predicate)?;
        let identity: Vec<_> = (0..declaration.arg_sorts.len()).map(Some).collect();
        let Some(candidate) = rewrite_query_for_target(
            self.problem,
            self.spec,
            constraint,
            self.arg_positions,
            self.layout,
            declaration.id,
            &declaration.arg_sorts,
            self.layout,
            &identity,
            &local_reads,
            rewrite_remaining,
            self.control,
        ) else {
            return self.unsupported(rewrite_remaining);
        };
        let required = required_original_positions(
            &candidate.vars,
            &candidate.formula,
            self.layout,
            self.spec.n,
        )?;
        let transports = propagated_transports(
            self.problem,
            self.spec,
            self.predicate,
            self.layout,
            &required,
            self.control,
        )?;
        rewrite_transports_for_query(
            QueryTransportSource {
                problem: self.problem,
                spec: self.spec,
                constraint,
                arg_positions: self.arg_positions,
                layout: self.layout,
                local_reads: &local_reads,
                control: self.control,
            },
            candidate,
            transports,
            rewrite_remaining,
        )
        .map(Some)
    }

    fn unsupported(&self, remaining: &usize) -> Option<Option<Vec<QueryAnchoredGhostCandidate>>> {
        if *remaining == 0 || self.control.is_some_and(CandidateControl::stopped) {
            None
        } else {
            Some(None)
        }
    }
}

/// Borrow complete positive OR leaves in source order; opaque/non-OR nodes
/// remain whole leaves. Charge nodes and outgoing links before extending either
/// scratch vector, using the existing batch-wide census allowance.
fn positive_disjuncts<'a>(
    constraint: &'a ChcExpr,
    remaining: &mut usize,
    control: Option<CandidateControl<'_>>,
) -> Option<Vec<&'a ChcExpr>> {
    positive_disjuncts_with_progress(constraint, &mut |amount| charge(remaining, amount, control))
}

/// The typed synthesis source builder supplies its SAME SourceControl here.
/// This helper borrows references and never constructs a source/proof object.
pub(in crate::transform::array_ghost_pairs) fn positive_disjuncts_with_progress<'a>(
    constraint: &'a ChcExpr,
    offer: &mut dyn FnMut(usize) -> Option<()>,
) -> Option<Vec<&'a ChcExpr>> {
    offer(1)?;
    let mut stack = Vec::new();
    stack.try_reserve(1).ok()?;
    stack.push((constraint, 0usize));
    let mut leaves = Vec::new();
    while !stack.is_empty() {
        offer(1)?;
        let (node, depth) = stack.pop()?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        if let ChcExpr::Op(ChcOp::Or, args) = node {
            if args.len() < 2 {
                return None;
            }
            offer(args.len())?;
            stack.try_reserve(args.len()).ok()?;
            stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
        } else {
            if leaves.len() >= MAX_PROPAGATED_CANDIDATES {
                return None;
            }
            offer(1)?;
            leaves.try_reserve(1).ok()?;
            leaves.push(node);
        }
    }
    offer(0)?;
    (!leaves.is_empty()).then_some(leaves)
}

fn charge(
    remaining: &mut usize,
    amount: usize,
    control: Option<CandidateControl<'_>>,
) -> Option<()> {
    if control.is_some_and(CandidateControl::stopped) {
        return None;
    }
    let Some(rest) = remaining.checked_sub(amount) else {
        *remaining = 0;
        return None;
    };
    *remaining = rest;
    Some(())
}

#[cfg(test)]
#[path = "candidate_disjunct_tests.rs"]
mod tests;
