// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Helper functions extracted from `solver.rs` during #1561.

use crate::pdr::frame::Frame;
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

pub(super) fn build_canonical_predicate_vars(
    problem: &ChcProblem,
) -> FxHashMap<PredicateId, Vec<ChcVar>> {
    let mut map = FxHashMap::default();
    for pred in problem.predicates() {
        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
            .collect();
        map.insert(pred.id, vars);
    }
    map
}

pub(super) fn build_push_cache_deps(
    problem: &ChcProblem,
) -> FxHashMap<PredicateId, Vec<PredicateId>> {
    let mut deps: FxHashMap<PredicateId, FxHashSet<PredicateId>> = FxHashMap::default();

    for pred in problem.predicates() {
        deps.entry(pred.id).or_default();
        for clause in problem.clauses_defining(pred.id) {
            for (body_pred, _) in &clause.body.predicates {
                deps.entry(pred.id).or_default().insert(*body_pred);
            }
        }
    }

    let mut out = FxHashMap::default();
    for (pred, set) in deps {
        let mut v: Vec<PredicateId> = set.into_iter().collect();
        v.sort_by_key(|p| p.index());
        out.insert(pred, v);
    }
    out
}

/// Build the inverse of push_cache_deps: for each predicate P, which predicates have P in their body.
///
/// If Q's clause has P in body, then predicate_users[P] contains Q.
/// This is used for propagating discovered invariants from P to all predicates that depend on P.
pub(super) fn build_predicate_users(
    problem: &ChcProblem,
) -> FxHashMap<PredicateId, Vec<PredicateId>> {
    let mut users: FxHashMap<PredicateId, FxHashSet<PredicateId>> = FxHashMap::default();

    // Initialize empty sets for all predicates
    for pred in problem.predicates() {
        users.entry(pred.id).or_default();
    }

    // For each clause, the body predicates are "used by" the head predicate
    for clause in problem.clauses() {
        let Some(head_pred) = clause.head.predicate_id() else {
            continue;
        };

        for (body_pred, _) in &clause.body.predicates {
            users.entry(*body_pred).or_default().insert(head_pred);
        }
    }

    // Convert to sorted vectors for deterministic iteration
    let mut out = FxHashMap::default();
    for (pred, set) in users {
        let mut v: Vec<PredicateId> = set.into_iter().collect();
        v.sort_by_key(|p| p.index());
        out.insert(pred, v);
    }
    out
}

pub(super) fn build_frame_predicate_lemma_counts(frame: &Frame) -> FxHashMap<PredicateId, usize> {
    let mut counts: FxHashMap<PredicateId, usize> = FxHashMap::default();
    for lemma in &frame.lemmas {
        *counts.entry(lemma.predicate).or_insert(0) += 1;
    }
    counts
}

/// Compute the set of predicates reachable from init states via transitions.
///
/// A predicate is reachable if:
/// - It has direct fact clauses (init states), OR
/// - It's the head of a clause whose body predicates are all reachable
///
/// Computes hypergraph reachability from predicates with facts, following transitions
/// (body → head). For multi-body clauses, the head becomes reachable only once *all*
/// body predicates are reachable.
///
/// Complexity: O(total body predicate occurrences)
pub(super) fn compute_reachable_predicates(
    problem: &ChcProblem,
    predicates_with_facts: &FxHashSet<PredicateId>,
) -> FxHashSet<PredicateId> {
    let mut reachable = predicates_with_facts.clone();
    let mut worklist: Vec<PredicateId> = predicates_with_facts.iter().copied().collect();

    let clauses = problem.clauses();

    // Hypergraph reachability via "remaining prerequisites" counters.
    //
    // For each clause, track how many unique body predicates are not yet reachable.
    // When the count reaches 0, the head predicate becomes reachable.
    let mut remaining: Vec<u32> = vec![0; clauses.len()];

    // Watch-list: for each predicate, which clauses are waiting on it to become reachable.
    let mut watchers: Vec<Vec<usize>> = vec![Vec::new(); problem.predicates().len()];

    for (clause_idx, clause) in clauses.iter().enumerate() {
        if clause.body.predicates.is_empty() {
            continue;
        }

        // Dedup body predicate IDs to avoid double-counting duplicates.
        let mut body_preds: Vec<PredicateId> =
            clause.body.predicates.iter().map(|(p, _)| *p).collect();
        body_preds.sort_by_key(|p| p.index());
        body_preds.dedup();

        remaining[clause_idx] = body_preds.len() as u32;
        for p in body_preds {
            watchers[p.index()].push(clause_idx);
        }
    }

    while let Some(src_pred) = worklist.pop() {
        for &clause_idx in &watchers[src_pred.index()] {
            let r = &mut remaining[clause_idx];
            if *r == 0 {
                continue;
            }
            *r -= 1;
            if *r != 0 {
                continue;
            }

            let Some(head_pred) = clauses[clause_idx].head.predicate_id() else {
                continue;
            };
            if reachable.insert(head_pred) {
                worklist.push(head_pred);
            }
        }
    }

    reachable
}

pub(super) fn compute_push_cache_signature(
    lemma_counts: &FxHashMap<PredicateId, usize>,
    deps: &[PredicateId],
) -> u64 {
    // Small stable hash: FNV-1a over (pred_id, count) pairs in a deterministic order.
    const FNV_OFFSET: u64 = 14695981039346656037;
    const FNV_PRIME: u64 = 1099511628211;

    let mut h = FNV_OFFSET;
    for pred in deps {
        let idx = pred.index() as u64;
        let count = lemma_counts.get(pred).copied().unwrap_or(0) as u64;
        h ^= idx;
        h = h.wrapping_mul(FNV_PRIME);
        h ^= count;
        h = h.wrapping_mul(FNV_PRIME);
    }
    h
}

/// Detect triangular number pattern in blocked states.
///
/// Checks if blocked states fit c = k*(k+1)/2 + offset (triangular numbers).
/// This pattern appears in s_multipl benchmarks where an accumulator increments
/// by a counter that itself increments by 1.
///
/// Returns linear approximation bounds if the pattern is detected:
/// - c >= k (always true for positive triangular numbers)
/// - c >= k + offset (tighter bound using detected offset)
///
/// # Arguments
/// - `data_points`: Blocked state values as vectors
/// - `k_idx`: Index of the counter variable (k)
/// - `c_idx`: Index of the accumulator variable (c)
/// - `vars`: Variable definitions for building expressions
/// - `verbose`: Whether to print debug output
pub(super) fn detect_triangular_pattern(
    data_points: &[Vec<i64>],
    k_idx: usize,
    c_idx: usize,
    vars: &[ChcVar],
    verbose: bool,
) -> Option<Vec<ChcExpr>> {
    // Need at least 4 points to fit a quadratic pattern reliably
    if data_points.len() < 4 {
        return None;
    }

    // Extract (k, c) pairs from data points
    let pairs: Vec<(i64, i64)> = data_points.iter().map(|p| (p[k_idx], p[c_idx])).collect();

    // Check if all points satisfy c = k*(k+1)/2 + offset for some offset
    // Rearranged: offset = c - k*(k+1)/2
    let mut offsets = Vec::new();
    for &(k, c) in &pairs {
        // Skip negative k values (triangular numbers are defined for non-negative k)
        if k < 0 {
            return None;
        }
        let triangular = k.checked_mul(k + 1).map(|v| v / 2)?;
        let offset = c - triangular;
        offsets.push(offset);
    }

    // Check if all offsets are the same (exact fit)
    let first_offset = offsets[0];
    let exact_fit = offsets.iter().all(|&o| o == first_offset);

    // If not exact, check if offsets are within a small range (approximate fit)
    let min_offset = *offsets.iter().min()?;
    let max_offset = *offsets.iter().max()?;
    let approx_fit = max_offset - min_offset <= 5; // Allow 5 unit variance

    if !exact_fit && !approx_fit {
        return None;
    }

    // Pattern detected! Generate linear bounds.
    let k_var = &vars[k_idx];
    let c_var = &vars[c_idx];

    if verbose {
        safe_eprintln!(
            "PDR: Detected triangular pattern: {} ~ {}*({}+1)/2 + {} (exact: {})",
            c_var.name,
            k_var.name,
            k_var.name,
            min_offset,
            exact_fit
        );
    }

    let mut bounds = Vec::new();

    // Bound 1: c >= k (always true for triangular numbers + offset >= 0)
    // Note: k*(k+1)/2 >= k for k >= 0, so c >= triangular + offset >= k + offset
    // If offset >= 0, then c >= k
    if min_offset >= 0 {
        bounds.push(ChcExpr::ge(
            ChcExpr::var(c_var.clone()),
            ChcExpr::var(k_var.clone()),
        ));
    }

    // Bound 2: c >= k + min_offset (tighter bound using detected offset)
    if min_offset != 0 {
        bounds.push(ChcExpr::ge(
            ChcExpr::var(c_var.clone()),
            ChcExpr::add(ChcExpr::var(k_var.clone()), ChcExpr::int(min_offset)),
        ));
    }

    // Bound 3: c >= 2*k - 1 (lower bound on triangular: k*(k+1)/2 >= k for k>=0, tighter: >= 2k-1 for k>=2)
    // Only add if we have evidence k >= 2
    if pairs.iter().any(|(k, _)| *k >= 2) && min_offset >= -1 {
        bounds.push(ChcExpr::ge(
            ChcExpr::var(c_var.clone()),
            ChcExpr::sub(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(k_var.clone())),
                ChcExpr::int(1 - min_offset),
            ),
        ));
    }

    if bounds.is_empty() {
        None
    } else {
        Some(bounds)
    }
}

#[cfg(test)]
mod tests;
