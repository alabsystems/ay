// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strongly Connected Component (SCC) Detection for Cyclic Predicates.

use crate::{ChcProblem, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Strongly connected component of predicates
#[derive(Debug, Clone)]
pub(crate) struct PredicateSCC {
    /// Predicates in this SCC
    pub(crate) predicates: Vec<PredicateId>,
    /// True if SCC contains a cycle (len > 1 or self-loop)
    pub(crate) is_cyclic: bool,
}

/// SCC index for each predicate
#[derive(Default)]
pub(crate) struct SCCInfo {
    /// Which SCC each predicate belongs to
    pub(crate) predicate_to_scc: FxHashMap<PredicateId, usize>,
    /// All SCCs
    pub(crate) sccs: Vec<PredicateSCC>,
}

/// Tarjan's algorithm for strongly connected component detection.
///
/// Build predicate dependency graph: P depends on Q if Q appears in body of clause defining P.
/// Finds all SCCs and marks cyclic ones (size > 1 or self-loop).
pub(crate) fn tarjan_scc(problem: &ChcProblem) -> SCCInfo {
    let predicates = problem.predicates();
    let n = predicates.len();

    if n == 0 {
        return SCCInfo::default();
    }

    // Map predicate index to local index 0..n-1
    let pred_to_idx: FxHashMap<PredicateId, usize> = predicates
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id, i))
        .collect();

    // Build adjacency list: head -> body predicates
    // P depends on Q if Q appears in body of clause defining P
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for clause in problem.clauses() {
        if let Some(head_id) = clause.head.predicate_id() {
            if let Some(&head_idx) = pred_to_idx.get(&head_id) {
                for (body_id, _) in &clause.body.predicates {
                    if let Some(&body_idx) = pred_to_idx.get(body_id) {
                        if !adj[head_idx].contains(&body_idx) {
                            adj[head_idx].push(body_idx);
                        }
                    }
                }
            }
        }
    }

    // Compute raw SCCs using shared Tarjan implementation
    let raw_sccs = crate::tarjan::tarjan_scc_dense(n, |v| adj[v].clone());

    // Convert raw SCCs to PredicateSCC with predicate IDs and cyclicity
    let mut sccs: Vec<PredicateSCC> = Vec::with_capacity(raw_sccs.len());
    for raw_scc in raw_sccs {
        let scc_preds: Vec<PredicateId> = raw_scc.iter().map(|&w| predicates[w].id).collect();
        let root = raw_scc[raw_scc.len() - 1];
        let is_cyclic = raw_scc.len() > 1 || adj[root].contains(&root);

        sccs.push(PredicateSCC {
            predicates: scc_preds,
            is_cyclic,
        });
    }

    // Build predicate_to_scc mapping
    let mut predicate_to_scc = FxHashMap::default();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for pred in &scc.predicates {
            predicate_to_scc.insert(*pred, scc_idx);
        }
    }

    SCCInfo {
        predicate_to_scc,
        sccs,
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
