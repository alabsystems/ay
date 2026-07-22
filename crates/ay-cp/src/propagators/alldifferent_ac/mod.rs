// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AllDifferent arc-consistency (domain-consistency) propagator.
//!
//! Implements Régin's filtering algorithm for the all-different constraint:
//! after computing a maximum matching in the variable–value bipartite graph,
//! build the residual graph, compute its strongly connected components, and
//! remove any edge (x, v) that is neither in the matching nor in an SCC
//! (such edges cannot participate in any maximum matching).
//!
//! # Algorithm
//!
//! 1. Build bipartite graph from current bound intervals [lb, ub].
//! 2. Compute maximum matching via augmenting-path search seeded with the
//!    previous matching.
//! 3. If no complete matching exists, emit a conflict clause from the
//!    Hall set discovered by the failed augmenting-path search.
//! 4. Build the residual graph (matching edges: value→var, free edges:
//!    var→value). Edges to free (unmatched) values are always supported.
//! 5. Compute SCCs with Kosaraju's two-pass algorithm.
//! 6. For every non-matched, non-free edge (var, value) whose endpoints
//!    are in different SCCs, the value is unsupported: emit one `x != value`
//!    clause per propagation call to avoid batch-conflict issues.
//!
//! Complexity: O(n·d) per propagation call, where n = #variables, d = max
//! domain size. The SCC decomposition is linear in the residual graph size.
//!
//! # Reference
//!
//! - Régin, "A filtering algorithm for constraints of difference in CSPs"
//!   (AAAI 1994)
//! - OR-Tools CP-SAT `AllDifferentAC`: `ortools/sat/all_different.cc:201-408`

mod filtering;
#[cfg(test)]
mod tests;

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// Maximum domain size for which AC propagation is applied.
/// Variables with larger domains fall back to bounds-only propagation.
pub(crate) const ALLDIFF_AC_DOMAIN_LIMIT: i64 = 128;

/// Sentinel value: unmatched.
const UNMATCHED: u32 = u32::MAX;

/// AllDifferent arc-consistency propagator using Régin's algorithm.
#[derive(Debug)]
pub struct AllDifferentAc {
    vars: Vec<IntVarId>,
    n_vars: usize,
    /// Dense value remapping: concrete value → dense index.
    val_to_idx: Vec<(i64, u32)>,
    /// Reverse map: dense index → concrete value.
    idx_to_val: Vec<i64>,
    n_vals: usize,
    /// Matching: variable index → value index (UNMATCHED if unmatched).
    var_match: Vec<u32>,
    /// Matching: value index → variable index (UNMATCHED if unmatched).
    val_match: Vec<u32>,
    /// Pre-allocated workspace: bipartite adjacency lists (cleared each call).
    ws_adj: Vec<Vec<u32>>,
    /// Pre-allocated workspace: visited flags for matching/conflict BFS.
    ws_visited_vars: Vec<bool>,
    ws_visited_vals: Vec<bool>,
    /// Pre-allocated workspace: BFS parent tracking for augmenting paths.
    ws_val_parent: Vec<u32>,
    /// Pre-allocated workspace: BFS queue for augmenting path search.
    ws_bfs_queue: std::collections::VecDeque<u32>,
    /// Pre-allocated workspace: SCC forward adjacency (residual graph).
    ws_scc_fwd: Vec<Vec<usize>>,
    /// Pre-allocated workspace: SCC reverse adjacency (residual graph).
    ws_scc_rev: Vec<Vec<usize>>,
    /// Pre-allocated workspace: SCC visited flags (pass 1).
    ws_scc_visited: Vec<bool>,
    /// Pre-allocated workspace: SCC finish order (Kosaraju pass 1).
    ws_scc_finish: Vec<usize>,
    /// Pre-allocated workspace: SCC component IDs (Kosaraju pass 2).
    ws_scc_id: Vec<u32>,
    /// Pre-allocated workspace: DFS stack for Kosaraju pass 1.
    ws_scc_stack1: Vec<(usize, usize)>,
    /// Pre-allocated workspace: DFS stack for Kosaraju pass 2.
    ws_scc_stack2: Vec<usize>,
    /// Pre-allocated workspace: nodes reachable from free (unmatched) values
    /// in the residual graph. Used by `compute_free_reachable()`.
    ws_free_reachable: Vec<bool>,
}

impl AllDifferentAc {
    /// Create a new AC propagator for the given variables.
    ///
    /// `initial_values` provides the union of all values across all variable
    /// domains. The propagator builds a dense remapping from these values.
    pub fn new(vars: Vec<IntVarId>, initial_values: Vec<i64>) -> Self {
        let n_vars = vars.len();
        let mut sorted_vals = initial_values;
        sorted_vals.sort_unstable();
        sorted_vals.dedup();
        let n_vals = sorted_vals.len();

        let val_to_idx: Vec<(i64, u32)> = sorted_vals
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, i as u32))
            .collect();
        let idx_to_val = sorted_vals;

        Self {
            vars,
            n_vars,
            val_to_idx,
            idx_to_val,
            n_vals,
            var_match: vec![UNMATCHED; n_vars],
            val_match: vec![UNMATCHED; n_vals],
            ws_adj: (0..n_vars).map(|_| Vec::with_capacity(n_vals)).collect(),
            ws_visited_vars: vec![false; n_vars],
            ws_visited_vals: vec![false; n_vals],
            ws_val_parent: vec![UNMATCHED; n_vals],
            ws_bfs_queue: std::collections::VecDeque::with_capacity(n_vars),
            ws_scc_fwd: (0..n_vars + n_vals).map(|_| Vec::new()).collect(),
            ws_scc_rev: (0..n_vars + n_vals).map(|_| Vec::new()).collect(),
            ws_scc_visited: vec![false; n_vars + n_vals],
            ws_scc_finish: Vec::with_capacity(n_vars + n_vals),
            ws_scc_id: vec![UNMATCHED; n_vars + n_vals],
            ws_scc_stack1: Vec::with_capacity(n_vars + n_vals),
            ws_scc_stack2: Vec::with_capacity(n_vars + n_vals),
            ws_free_reachable: vec![false; n_vars + n_vals],
        }
    }

    /// Look up the dense index for a concrete value.
    #[cfg(test)]
    fn value_index(&self, val: i64) -> Option<u32> {
        self.val_to_idx
            .binary_search_by_key(&val, |&(v, _)| v)
            .ok()
            .map(|pos| self.val_to_idx[pos].1)
    }

    /// Build the current bipartite adjacency from the values that are still
    /// present in each variable's domain.
    ///
    /// Sparse holes from Wave 1A must be respected here or the matching can
    /// reason over values that the trail already forbids.
    ///
    /// Uses pre-allocated workspace `ws_adj` to avoid per-call allocation.
    fn build_adjacency(&mut self, trail: &IntegerTrail) {
        for (i, &var) in self.vars.iter().enumerate() {
            self.ws_adj[i].clear();
            for &(val, idx) in &self.val_to_idx {
                if trail.contains(var, val) {
                    self.ws_adj[i].push(idx);
                }
            }
        }
    }

    // augmenting_path, compute_matching, build_conflict, compute_sccs,
    // compute_free_reachable, filter_unsupported extracted to filtering.rs

    /// Collect bound and domain-hole reason literals for a variable.
    ///
    /// Adds `[var >= lb]`, `[var <= ub]`, and for each hole value `w` in
    /// `[lb, ub]` where `!trail.contains(var, w)`, adds `[var >= w+1]`.
    /// The hole literals are necessary for soundness: without them, the SAT
    /// solver sees the domain as the full interval `[lb, ub]`, overcounting
    /// available values and potentially deriving unsound learned clauses.
    ///
    /// Returns `false` if any required literal is missing from the encoder,
    /// indicating the explanation would be incomplete. Callers must bail
    /// (return `NoChange` or skip the clause) rather than use incomplete
    /// reasons — incomplete explanations cause unsound learned clauses
    /// during CDCL conflict analysis (#5986, #7224).
    fn collect_var_reasons(
        &self,
        var: IntVarId,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        reasons: &mut Vec<ay_sat::Literal>,
    ) -> bool {
        let lb = trail.lb(var);
        let ub = trail.ub(var);
        let Some(ge_lit) = encoder.lookup_ge(var, lb) else {
            return false;
        };
        reasons.push(ge_lit);
        let Some(le_lit) = encoder.lookup_le(var, ub) else {
            return false;
        };
        reasons.push(le_lit);
        // Include domain hole reasons: for each value w in [lb, ub] that is
        // not in the domain, the forbid_value clause ¬[x >= w] ∨ [x >= w+1]
        // was unit-propagated. Since [x >= w] is implied by [x >= lb] (as
        // lb <= w), the derived literal [x >= w+1] is the witness for the
        // hole. Including it as a reason ensures the explanation correctly
        // reflects the smaller effective domain size.
        //
        // We iterate all integers in [lb, ub], not just val_to_idx entries,
        // because val_to_idx is built from initial domain values which
        // already exclude root-level holes (forbid_value at registration).
        for w in lb..=ub {
            if !trail.contains(var, w) {
                let Some(ge_next) = encoder.lookup_ge(var, w + 1) else {
                    return false;
                };
                reasons.push(ge_next);
            }
        }
        true
    }
}

impl Propagator for AllDifferentAc {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Global
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        self.build_adjacency(trail);

        // Check for empty domains.
        for var_i in 0..self.n_vars {
            if self.ws_adj[var_i].is_empty() {
                let var = self.vars[var_i];
                let mut reasons = Vec::new();
                if !self.collect_var_reasons(var, trail, encoder, &mut reasons)
                    || reasons.is_empty()
                {
                    // Explanation incomplete — bail (#5986).
                    return PropagationResult::NoChange;
                }
                let expl = Explanation::new(reasons);
                return PropagationResult::Conflict(expl.into_conflict_clause());
            }
        }

        if !self.compute_matching() {
            return self.build_conflict(trail, encoder);
        }

        self.compute_sccs();
        self.compute_free_reachable();

        // Emit all unsupported-edge pruning clauses in one batch. Each clause
        // independently excludes a single value from a variable's domain, so
        // they don't interact. The theory callback (theory_callback.rs:106-113)
        // handles the "all literals false" case individually per clause. Emitting
        // all clauses avoids redundant matching + SCC recomputation on subsequent
        // propagate() calls (previously limited to 1 clause per call).
        let clauses = self.filter_unsupported(trail, encoder);

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    fn name(&self) -> &'static str {
        "alldifferent_ac"
    }
}
