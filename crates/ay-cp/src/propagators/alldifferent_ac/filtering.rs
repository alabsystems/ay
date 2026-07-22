// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Matching, SCC decomposition, and edge filtering for AllDifferent AC.
//!
//! Extracted from `mod.rs` to keep each file under 500 lines.
//! Contains: augmenting-path matching, conflict explanation, Kosaraju's SCC,
//! free-value reachability, and unsupported-edge filtering.

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult};
use crate::trail::IntegerTrail;

use super::{AllDifferentAc, UNMATCHED};

impl AllDifferentAc {
    /// Augmenting path BFS from an unmatched variable.
    /// Returns true if an augmenting path was found and the matching updated.
    ///
    /// Uses pre-allocated `ws_val_parent` workspace. Caller must have cleared
    /// `ws_visited_vars` and `ws_visited_vals` before each call.
    pub(super) fn augmenting_path(&mut self, start_var: usize) -> bool {
        self.ws_bfs_queue.clear();
        self.ws_val_parent.fill(UNMATCHED);

        self.ws_bfs_queue.push_back(start_var as u32);
        self.ws_visited_vars[start_var] = true;

        while let Some(var_i) = self.ws_bfs_queue.pop_front() {
            let var_idx = var_i as usize;
            for &val_idx in &self.ws_adj[var_idx] {
                let vi = val_idx as usize;
                if self.ws_visited_vals[vi] {
                    continue;
                }
                self.ws_visited_vals[vi] = true;
                self.ws_val_parent[vi] = var_i;

                let matched_var = self.val_match[vi];
                if matched_var == UNMATCHED {
                    // Found augmenting path — trace back and flip.
                    let mut cur_val = val_idx;
                    loop {
                        let p_var = self.ws_val_parent[cur_val as usize];
                        let prev_val = self.var_match[p_var as usize];
                        self.var_match[p_var as usize] = cur_val;
                        self.val_match[cur_val as usize] = p_var;
                        if prev_val == UNMATCHED {
                            break;
                        }
                        cur_val = prev_val;
                    }
                    return true;
                }

                let mv = matched_var as usize;
                if !self.ws_visited_vars[mv] {
                    self.ws_visited_vars[mv] = true;
                    self.ws_bfs_queue.push_back(matched_var);
                }
            }
        }

        false
    }

    /// Compute maximum matching. Returns true if a complete matching exists.
    pub(super) fn compute_matching(&mut self) -> bool {
        for (var_i, var_adj) in self.ws_adj.iter().enumerate().take(self.n_vars) {
            let val_idx = self.var_match[var_i];
            if val_idx != UNMATCHED && !var_adj.contains(&val_idx) {
                self.val_match[val_idx as usize] = UNMATCHED;
                self.var_match[var_i] = UNMATCHED;
            }
        }

        for var_i in 0..self.n_vars {
            if self.var_match[var_i] != UNMATCHED {
                continue;
            }
            self.ws_visited_vars.fill(false);
            self.ws_visited_vals.fill(false);

            if !self.augmenting_path(var_i) {
                return false;
            }
        }

        true
    }

    /// Build conflict explanation from the Hall set discovered when
    /// the augmenting-path search fails.
    ///
    /// Uses pre-allocated `ws_visited_vars` / `ws_visited_vals` workspace.
    pub(super) fn build_conflict(
        &mut self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> PropagationResult {
        self.ws_visited_vars.fill(false);
        self.ws_visited_vals.fill(false);

        for var_i in 0..self.n_vars {
            if self.var_match[var_i] != UNMATCHED {
                continue;
            }
            self.ws_bfs_queue.clear();
            self.ws_bfs_queue.push_back(var_i as u32);
            self.ws_visited_vars[var_i] = true;

            while let Some(vi) = self.ws_bfs_queue.pop_front() {
                for &val_idx in &self.ws_adj[vi as usize] {
                    let vv = val_idx as usize;
                    if self.ws_visited_vals[vv] {
                        continue;
                    }
                    self.ws_visited_vals[vv] = true;
                    let mv = self.val_match[vv];
                    if mv != UNMATCHED && !self.ws_visited_vars[mv as usize] {
                        self.ws_visited_vars[mv as usize] = true;
                        self.ws_bfs_queue.push_back(mv);
                    }
                }
            }
            break;
        }

        let mut reasons = Vec::new();
        for (var_i, &visited) in self.ws_visited_vars.iter().enumerate().take(self.n_vars) {
            if !visited {
                continue;
            }
            if !self.collect_var_reasons(self.vars[var_i], trail, encoder, &mut reasons) {
                // Explanation incomplete — bail to avoid unsound learned clause (#5986).
                return PropagationResult::NoChange;
            }
        }

        if reasons.is_empty() {
            return PropagationResult::NoChange;
        }

        let expl = Explanation::new(reasons);
        PropagationResult::Conflict(expl.into_conflict_clause())
    }

    /// Kosaraju's SCC on the residual graph.
    ///
    /// Residual graph edges:
    /// - Matched (var_i, val_j): val_j → var_i
    /// - Free (var_i, val_j): var_i → val_j
    ///
    /// Free (unmatched) values are handled in `filter_unsupported` and
    /// never pruned regardless of SCC membership.
    ///
    /// Node numbering: 0..n_vars = variables, n_vars..n_vars+n_vals = values.
    ///
    /// Uses pre-allocated workspace: ws_scc_fwd, ws_scc_rev, ws_scc_visited,
    /// ws_scc_finish, ws_scc_id. Results stored in ws_scc_id.
    pub(super) fn compute_sccs(&mut self) {
        let total = self.n_vars + self.n_vals;

        // Clear workspace adjacency lists.
        for v in self.ws_scc_fwd.iter_mut().take(total) {
            v.clear();
        }
        for v in self.ws_scc_rev.iter_mut().take(total) {
            v.clear();
        }

        for var_i in 0..self.n_vars {
            let matched_val = self.var_match[var_i];
            for &val_idx in &self.ws_adj[var_i] {
                let val_node = self.n_vars + val_idx as usize;
                if val_idx == matched_val {
                    self.ws_scc_fwd[val_node].push(var_i);
                    self.ws_scc_rev[var_i].push(val_node);
                } else {
                    self.ws_scc_fwd[var_i].push(val_node);
                    self.ws_scc_rev[val_node].push(var_i);
                }
            }
        }

        // Pass 1: forward DFS, record finish order.
        self.ws_scc_visited.fill(false);
        self.ws_scc_finish.clear();

        for start in 0..total {
            if self.ws_scc_visited[start] {
                continue;
            }
            self.ws_scc_stack1.clear();
            self.ws_scc_stack1.push((start, 0));
            self.ws_scc_visited[start] = true;
            while let Some((node, idx)) = self.ws_scc_stack1.last_mut() {
                if *idx < self.ws_scc_fwd[*node].len() {
                    let next = self.ws_scc_fwd[*node][*idx];
                    *idx += 1;
                    if !self.ws_scc_visited[next] {
                        self.ws_scc_visited[next] = true;
                        self.ws_scc_stack1.push((next, 0));
                    }
                } else {
                    self.ws_scc_finish.push(*node);
                    self.ws_scc_stack1.pop();
                }
            }
        }

        // Pass 2: reverse DFS in reverse finish order.
        self.ws_scc_id.fill(UNMATCHED);
        let mut current_scc: u32 = 0;

        for fi in (0..self.ws_scc_finish.len()).rev() {
            let start = self.ws_scc_finish[fi];
            if self.ws_scc_id[start] != UNMATCHED {
                continue;
            }
            self.ws_scc_stack2.clear();
            self.ws_scc_stack2.push(start);
            self.ws_scc_id[start] = current_scc;
            while let Some(node) = self.ws_scc_stack2.pop() {
                for ri in 0..self.ws_scc_rev[node].len() {
                    let prev = self.ws_scc_rev[node][ri];
                    if self.ws_scc_id[prev] == UNMATCHED {
                        self.ws_scc_id[prev] = current_scc;
                        self.ws_scc_stack2.push(prev);
                    }
                }
            }
            current_scc += 1;
        }
    }

    /// Compute which nodes are reachable from free (unmatched) values
    /// in the residual graph via BFS on `ws_scc_rev`.
    ///
    /// Per Régin 1994: an edge (x, v) can be in a maximum matching if
    /// it's in an alternating cycle (captured by SCC) OR on an alternating
    /// path from a free vertex (captured by this reachability check).
    /// Without this check, edges reachable from free values are incorrectly
    /// pruned, causing false UNSAT in optimization problems like golomb_ruler_7.
    ///
    /// Uses `ws_free_reachable` workspace. Must be called AFTER `compute_sccs()`
    /// which populates `ws_scc_rev`.
    ///
    /// Our residual graph uses: matched val→var, unmatched var→val.
    /// Régin's convention is the transpose: matched var→val, unmatched val→var.
    /// "Reachable from free value" in Régin's graph = reachable from free value
    /// via REVERSE edges in our graph. So we BFS over `ws_scc_rev`.
    pub(super) fn compute_free_reachable(&mut self) {
        self.ws_free_reachable.fill(false);
        // Seed BFS from all free (unmatched) value nodes.
        self.ws_scc_stack2.clear();
        for val_idx in 0..self.n_vals {
            if self.val_match[val_idx] == UNMATCHED {
                let val_node = self.n_vars + val_idx;
                if !self.ws_free_reachable[val_node] {
                    self.ws_free_reachable[val_node] = true;
                    self.ws_scc_stack2.push(val_node);
                }
            }
        }
        // BFS through REVERSE edges of our residual graph.
        // Our graph is the transpose of Régin's, so ws_scc_rev gives
        // forward traversal in Régin's directed graph.
        while let Some(node) = self.ws_scc_stack2.pop() {
            for fi in 0..self.ws_scc_rev[node].len() {
                let next = self.ws_scc_rev[node][fi];
                if !self.ws_free_reachable[next] {
                    self.ws_free_reachable[next] = true;
                    self.ws_scc_stack2.push(next);
                }
            }
        }
    }

    /// Filter unsupported edges using SCC decomposition and free-value
    /// reachability (Régin 1994).
    ///
    /// An edge (x, v) is unsupported (not in any max matching) iff:
    /// 1. It's not in the current matching, AND
    /// 2. v is not free (unmatched), AND
    /// 3. x and v are in different SCCs in the residual graph, AND
    /// 4. v is NOT reachable from any free value in the residual graph.
    ///
    /// Reasons are precomputed once per variable (bounds + holes of all OTHER
    /// variables), then shared across all unsupported edges for that variable.
    /// Reads SCC results from `ws_scc_id` and reachability from
    /// `ws_free_reachable`.
    pub(super) fn filter_unsupported(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Vec<Vec<ay_sat::Literal>> {
        let mut clauses = Vec::new();

        for var_i in 0..self.n_vars {
            let var = self.vars[var_i];
            let matched_val = self.var_match[var_i];

            // Check if this variable has any unsupported edges before
            // computing the (expensive) reasons vector.
            let has_unsupported = self.ws_adj[var_i].iter().any(|&val_idx| {
                let val_node = self.n_vars + val_idx as usize;
                val_idx != matched_val
                    && self.val_match[val_idx as usize] != UNMATCHED
                    && self.ws_scc_id[var_i] != self.ws_scc_id[val_node]
                    && !self.ws_free_reachable[val_node]
            });
            if !has_unsupported {
                continue;
            }

            // Precompute reasons once for all edges from this variable.
            let mut reasons = Vec::new();
            let mut reasons_complete = true;
            for var_j in 0..self.n_vars {
                if var_j == var_i {
                    continue;
                }
                if !self.collect_var_reasons(self.vars[var_j], trail, encoder, &mut reasons) {
                    reasons_complete = false;
                    break;
                }
            }
            if !reasons_complete {
                // Explanation incomplete — skip pruning for this variable (#5986).
                continue;
            }

            // Pre-negate reasons once. Each unsupported-edge clause is
            // `negated_reasons ∨ ¬ge(x,v) ∨ ge(x,v+1)`. Building from a
            // shared base avoids O(n²d) reason clones.
            let negated_base: Vec<ay_sat::Literal> =
                reasons.iter().map(|lit| lit.negated()).collect();

            for &val_idx in &self.ws_adj[var_i] {
                if val_idx == matched_val {
                    continue;
                }

                // Free values are always supported (Régin 1994, Theorem 2).
                if self.val_match[val_idx as usize] == UNMATCHED {
                    continue;
                }

                let val_node = self.n_vars + val_idx as usize;

                // Same SCC → edge is on an alternating cycle → supported.
                if self.ws_scc_id[var_i] == self.ws_scc_id[val_node] {
                    continue;
                }

                // Reachable from a free value → edge is on an alternating
                // path from a free vertex → supported (Régin 1994).
                if self.ws_free_reachable[val_node] {
                    continue;
                }

                // Unsupported edge: emit x != value.
                let value = self.idx_to_val[val_idx as usize];

                let ge_v = encoder.lookup_ge(var, value);
                let ge_v1 = encoder.lookup_ge(var, value + 1);

                if let (Some(ge_v_lit), Some(ge_v1_lit)) = (ge_v, ge_v1) {
                    let mut clause = Vec::with_capacity(negated_base.len() + 2);
                    clause.extend_from_slice(&negated_base);
                    clause.push(ge_v_lit.negated());
                    clause.push(ge_v1_lit);
                    clauses.push(clause);
                }
            }
        }

        clauses
    }
}
