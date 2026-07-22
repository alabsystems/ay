// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterative Tarjan SCC algorithm and equivalence chain construction.
//!
//! This module contains the core SCC traversal (`run_round`), SCC member
//! processing (`process_scc`), and LRAT equivalence chain building
//! (`build_equiv_chains`, `bfs_path_to_repr`).
//!
//! Reference: CaDiCaL `decompose.cpp:130-356`

use crate::kani_compat::DetHashMap as HashMap;
use crate::literal::Literal;
use crate::watched::WatchedLists;

use super::{Decompose, DecomposeResult, EquivChain, TRAVERSED};

impl Decompose {
    /// Run one round of iterative Tarjan SCC on the binary implication graph.
    pub(super) fn run_round(
        &mut self,
        watches: &WatchedLists,
        num_vars: usize,
        vals: &[i8],
        frozen: &[u32],
        var_states: &[crate::solver::lifecycle::VarState],
        need_chains: bool,
    ) -> DecomposeResult {
        let num_lits = num_vars * 2;
        let mut result = DecomposeResult {
            equiv_chains: if need_chains {
                vec![EquivChain::default(); num_lits]
            } else {
                Vec::new()
            },
            ..DecomposeResult::default()
        };
        let mut dfs_idx: u32 = 0;

        for var_idx in 0..num_vars {
            // Skip inactive variables: assigned, eliminated, or previously substituted.
            // CaDiCaL: `if (!active(root_idx)) continue;` at decompose.cpp:176.
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue;
            }
            if var_idx < var_states.len() && var_states[var_idx].is_removed() {
                continue;
            }

            for sign in 0..2u32 {
                let root = Literal(var_idx as u32 * 2 + sign);

                if self.dfs[root.index()].min == TRAVERSED {
                    continue;
                }
                if self.dfs[root.index()].idx != 0 {
                    continue;
                }

                self.work.clear();
                self.work.push((root.0, 0));

                while let Some((parent_raw, mut child_pos)) = self.work.pop() {
                    let parent = Literal(parent_raw);
                    let pi = parent.index();

                    if self.dfs[pi].min == TRAVERSED {
                        continue;
                    }

                    if self.dfs[pi].idx == 0 {
                        // Pre-fix: first visit.
                        dfs_idx += 1;
                        self.dfs[pi].idx = dfs_idx;
                        self.dfs[pi].min = dfs_idx;
                        self.scc_stack.push(parent_raw);

                        // Traverse binary implications: parent is true, so
                        // ¬parent is false. Watch list of ¬parent contains
                        // binary clauses (¬parent ∨ child), meaning parent→child.
                    }

                    let neg_parent = parent.negated();
                    let wl = watches.get_watches(neg_parent);
                    let mut pushed_child = false;

                    while child_pos < wl.len() {
                        let wi = child_pos;
                        child_pos += 1;

                        if !wl.is_binary(wi) {
                            continue;
                        }

                        let child = wl.blocker(wi);
                        let ci = child.index();
                        let child_var = child.variable().index();

                        // Skip inactive literals: assigned or eliminated.
                        // CaDiCaL skips these via `active()` checks throughout.
                        if child_var * 2 < vals.len() && vals[child_var * 2] != 0 {
                            continue;
                        }
                        if child_var < var_states.len() && var_states[child_var].is_removed() {
                            continue;
                        }

                        if self.dfs[ci].min == TRAVERSED {
                            continue;
                        }

                        if self.dfs[ci].idx == 0 {
                            // Tree edge: suspend parent at the next child position
                            // and continue DFS with the child.
                            self.work.push((parent_raw, child_pos));
                            self.work.push((child.0, 0));
                            pushed_child = true;
                            break;
                        }

                        // Back/cross edge to a node still on the SCC stack.
                        // Tarjan uses the discovery index for this case.
                        if self.dfs[ci].idx < self.dfs[pi].min {
                            self.dfs[pi].min = self.dfs[ci].idx;
                        }
                    }

                    if pushed_child {
                        continue;
                    }

                    // Post-fix: all children processed.
                    if self.dfs[pi].idx == self.dfs[pi].min {
                        // SCC root found. Pop all members.
                        self.process_scc(
                            parent,
                            watches,
                            vals,
                            frozen,
                            var_states,
                            need_chains,
                            &mut result,
                        );
                        if result.unsat {
                            return result;
                        }
                    }

                    // Propagate low-link to the active parent frame.
                    if let Some((gp_raw, _)) = self.work.last() {
                        let gp_idx = Literal(*gp_raw).index();
                        if self.dfs[pi].min < self.dfs[gp_idx].min {
                            self.dfs[gp_idx].min = self.dfs[pi].min;
                        }
                    }
                }
            }
        }

        result
    }

    /// Process a completed SCC rooted at `root`.
    #[allow(clippy::too_many_arguments)]
    fn process_scc(
        &mut self,
        root: Literal,
        watches: &WatchedLists,
        vals: &[i8],
        frozen: &[u32],
        var_states: &[crate::solver::lifecycle::VarState],
        need_chains: bool,
        result: &mut DecomposeResult,
    ) {
        // Find the start of this SCC on the scc_stack.
        let mut scc_start = self.scc_stack.len();
        while scc_start > 0 {
            scc_start -= 1;
            if Literal(self.scc_stack[scc_start]) == root {
                break;
            }
        }

        let scc_members: Vec<u32> = self.scc_stack[scc_start..].to_vec();
        self.scc_stack.truncate(scc_start);

        // Mark all members as TRAVERSED.
        for &lit_raw in &scc_members {
            self.dfs[Literal(lit_raw).index()].min = TRAVERSED;
        }

        if scc_members.len() <= 1 {
            return; // Trivial SCC, no equivalences.
        }

        // Check for conflicting SCC (lit and ¬lit both present).
        for &lit_raw in &scc_members {
            let lit = Literal(lit_raw);
            let neg = lit.negated();
            if scc_members.contains(&neg.0) {
                result.unsat = true;
                let pos = Literal::positive(lit.variable());
                if lit.variable().index() * 2 < vals.len() && vals[lit.variable().index() * 2] == 0
                {
                    result.units.push(pos);
                    result.new_units += 1;
                }
                return;
            }
        }

        // Choose representative: literal with the smallest variable index.
        let mut repr = Literal(scc_members[0]);
        for &lit_raw in &scc_members[1..] {
            let lit = Literal(lit_raw);
            if lit.variable().index() < repr.variable().index() {
                repr = lit;
            }
        }

        // If representative is frozen, keep it. Otherwise check if any frozen
        // variable is in the SCC and promote it to representative.
        let repr_var = repr.variable().index();
        let repr_frozen = repr_var < frozen.len() && frozen[repr_var] > 0;
        if !repr_frozen {
            for &lit_raw in &scc_members {
                let lit = Literal(lit_raw);
                let vi = lit.variable().index();
                if vi < frozen.len() && frozen[vi] > 0 {
                    repr = lit;
                    break;
                }
            }
        }

        // CaDiCaL: decompose.cpp:432-433 — representative must not be eliminated or substituted.
        {
            let ri = repr.variable().index();
            debug_assert!(
                ri >= var_states.len() || !var_states[ri].is_removed(),
                "BUG: decompose representative var {} is removed (state {:?})",
                ri,
                var_states.get(ri),
            );
            let _ = &var_states;
        }

        // Build LRAT equivalence chains via BFS parent pointers (only when needed for proofs).
        // CaDiCaL decompose.cpp:260-356.
        // When !need_chains, skip the expensive BFS + 118K-element allocations (#3366).
        let chains = if need_chains {
            self.build_equiv_chains(repr, &scc_members, watches, vals, var_states)
        } else {
            HashMap::default()
        };

        // Map all SCC members to the representative.
        for &lit_raw in &scc_members {
            let lit = Literal(lit_raw);
            if lit == repr {
                continue;
            }

            let vi = lit.variable().index();
            if vi < frozen.len() && frozen[vi] > 0 {
                continue;
            }

            self.reprs[lit.index()] = repr;
            self.reprs[lit.negated().index()] = repr.negated();

            // Store equiv chains for this literal (only when LRAT proofs needed).
            if need_chains {
                if let Some(chain) = chains.get(&lit_raw) {
                    let li = lit.index();
                    if li < result.equiv_chains.len() {
                        result.equiv_chains[li] = chain.clone();
                    }
                }
            }

            result.substituted += 1;
        }
    }

    /// Build equivalence chains for all non-repr SCC members.
    ///
    /// Returns a map from literal raw value to its EquivChain.
    /// Each chain contains binary clause ClauseRef.0 values needed for
    /// LRAT hint generation.
    fn build_equiv_chains(
        &self,
        repr: Literal,
        scc_members: &[u32],
        watches: &WatchedLists,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
    ) -> HashMap<u32, EquivChain> {
        let mut chains = HashMap::default();
        if scc_members.len() <= 1 {
            return chains;
        }

        // Build set of SCC member literal indices for O(1) membership test.
        let mut in_scc = vec![false; self.dfs.len()];
        for &lit_raw in scc_members {
            in_scc[Literal(lit_raw).index()] = true;
        }

        // --- Forward BFS from repr ---
        // Discovers the path repr -> each member via binary implications.
        let num_lits = self.dfs.len();
        let mut parent_cref: Vec<u32> = vec![u32::MAX; num_lits];
        let mut parent_from: Vec<u32> = vec![u32::MAX; num_lits];
        let mut bfs_queue: Vec<u32> = Vec::new();
        bfs_queue.push(repr.0);

        while let Some(next_raw) = bfs_queue.pop() {
            let next = Literal(next_raw);
            let neg_next = next.negated();
            let wl = watches.get_watches(neg_next);
            for wi in 0..wl.len() {
                if !wl.is_binary(wi) {
                    continue;
                }
                let child = wl.blocker(wi);
                let ci = child.index();

                // Only visit SCC members.
                if ci >= num_lits || !in_scc[ci] {
                    continue;
                }
                // Skip inactive literals.
                let child_var = child.variable().index();
                if child_var * 2 < vals.len() && vals[child_var * 2] != 0 {
                    continue;
                }
                if child_var < var_states.len() && var_states[child_var].is_removed() {
                    continue;
                }
                // Skip already-visited.
                if parent_cref[ci] != u32::MAX || child == repr {
                    continue;
                }

                parent_cref[ci] = wl.clause_ref(wi).0;
                parent_from[ci] = next_raw;
                bfs_queue.push(child.0);
            }
        }

        // --- Build chains for each non-repr member ---
        for &lit_raw in scc_members {
            let lit = Literal(lit_raw);
            if lit == repr {
                continue;
            }

            // 1. repr_to_lit: walk parent pointers from lit back to repr,
            //    then reverse. Each step is a binary clause on the path
            //    repr -> ... -> lit.
            let mut fwd_chain = Vec::new();
            let mut cursor = lit_raw;
            while cursor != repr.0 && parent_cref[Literal(cursor).index()] != u32::MAX {
                fwd_chain.push(parent_cref[Literal(cursor).index()]);
                cursor = parent_from[Literal(cursor).index()];
            }
            fwd_chain.reverse(); // Now in order: repr -> ... -> lit

            // 2. lit_to_repr: BFS from lit to repr through binary implications,
            //    avoiding the forward-path edges to get the "other" SCC path.
            let rev_chain = self.bfs_path_to_repr(lit, repr, &in_scc, watches, vals, var_states);

            chains.insert(
                lit_raw,
                EquivChain {
                    repr_to_lit: fwd_chain,
                    lit_to_repr: rev_chain,
                },
            );
        }

        chains
    }

    /// BFS from `start` to `target` through binary implications among SCC members.
    /// Returns the sequence of ClauseRef.0 values along the path.
    fn bfs_path_to_repr(
        &self,
        start: Literal,
        target: Literal,
        in_scc: &[bool],
        watches: &WatchedLists,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
    ) -> Vec<u32> {
        let num_lits = self.dfs.len();
        // BFS parent tracking for this search.
        let mut visited = vec![false; num_lits];
        let mut bfs_parent_cref: Vec<u32> = vec![u32::MAX; num_lits];
        let mut bfs_parent_from: Vec<u32> = vec![u32::MAX; num_lits];
        let mut queue: Vec<u32> = Vec::new();

        visited[start.index()] = true;
        queue.push(start.0);

        let mut found = false;
        while let Some(next_raw) = queue.pop() {
            let next = Literal(next_raw);
            if next == target {
                found = true;
                break;
            }
            let neg_next = next.negated();
            let wl = watches.get_watches(neg_next);
            for wi in 0..wl.len() {
                if !wl.is_binary(wi) {
                    continue;
                }
                let child = wl.blocker(wi);
                let ci = child.index();
                if ci >= num_lits || !in_scc[ci] {
                    continue;
                }
                let child_var = child.variable().index();
                if child_var * 2 < vals.len() && vals[child_var * 2] != 0 {
                    continue;
                }
                if child_var < var_states.len() && var_states[child_var].is_removed() {
                    continue;
                }
                if visited[ci] {
                    continue;
                }
                visited[ci] = true;
                bfs_parent_cref[ci] = wl.clause_ref(wi).0;
                bfs_parent_from[ci] = next_raw;
                queue.push(child.0);

                if child == target {
                    found = true;
                    break;
                }
            }
            if found {
                break;
            }
        }

        if !found {
            return Vec::new();
        }

        // Walk back from target to start, collecting clause refs.
        let mut chain = Vec::new();
        let mut cursor = target.0;
        while cursor != start.0 && bfs_parent_cref[Literal(cursor).index()] != u32::MAX {
            chain.push(bfs_parent_cref[Literal(cursor).index()]);
            cursor = bfs_parent_from[Literal(cursor).index()];
        }
        chain.reverse(); // Now in order: start -> ... -> target
        chain
    }
}
