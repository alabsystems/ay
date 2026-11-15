// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental E-graph operations for `EufSolver`.
//!
//! Contains the worklist-based incremental merge infrastructure:
//! E-node initialization, find/union operations, class iteration,
//! congruence table management, and incremental rebuild.

use ay_core::term::TermId;

use crate::solver::EufSolver;
use crate::types::{CongruenceTable, ENode};

mod rebuild;

impl EufSolver<'_> {
    // ========================================================================
    // Incremental E-graph methods (Phase 1)
    // ========================================================================

    /// Initialize the E-node array and populate parent pointers.
    ///
    /// This is called lazily on first use. It:
    /// 1. Creates an ENode for each term
    /// 2. Registers function applications with their arguments' parent lists
    /// 3. Populates the congruence table with initial signatures
    pub(crate) fn init_enodes(&mut self) {
        if ay_core::misc_cli_flags().debug_euf_init {
            use std::sync::atomic::{AtomicU64, Ordering};
            static INIT_COUNT: AtomicU64 = AtomicU64::new(0);
            let n = INIT_COUNT.fetch_add(1, Ordering::Relaxed).saturating_add(1);
            if n.is_multiple_of(1000) || n <= 3 {
                eprintln!(
                    "[euf-init-dbg] init_enodes call #{n} (terms={})",
                    self.terms.len()
                );
            }
        }
        if self.enodes_init {
            return;
        }

        // Ensure func_apps is initialized first
        self.init_func_apps();

        // Create ENodes for all terms + cache Bool-sortedness (static per term).
        //
        // #L2 (GROUP_E_FINDINGS.md §6b): `verify_euf_conflict` builds a FRESH
        // scoped solver on EVERY theory conflict (no sampling, unlike the
        // propagation path), and this loop is the O(|TermStore|) term of that
        // cost — measured at 596x over-scan (terms_touched 639,543,480 vs
        // scope_sum 1,072,517). `func_app_scope` is already honoured by
        // `init_func_apps`, but was never applied here.
        //
        // The `bool_sorted` table is a pure CACHE: both read sites
        // (`bool_atoms.rs:47` and `:208`) already fall back to
        // `self.terms.sort(term) == &Sort::Bool` for any index past its end,
        // and that fallback computes the identical value — the table is
        // populated from exactly that expression. So for a verification-scoped
        // solver we skip building it and let every lookup take the fallback:
        // BEHAVIOUR-IDENTICAL by construction, and cheap because a scoped
        // solver's `assigns` holds only the conflict's own literals rather than
        // a whole solve's trail.
        //
        // `enodes` is NOT skippable the same way — it is a DENSE Vec indexed by
        // term id (`self.enodes[arg as usize]`), so omitting entries would shift
        // every index and corrupt the e-graph. It stays full-length; `ENode::new`
        // is a trivial constructor, and the `sort()` lookup was the expensive
        // half being removed here.
        let scoped = self.func_app_scope.is_some();
        self.enodes.clear();
        self.bool_sorted.clear();
        // Capacity hints only: a failed reservation leaves `push` to grow the
        // vectors, so the contents are the same either way.
        let _ = self.enodes.try_reserve(self.terms.len());
        if !scoped {
            let _ = self.bool_sorted.try_reserve(self.terms.len());
        }
        for term_id in self.terms.term_ids() {
            if !scoped {
                self.bool_sorted
                    .push(self.terms.sort(term_id) == &ay_core::Sort::Bool);
            }
            self.enodes.push(ENode::new(term_id.0));
        }

        // Register parent pointers for function applications
        for meta in &self.func_apps {
            for &arg in &meta.args {
                self.enodes[arg as usize].parents.push(meta.term_id);
            }
        }

        // Populate initial congruence table
        self.cong_table.clear();
        for meta in &self.func_apps {
            let sig = CongruenceTable::make_signature(meta.func_hash, &meta.args, &self.enodes);
            self.cong_table.insert(meta.term_id, sig);
        }

        self.enodes_init = true;

        // #euf-inc-cong-undo threshold diagnostic (measurement-only).
        if ay_core::misc_cli_flags().euf_cong_undo_debug {
            safe_eprintln!(
                "[cong-undo] func_apps={} threshold={} active={}",
                self.func_apps.len(),
                self.cong_undo_min_func_apps,
                self.cong_undo_active()
            );
        }
        // #euf-inc-diseq-undo threshold diagnostic (measurement-only).
        if ay_core::misc_cli_flags().euf_diseq_undo_debug {
            safe_eprintln!(
                "[diseq-undo] func_apps={} threshold={} active={}",
                self.func_apps.len(),
                self.diseq_undo_min_func_apps,
                self.diseq_undo_active()
            );
        }
    }

    /// Ensure enodes array is sized for term_id.
    /// This handles terms added dynamically during CHC solving (lemma learning).
    pub(crate) fn ensure_enodes_size(&mut self, term_id: u32) {
        // Widen before adding: `term_id + 1` cannot overflow in usize.
        let Some(needed) = (term_id as usize).checked_add(1) else {
            return;
        };
        while self.enodes.len() < needed {
            let new_id = self.enodes.len() as u32;
            self.enodes.push(ENode::new(new_id));
        }
    }

    /// Find the representative of a term in the incremental E-graph.
    /// Uses path compression for efficiency.
    #[inline]
    pub(crate) fn enode_find(&mut self, x: u32) -> u32 {
        self.debug_assert_enode_index(x, "enode_find input");
        let root = self.enodes[x as usize].root;
        if root == x {
            return x;
        }
        // Path compression
        let final_root = self.enode_find(root);
        self.debug_assert_enode_root_fixed_point(final_root, "enode_find result");
        self.enodes[x as usize].root = final_root;
        final_root
    }

    /// Find representative without mutation (for use in const contexts)
    /// Returns x unchanged if term_id is beyond enodes array (dynamically added term).
    #[inline]
    /// Returns the equivalence class representative for term `x` (immutable).
    pub fn enode_find_const(&self, x: u32) -> u32 {
        if (x as usize) >= self.enodes.len() {
            return x; // Treat uninitialized terms as singletons
        }
        let mut curr = x;
        while self.enodes[curr as usize].root != curr {
            curr = self.enodes[curr as usize].root;
            if (curr as usize) >= self.enodes.len() {
                return x; // Corrupted state fallback
            }
        }
        curr
    }

    /// Bool-arg app pairs that the most recent `bool_arg_model_is_congruent`
    /// call found FORCED equal by congruence under the candidate model.
    ///
    /// Non-empty only after that guard has run. Intended for a caller that sees
    /// the guard downgrade `Sat` -> `Unknown` and wants to repair the model by
    /// injecting `(/\ a_i = b_i) -> f(a) = f(b)` for exactly these pairs and
    /// re-solving, instead of surrendering the check-sat. Read-only diagnostic.
    pub fn last_bool_arg_forced_edges(&self) -> &[(TermId, TermId)] {
        &self.last_bool_arg_forced_edges
    }

    /// Check if two terms are in the same equivalence class.
    pub fn are_equal(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return true;
        }
        self.enode_find_const(a.0) == self.enode_find_const(b.0)
    }

    /// Sync E-graph representatives to legacy UF structure.
    /// O(n log n) pass — sets UF parent of each term to its E-graph root.
    /// Uses enode_find_const (no path compression), so each find is O(depth)
    /// where depth is O(log n) due to merge-by-size. Total: O(n log n).
    /// This ensures callers using uf.find() see consistent results after
    /// incremental_rebuild(). (#5575)
    pub(crate) fn sync_egraph_to_uf(&mut self) {
        if !self.enodes_init {
            return;
        }
        self.uf.ensure_size(self.enodes.len());

        // INCREMENTAL sync (default): the UF mirror is a flattened copy of the
        // E-graph partition (`uf.parent[i] == enode_find_const(i)` for all i).
        // A class merge changes that value only for nodes whose root moved, and
        // a `pop` only for nodes whose root is restored — both are recorded in
        // `uf_dirty_nodes`. So when the invariant held at the previous sync, we
        // only need to refresh those nodes; every other node's mirror entry is
        // already correct. (Path compression in `enode_find` rewrites `root` but
        // preserves the representative `enode_find_const` resolves to, so it can
        // never invalidate a mirror entry and is deliberately not tracked.)
        //
        // SOUNDNESS: if there is ANY doubt the dirty set is complete (first sync,
        // enodes grew, or a hard/soft reset), `uf_full_sync_needed` forces the
        // full O(n) rebuild below — correct but slower. We never silently trust
        // an incomplete dirty set.
        if self.inc_sync_enabled && !self.uf_full_sync_needed {
            let dirty = std::mem::take(&mut self.uf_dirty_nodes);
            for node in dirty {
                let i = node as usize;
                if i < self.enodes.len() {
                    self.uf.parent[i] = self.enode_find_const(node);
                }
            }
            // Soundness self-check (debug only): the incremental update must
            // leave the mirror identical to a from-scratch full recompute. If
            // the dirty set ever misses a node, this fires in tests/fuzzing
            // before any wrong answer can escape.
            #[cfg(debug_assertions)]
            for i in 0..self.enodes.len() {
                debug_assert_eq!(
                    self.uf.parent[i],
                    self.enode_find_const(i as u32),
                    "BUG: incremental UF sync diverged from full recompute at node {i} \
                     (dirty-node cover incomplete)"
                );
            }
            return;
        }

        // FULL sync: rebuild the whole mirror and re-establish the invariant.
        for i in 0..self.enodes.len() {
            let root = self.enode_find_const(i as u32);
            self.uf.parent[i] = root;
        }
        self.uf_full_sync_needed = false;
        self.uf_dirty_nodes.clear();
    }

    /// Iterate over all members of an equivalence class.
    /// Uses the circular linked list.
    pub(crate) fn enode_class_iter(&self, root: u32) -> impl Iterator<Item = u32> + '_ {
        let start = root;
        let mut curr = root;
        let mut done = false;
        std::iter::from_fn(move || {
            if done {
                return None;
            }
            let result = curr;
            curr = self.enodes[curr as usize].next;
            if curr == start {
                done = true;
            }
            Some(result)
        })
    }

    // ========================================================================
    // Proof-forest methods (Z3-style explain)
    // Port of Z3's euf_egraph.cpp / euf_enode.cpp proof justification system.
    // The proof-forest is a tree embedded in ENode::proof_target/proof_justification
    // that records merge history for O(depth) explain without HashMap allocation.
    // ========================================================================

    /// Get function application info for a term (func_hash and argument ids).
    /// Clones the args Vec. Use get_func_app_sig() to avoid the clone when
    /// only the signature is needed.
    pub(crate) fn get_func_app_info(&self, term: u32) -> Option<(u64, Vec<u32>)> {
        let idx = self.func_app_index.get(&term)?;
        let meta = &self.func_apps[*idx];
        Some((meta.func_hash, meta.args.clone()))
    }

    /// Compute the congruence table signature for a function application term
    /// without cloning args — uses func_apps index directly (#5575).
    pub(crate) fn get_func_app_sig(&self, term: u32) -> Option<crate::types::Signature> {
        let idx = self.func_app_index.get(&term)?;
        let meta = &self.func_apps[*idx];
        Some(CongruenceTable::make_signature(
            meta.func_hash,
            &meta.args,
            &self.enodes,
        ))
    }
}
