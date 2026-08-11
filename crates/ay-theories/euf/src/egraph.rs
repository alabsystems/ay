// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental E-graph operations for `EufSolver`.
//!
//! Contains the worklist-based incremental merge infrastructure:
//! E-node initialization, find/union operations, class iteration,
//! congruence table management, and incremental rebuild.

use ay_core::term::{TermData, TermId};
use ay_core::TheoryLit;
use tracing::info;

use crate::solver::EufSolver;
use crate::types::{CongruenceTable, ENode, EqualityReason, MergeReason};

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
        if std::env::var_os("AY_DEBUG_EUF_INIT").is_some() {
            use std::sync::atomic::{AtomicU64, Ordering};
            static INIT_COUNT: AtomicU64 = AtomicU64::new(0);
            let n = INIT_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
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
        self.enodes.reserve(self.terms.len());
        if !scoped {
            self.bool_sorted.reserve(self.terms.len());
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
        if std::env::var_os("AY_EUF_CONG_UNDO_DEBUG").is_some() {
            safe_eprintln!(
                "[cong-undo] func_apps={} threshold={} active={}",
                self.func_apps.len(),
                self.cong_undo_min_func_apps,
                self.cong_undo_active()
            );
        }
        // #euf-inc-diseq-undo threshold diagnostic (measurement-only).
        if std::env::var_os("AY_EUF_DISEQ_UNDO_DEBUG").is_some() {
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
        let needed = (term_id + 1) as usize;
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

    /// Process the merge worklist until fixed point.
    ///
    /// Each merge can discover new congruences, which are added to the worklist.
    /// We process until no more merges are pending.
    pub(crate) fn incremental_propagate(&mut self) -> usize {
        let debug = self.debug_euf;
        let mut iterations = 0;
        let initial_pending = self.to_merge.len();

        while let Some(merge) = self.to_merge.pop_front() {
            iterations += 1;
            self.incremental_merge(merge.a, merge.b, merge.reason);
            // #8469: Track merge epoch for disequality dirty tracking.
            self.merge_epoch = self.merge_epoch.wrapping_add(1);
        }

        if debug && iterations > 0 {
            safe_eprintln!(
                "[EUF] incremental_propagate: {} merges processed",
                iterations
            );
        }

        if iterations > 0 {
            info!(
                target: "ay::euf",
                initial_pending,
                merges_processed = iterations,
                pending_after = self.to_merge.len(),
                "EUF incremental propagation summary"
            );
        }

        iterations
    }

    /// Process pending merges in the incremental E-graph.
    ///
    /// In true incremental mode, equalities are queued in record_assignment(),
    /// and we just process the worklist here. No full rebuild needed.
    pub(crate) fn incremental_rebuild(&mut self) {
        let debug = self.debug_euf;
        let initial_pending = self.to_merge.len();
        let mut merge_steps = 0usize;

        // If dirty but no pending merges, enodes might not be initialized
        // This happens on first call or after reset
        if !self.enodes_init {
            self.init_enodes();
        }

        // #euf-idle-rebuild: re-derive the merge queue from surviving state only
        // after an event that may have discarded or unwound merges (pop/reset/
        // soft_reset/unwind — see `egraph_requeue_needed`). Between such events
        // the queue is maintained incrementally at assert time, so the previous
        // `dirty && to_merge.is_empty()` trigger — which fired on every BCP
        // batch containing any non-equality Bool assignment — degenerated into
        // an O(|assigns| log |assigns|) scan per batch (80s of an 81s hwbench
        // firewire_tree.3 solve).
        if self.egraph_requeue_needed {
            self.refill_incremental_merge_queue_from_state();
        }

        // Process all pending merges from record_assignment()
        if !self.to_merge.is_empty() {
            if debug {
                safe_eprintln!(
                    "[EUF] incremental_rebuild: processing {} pending merges",
                    self.to_merge.len()
                );
            }
            merge_steps += self.incremental_propagate();
        }

        // Merge Bool-valued theory atoms sharing the same truth value.
        // Same logic as merge_bool_valued_atoms() but uses the incremental
        // merge path (to_merge queue) instead of uf.union(). (#4610)
        let bool_merge_candidates = self.incremental_merge_bool_valued_atoms();
        // #euf-idle-rebuild: both requeue consumers (queue refill above, bool
        // full rescan inside the call above) have now run; return to the
        // incremental feed until the next pop/reset/unwind.
        self.egraph_requeue_needed = false;
        if !self.to_merge.is_empty() {
            merge_steps += self.incremental_propagate();
        }

        // ITE axiom: when the condition of ite(c, t, e) is assigned, merge the
        // ITE term with the selected branch (incremental path). (#5081)
        // Uses pre-indexed ITE term list to avoid O(|terms|) scan (#5575).
        self.init_ite_terms();
        let mut ite_merge_count = 0usize;
        // #euf-ite-worklist: scan only the ITE terms an assignment could have
        // unblocked, not all of them.
        //
        // The body below fires only when the condition has a value, so the ONLY
        // ITE terms worth visiting are those whose condition was assigned since
        // the last sweep — `pending_ite`, maintained at assert time via the
        // `ite_by_cond` index. The old code rescanned every ITE term on every
        // rebuild: 1,471,446,450 iterations producing 300,988 merges (0.02%
        // useful), and `rebuild_closure` still measures 21% of self time on
        // hwbench instances after the clone fix.
        //
        // `ite_sweep_full_needed` is the escape hatch, set on exactly the events
        // that set `egraph_requeue_needed` (pop / reset / soft_reset / unwind).
        // After those, merges have been discarded or unwound, so a previously
        // "already merged" ITE may need re-merging and the worklist can no longer
        // be trusted — fall back to the full scan. This mirrors the same fix
        // already applied to the merge queue three blocks above, whose comment
        // records the identical bug costing "80s of an 81s hwbench solve".
        let sweep: Vec<u32> = if self.ite_sweep_full_needed {
            self.ite_sweep_full_needed = false;
            self.pending_ite.clear();
            self.ite_terms.clone()
        } else {
            std::mem::take(&mut self.pending_ite)
        };
        for idx in sweep {
            let term_id = TermId(idx);
            // #euf-ite-sweep: this loop runs on EVERY rebuild over EVERY ITE
            // term — profiled at 1,471,446,450 iterations producing 300,988
            // merges (0.02% useful) on firewire_tree.5, inside a
            // `rebuild_closure` that is 40% of AY self time.
            //
            // Two fixes here, both semantics-preserving (same merges, same
            // order):
            //   1. Read `cond`/`then`/`else` by REFERENCE. The old code did
            //      `self.terms.get(term_id).clone()` just to destructure —
            //      cloning a `TermData` per iteration, ~1.5e9 times. That clone
            //      and its matching drop are what showed up as
            //      `drop_in_place<TermData>` (4.7% of self time).
            //   2. Test the condition's assignment FIRST and `continue` when it
            //      is unassigned, which is the overwhelmingly common case. The
            //      body below only ever fires when `cond_val` is `Some`, so
            //      skipping earlier changes nothing except the work done to get
            //      there.
            let (cond, then_t, else_t) = match self.terms.get(term_id) {
                TermData::Ite(c, t, e) => (*c, *t, *e),
                _ => continue,
            };
            let cond_val = match self.terms.get(cond) {
                TermData::Not(inner) => {
                    let inner = *inner;
                    self.assigns.get(&inner).map(|&v| !v)
                }
                _ => self.assigns.get(&cond).copied(),
            };
            {
                if let Some(val) = cond_val {
                    let branch = if val { then_t } else { else_t };
                    self.ensure_enodes_size(term_id.0);
                    self.ensure_enodes_size(branch.0);
                    let r1 = self.enode_find_const(term_id.0);
                    let r2 = self.enode_find_const(branch.0);
                    if r1 != r2 {
                        self.to_merge.push_back(MergeReason {
                            a: term_id.0,
                            b: branch.0,
                            reason: EqualityReason::Ite {
                                condition: cond,
                                value: val,
                            },
                        });
                        // Propagate ITE-derived equality to other theories via
                        // Nelson-Oppen (incremental path). (#5081)
                        let reason = vec![TheoryLit::new(cond, val)];
                        self.queue_pending_propagation(
                            term_id,
                            branch,
                            reason,
                            "incremental ITE branch equality",
                        );
                        ite_merge_count += 1;
                    }
                }
            }
        }
        if !self.to_merge.is_empty() {
            merge_steps += self.incremental_propagate();
        }

        // Sync E-graph representatives to legacy UF so all callers
        // (model extraction, explain, tests) see consistent state. O(n) pass.
        self.sync_egraph_to_uf();

        self.dirty = false;

        if merge_steps > 0
            || bool_merge_candidates > 0
            || ite_merge_count > 0
            || initial_pending > 0
        {
            info!(
                target: "ay::euf",
                assignments = self.assigns.len(),
                initial_pending,
                bool_merge_candidates,
                merge_steps,
                equality_edges = self.equality_edges.len(),
                "EUF incremental rebuild summary"
            );
        }
    }
}
