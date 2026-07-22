// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF incremental merge operations.

use crate::solver::EufSolver;
use crate::types::{EqualityReason, MergeReason, UndoRecord};
use ay_core::term::TermId;
use tracing::{debug, trace};

impl EufSolver<'_> {
    /// Incrementally merge two equivalence classes.
    ///
    /// This is the core of the incremental E-graph. When two terms are asserted
    /// equal, we:
    /// 1. Find their representatives
    /// 2. Remove affected parent applications from the congruence table
    /// 3. Union the classes (smaller into larger for efficiency)
    /// 4. Reinsert parent applications - discovering new congruences
    /// 5. Record undo information for backtracking
    ///
    /// Complexity: O(parents(smaller_class)) per merge
    pub(crate) fn incremental_merge(&mut self, a: u32, b: u32, reason: EqualityReason) {
        let debug = self.debug_euf;
        self.debug_assert_enode_index(a, "incremental_merge lhs");
        self.debug_assert_enode_index(b, "incremental_merge rhs");

        let mut r1 = self.enode_find(a);
        let mut r2 = self.enode_find(b);
        self.debug_assert_enode_root_fixed_point(r1, "incremental_merge lhs representative");
        self.debug_assert_enode_root_fixed_point(r2, "incremental_merge rhs representative");

        debug!(
            target: "ay::euf",
            lhs = a,
            rhs = b,
            reason = ?&reason,
            lhs_rep = r1,
            rhs_rep = r2,
            "EUF incremental merge request"
        );

        if r1 == r2 {
            trace!(
                target: "ay::euf",
                lhs = a,
                rhs = b,
                representative = r1,
                "EUF incremental merge skipped; terms already equivalent"
            );
            return;
        }
        // #8471: Record both old representatives as dirty so that
        // collect_disequalities_for_propagation can filter its scan
        // to only process false_eqs involving changed classes.
        self.dirty_merge_reps.insert(r1);
        self.dirty_merge_reps.insert(r2);
        // #euf-prop-gap: env-gated merge-source profiling.
        if self.gap_stats_enabled {
            match &reason {
                EqualityReason::Direct(_) => self.gap_stats.merges_direct += 1,
                EqualityReason::Congruence { .. } => self.gap_stats.merges_congruence += 1,
                EqualityReason::Shared => self.gap_stats.merges_shared += 1,
                _ => self.gap_stats.merges_other += 1,
            }
        }
        // D1 lazy-DT change feed: a real merge may commit a class to a
        // constructor; wake the datatype propagation pass (stage D1).
        self.dt_merge_dirty = true;
        let proof_reason = reason.clone();
        let edge_key = Self::edge_key(a, b);
        #[cfg(not(kani))]
        if let hashbrown::hash_map::Entry::Vacant(e) = self.equality_edges.entry(edge_key) {
            e.insert(reason);
            self.undo_trail
                .push(UndoRecord::RemoveEqualityEdge(edge_key.0, edge_key.1));
        }
        #[cfg(kani)]
        if let std::collections::btree_map::Entry::Vacant(e) = self.equality_edges.entry(edge_key) {
            e.insert(reason);
            self.undo_trail
                .push(UndoRecord::RemoveEqualityEdge(edge_key.0, edge_key.1));
        }
        self.merge_proof_forest(a, b, proof_reason);

        if self.enodes[r1 as usize].class_size > self.enodes[r2 as usize].class_size {
            std::mem::swap(&mut r1, &mut r2);
        }
        self.debug_assert_enode_root_fixed_point(r1, "incremental_merge source class");
        self.debug_assert_enode_root_fixed_point(r2, "incremental_merge destination class");

        // Incremental positive-propagation index: the absorbed class `r1`'s
        // equalities now resolve to the survivor `r2`. Move them so `class_eqs`
        // stays keyed by the current representative, and mark `r2` dirty so the
        // next incremental positive scan revisits its equalities (some of which
        // may have just become congruence-true). The index is stale after `pop`
        // and is rebuilt by the next full scan, so no undo record is needed.
        if self.inc_pos_enabled {
            if let Some(moved) = self.class_eqs.remove(&r1) {
                self.class_eqs.entry(r2).or_default().extend(moved);
            }
            self.pos_dirty_reps.insert(r2);
        }

        // Incremental disequality index (#inc-neg): rekey pair entries whose
        // endpoint representative was just absorbed. A key registered under a
        // rep that no longer resolves an index entry is stale and skipped. A
        // pair whose two sides collapse into one class is dropped from the
        // index — that is a conflict, and `check_disequality_conflicts` (which
        // scans `assigns`, not this index) remains the detection authority.
        // Stale after pop; the next full negative scan rebuilds it.
        if self.inc_neg_enabled {
            // #euf-inc-diseq-undo: whether this solve records diseq_pair_index
            // mutations for the trail-based pop-restore (constant per solve).
            let diseq_undo = self.diseq_undo_active();
            // #euf-inc-diseq-undo: an incremental pop may have left the inverse
            // index keyed by pre-pop reps; refresh it from the restored forward
            // index before rekeying reads it.
            self.ensure_diseq_keys_fresh();
            if let Some(keys) = self.diseq_keys_by_rep.remove(&r1) {
                for key in keys {
                    let Some(entry) = self.diseq_pair_index.get(&key).copied() else {
                        continue; // stale registration
                    };
                    // Only rekey entries actually keyed by the absorbed rep.
                    let other = if key.0 == r1 {
                        key.1
                    } else if key.1 == r1 {
                        key.0
                    } else {
                        continue; // stale registration
                    };
                    // #euf-inc-diseq-undo: record the mapping we are about to
                    // drop so pop() can restore this pair under its pre-merge
                    // key without a full rebuild.
                    if diseq_undo {
                        self.undo_trail.push(UndoRecord::DiseqSet { key, entry });
                    }
                    self.diseq_pair_index.remove(&key);
                    if other == r2 {
                        // Both sides now in one class: a disequality conflict.
                        // Record the candidate; check() verifies it against the
                        // live state before reporting (#inc-neg). The index
                        // entry is dropped (not re-inserted) — the `DiseqSet`
                        // above restores it when the merge is undone.
                        self.pending_diseq_conflicts.push(entry);
                        continue;
                    }
                    let new_key = (other.min(r2), other.max(r2));
                    // #euf-inc-diseq-undo: an insert into a vacant slot adds a
                    // NEW mapping; record its removal so pop() can undo it. A
                    // collision (`or_insert` keeps the existing entry) leaves the
                    // table unchanged — nothing to undo (the resident entry has
                    // its own restore record from when it was created).
                    let diseq_undo_new =
                        diseq_undo && !self.diseq_pair_index.contains_key(&new_key);
                    self.diseq_pair_index.entry(new_key).or_insert(entry);
                    if diseq_undo_new {
                        self.undo_trail
                            .push(UndoRecord::DiseqRemove { key: new_key });
                    }
                    self.diseq_keys_by_rep.entry(r2).or_default().push(new_key);
                    self.diseq_keys_by_rep
                        .entry(other)
                        .or_default()
                        .push(new_key);
                }
            }
            self.neg_dirty_reps.insert(r2);
        }

        if debug {
            safe_eprintln!(
                "[EUF] incremental_merge: {} -> {} (merging class {} into {})",
                a,
                b,
                r1,
                r2
            );
        }

        let parents_to_reinsert: Vec<u32> = self.enodes[r1 as usize].parents.clone();
        for &parent in &parents_to_reinsert {
            if let Some(sig) = self.get_func_app_sig(parent) {
                // #euf-inc-cong-undo: record the mapping we are about to drop so
                // pop() can restore it without a full rebuild. Only the first
                // removal of a shared signature records (later ones find it
                // already gone), which is exactly what the reverse replay needs.
                if self.cong_undo_active() {
                    if let Some(prev) = self.cong_table.get(&sig) {
                        self.undo_trail
                            .push(UndoRecord::CongSet { sig, term: prev });
                    }
                }
                self.cong_table.remove(&sig);
            }
        }

        let old_r1_next = self.enodes[r1 as usize].next;
        let old_r2_next = self.enodes[r2 as usize].next;
        let source_class_size = self.enodes[r1 as usize].class_size;
        let target_class_size_before = self.enodes[r2 as usize].class_size;
        #[allow(clippy::needless_collect)]
        let class_nodes: Vec<_> = self.enode_class_iter(r1).collect();
        for node in class_nodes {
            debug_assert_eq!(self.enodes[node as usize].root, r1);
            self.undo_trail.push(UndoRecord::SetRoot {
                node,
                old_root: r1,
                old_next: self.enodes[node as usize].next,
            });
            self.enodes[node as usize].root = r2;
            // Incremental UF-mirror sync: this node's representative just changed
            // from r1 to r2, so its `uf.parent` entry is now stale and must be
            // refreshed by the next `sync_egraph_to_uf`.
            if self.inc_sync_enabled {
                self.uf_dirty_nodes.insert(node);
            }
        }

        self.undo_trail.push(UndoRecord::SetRoot {
            node: r2,
            old_root: r2,
            old_next: self.enodes[r2 as usize].next,
        });
        self.enodes[r1 as usize].next = old_r2_next;
        self.enodes[r2 as usize].next = old_r1_next;
        let old_r2_size = self.enodes[r2 as usize].class_size;
        self.undo_trail.push(UndoRecord::SetClassSize {
            node: r2,
            old_size: old_r2_size,
        });
        self.enodes[r2 as usize].class_size += source_class_size;
        debug_assert_eq!(
            self.enodes[r2 as usize].class_size,
            target_class_size_before + source_class_size,
            "BUG: incremental_merge class_size update mismatch"
        );
        for &parent in &parents_to_reinsert {
            if let Some(new_sig) = self.get_func_app_sig(parent) {
                // #euf-inc-cong-undo: an insert that finds the slot empty adds a
                // NEW mapping; record its removal so pop() can undo it. A collision
                // (`insert` returns Some) leaves the table unchanged — nothing to
                // undo. Same for a same-term reinsert.
                let cong_undo_new =
                    self.cong_undo_active() && self.cong_table.get(&new_sig).is_none();
                let insert_res = self.cong_table.insert(parent, new_sig);
                if cong_undo_new {
                    self.undo_trail
                        .push(UndoRecord::CongRemove { sig: new_sig });
                }
                if let Some(congruent) = insert_res {
                    if congruent != parent {
                        if let Some((parent_fh, parent_args)) = self.get_func_app_info(parent) {
                            if let Some((cong_fh, cong_args)) = self.get_func_app_info(congruent) {
                                let is_true_congruence = parent_fh == cong_fh
                                    && parent_args.len() == cong_args.len()
                                    && parent_args.iter().zip(cong_args.iter()).all(|(&a, &b)| {
                                        self.enode_find_const(a) == self.enode_find_const(b)
                                    });
                                if is_true_congruence {
                                    let arg_pairs: Vec<(TermId, TermId)> = parent_args
                                        .iter()
                                        .zip(cong_args.iter())
                                        .map(|(&a, &b)| (TermId(a), TermId(b)))
                                        .collect();

                                    let cong_reason = EqualityReason::Congruence {
                                        _term1: TermId(parent),
                                        _term2: TermId(congruent),
                                        arg_pairs,
                                    };

                                    if debug {
                                        safe_eprintln!(
                                            "[EUF] Found congruence: {} ~ {} (adding to worklist)",
                                            parent,
                                            congruent
                                        );
                                    }
                                    debug!(
                                        target: "ay::euf",
                                        parent_term = parent,
                                        congruent_term = congruent,
                                        "EUF congruence discovered during incremental merge"
                                    );

                                    self.to_merge.push_back(MergeReason {
                                        a: parent,
                                        b: congruent,
                                        reason: cong_reason,
                                    });

                                    // Build the Nelson-Oppen propagation reason
                                    // for this congruence-derived equality. This
                                    // is the dominant cost of the per-conflict /
                                    // per-propagation soundness re-verification
                                    // (un-memoized recursive `explain`). The
                                    // verifier reads ONLY the check() verdict and
                                    // never drains `pending_propagations`, so when
                                    // `verify_only` is set we skip this block
                                    // entirely. The congruence merge itself (the
                                    // `to_merge` enqueue above) is unchanged, so
                                    // the Sat/Unsat verdict is identical. (#8529)
                                    if !self.verify_only {
                                        let lhs = TermId(parent);
                                        let rhs = TermId(congruent);
                                        let pair = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
                                        if !self.propagated_eq_pairs.contains(&pair) {
                                            self.propagated_eq_pairs.insert(pair);
                                            // Lazy N-O reason: defer the recursive
                                            // explain to drain time (empty reason =
                                            // "compute on demand"); standalone QF_UF
                                            // never drains, so it is never computed.
                                            let reasons = if self.lazy_noprop_reasons {
                                                Vec::new()
                                            } else {
                                                let mut r = Vec::new();
                                                for (&a, &b) in
                                                    parent_args.iter().zip(cong_args.iter())
                                                {
                                                    if a != b {
                                                        let sub =
                                                            self.explain(TermId(a), TermId(b));
                                                        r.extend(sub);
                                                    }
                                                }
                                                r.sort_unstable_by_key(|l| (l.term.0, l.value));
                                                r.dedup_by_key(|l| (l.term.0, l.value));
                                                r
                                            };
                                            self.queue_pending_propagation(
                                                lhs,
                                                rhs,
                                                reasons,
                                                "incremental congruence",
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            self.enodes[r2 as usize].parents.push(parent);
            self.undo_trail.push(UndoRecord::RemoveParent { node: r2 });
        }

        // #cong-neg-prop trigger: every reinserted parent's SIGNATURE just
        // changed, so equality atoms over its argument classes may have gained
        // a negative-congruence lookahead hit (merging them could now make
        // this parent congruent to a disequal application). Dirty those arg
        // classes so the incremental negative scan revisits their atoms —
        // recursing further argument levels when the cascade lookahead
        // (depth >= 2) is on, since an atom two levels below the reinserted
        // parent can gain a hit through the cascade. Missing a trigger costs
        // only search guidance, never soundness.
        if self.inc_neg_enabled && self.cong_neg_enabled {
            let levels = self.cong_neg_depth.max(1);
            let mut budget = 32u32;
            for &parent in &parents_to_reinsert {
                let Some(&idx) = self.func_app_index.get(&parent) else {
                    continue;
                };
                let n_args = self.func_apps[idx].args.len();
                for ai in 0..n_args {
                    let arg = self.func_apps[idx].args[ai];
                    let rep = self.enode_find_const(arg);
                    self.neg_dirty_reps.insert(rep);
                    if levels > 1 {
                        self.dirty_app_member_args_rec(rep, levels - 1, &mut budget);
                    }
                }
            }
        }

        trace!(
            target: "ay::euf",
            lhs = a,
            rhs = b,
            merged_into = r2,
            new_class_size = self.enodes[r2 as usize].class_size,
            reinserted_parents = parents_to_reinsert.len(),
            pending_merges = self.to_merge.len(),
            "EUF incremental merge completed"
        );

        #[cfg(debug_assertions)]
        self.debug_assert_enode_class_integrity(r2, "incremental_merge destination");
    }

    /// Rebuild the incremental merge queue from the current asserted state.
    /// Needed when queued merges were discarded on pop() before they were ever
    /// processed, but the surviving outer-scope assignments still need to be
    /// reflected in the E-graph.
    pub(crate) fn refill_incremental_merge_queue_from_state(&mut self) {
        self.scratch_equalities.clear();
        for (&lit_term, &value) in &self.assigns {
            if value {
                if let Some((lhs, rhs)) = self.decode_eq(lit_term) {
                    if lhs != rhs && self.terms.sort(lhs) == self.terms.sort(rhs) {
                        self.scratch_equalities.push((lit_term, lhs, rhs));
                    }
                }
            }
        }
        self.scratch_equalities
            .sort_by_key(|(lit_term, _, _)| *lit_term);
        for idx in 0..self.scratch_equalities.len() {
            let (lit_term, lhs, rhs) = self.scratch_equalities[idx];
            self.ensure_enodes_size(lhs.0);
            self.ensure_enodes_size(rhs.0);
            if self.enode_find_const(lhs.0) != self.enode_find_const(rhs.0) {
                self.to_merge.push_back(MergeReason {
                    a: lhs.0,
                    b: rhs.0,
                    reason: EqualityReason::Direct(lit_term),
                });
            }
        }

        self.scratch_shared_eq_keys.clear();
        self.scratch_shared_eq_keys
            .extend(self.shared_equality_reasons.keys().copied());
        self.scratch_shared_eq_keys.sort_unstable();
        for idx in 0..self.scratch_shared_eq_keys.len() {
            let (lhs, rhs) = self.scratch_shared_eq_keys[idx];
            self.ensure_enodes_size(lhs);
            self.ensure_enodes_size(rhs);
            if self.enode_find_const(lhs) != self.enode_find_const(rhs) {
                self.to_merge.push_back(MergeReason {
                    a: lhs,
                    b: rhs,
                    reason: EqualityReason::Shared,
                });
            }
        }
    }
}
