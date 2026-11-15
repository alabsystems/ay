// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The worklist half of the incremental E-graph: processing pending merges
//! and rebuilding congruence closure.

use ay_core::term::{TermData, TermId};
use ay_core::TheoryLit;
use tracing::info;

use crate::solver::EufSolver;
use crate::types::{EqualityReason, MergeReason};

impl EufSolver<'_> {
    /// Process the merge worklist until fixed point.
    ///
    /// Each merge can discover new congruences, which are added to the worklist.
    /// We process until no more merges are pending.
    pub(crate) fn incremental_propagate(&mut self) -> usize {
        let debug = self.debug_euf;
        let mut iterations: usize = 0;
        let initial_pending = self.to_merge.len();
        #[cfg(debug_assertions)]
        let mut changed_nodes = Vec::new();
        // Capacity hint only (debug builds): `extend` still grows on failure.
        #[cfg(debug_assertions)]
        let _ = changed_nodes.try_reserve(initial_pending.saturating_mul(2));

        while let Some(merge) = self.to_merge.pop_front() {
            iterations = iterations.saturating_add(1);
            #[cfg(debug_assertions)]
            changed_nodes.extend([merge.a, merge.b]);
            self.incremental_merge(merge.a, merge.b, merge.reason);
            // #8469: Track merge epoch for disequality dirty tracking.
            self.merge_epoch = self.merge_epoch.wrapping_add(1);
        }
        #[cfg(debug_assertions)]
        self.debug_assert_changed_enode_classes(changed_nodes);

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
            merge_steps = merge_steps.saturating_add(self.incremental_propagate());
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
            merge_steps = merge_steps.saturating_add(self.incremental_propagate());
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
                        // The sweep reads `not p` through p's SAT assignment.
                        // Record that same owned atom and polarity in every
                        // explanation and Nelson-Oppen propagation, rather than
                        // naming an unassigned `not` node as a premise.
                        let (reason_condition, reason_value) = match self.terms.get(cond) {
                            TermData::Not(inner) => (*inner, !val),
                            _ => (cond, val),
                        };
                        self.to_merge.push_back(MergeReason {
                            a: term_id.0,
                            b: branch.0,
                            reason: EqualityReason::Ite {
                                condition: reason_condition,
                                value: reason_value,
                            },
                        });
                        // Propagate ITE-derived equality to other theories via
                        // Nelson-Oppen (incremental path). (#5081)
                        let reason = vec![TheoryLit::new(reason_condition, reason_value)];
                        self.queue_pending_propagation(
                            term_id,
                            branch,
                            reason,
                            "incremental ITE branch equality",
                        );
                        ite_merge_count = ite_merge_count.saturating_add(1);
                    }
                }
            }
        }
        if !self.to_merge.is_empty() {
            merge_steps = merge_steps.saturating_add(self.incremental_propagate());
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
