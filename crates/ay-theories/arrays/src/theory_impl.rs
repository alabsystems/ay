// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `ArraySolver`.
//!
//! Implements the DPLL(T) theory interface for the array theory.
//! Check logic is in `theory_check.rs`, propagation in `theory_propagate.rs`.

use super::*;
const APPLIED_LEMMAS_SOFT_CAP: usize = 8_192;

impl TheorySolver for ArraySolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.register_scope_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        let (term, val) = ay_core::unwrap_not(self.terms, literal, value);
        let previous = self.assigns.get(&term).copied();
        self.record_assignment(term, val);

        // #6546 Packet 4: direct asserted array equalities must drive the same
        // incremental ROW2 queueing path as shared equalities. Without this,
        // `a = b` learned/assumed at the SAT layer leaves `array_vars`
        // unmerged and misses the eager `(store(b, i, v), select(a, j))`
        // registrations that `notify_equality()` performs.
        if !val || previous == Some(true) {
            return;
        }

        let TermData::App(sym, args) = self.terms.get(term) else {
            return;
        };
        if sym.name() != "=" || args.len() != 2 {
            return;
        }
        let sort0 = self.terms.sort(args[0]);
        let sort1 = self.terms.sort(args[1]);
        if !matches!(sort0, Sort::Array(_)) || !matches!(sort1, Sort::Array(_)) {
            return;
        }

        self.notify_equality(args[0], args[1]);
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Forward to assert_external_equality for the eq-graph and also
        // trigger notify_equality for eager ROW2 axiom queuing (#6546).
        self.assert_external_equality_with_reasons(lhs, rhs, reason);
        self.notify_equality(lhs, rhs);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_impl()
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        // M5 shadow: env-gated (`AY_WEQ5_SHADOW_DUMP`) one-line dump of the
        // verdict-only-flip differential totals at solve/stat-collection time.
        // Debug-only; release compiles it out with the rest of `weq5_shadow`.
        #[cfg(debug_assertions)]
        weak_equiv::weq5_shadow::maybe_dump();
        vec![
            ("arrays_checks", self.check_count),
            ("arrays_conflicts", self.conflict_count),
            ("arrays_propagations", self.propagation_count),
            ("arrays_scan_count", self.scan_count),
            ("arrays_scan_entry_visits", self.scan_entry_visits),
            ("arrays_scan_view_iters", self.scan_view_iters),
            ("arrays_fingerprint_gc", self.fingerprint_gc_removed),
            (
                "arrays_candidate_pairs_calls",
                self.candidate_pairs_calls.get(),
            ),
            (
                "arrays_candidate_pairs_generated",
                self.candidate_pairs_generated.get(),
            ),
            (
                "arrays_candidate_pairs_memo_hits",
                self.candidate_pairs_memo_hits.get(),
            ),
            (
                "arrays_fingerprint_live",
                self.axiom_fingerprints.len() as u64,
            ),
            (
                "arrays_applied_lemmas_live",
                self.applied_theory_lemmas.len() as u64,
            ),
            (
                "arrays_requested_model_eqs",
                self.requested_model_eqs.len() as u64,
            ),
            (
                "arrays_requested_interface_eqs",
                self.requested_interface_eqs.len() as u64,
            ),
            (
                "arrays_sent_propagations",
                self.sent_propagations.len() as u64,
            ),
        ]
    }

    fn note_applied_theory_lemma(&mut self, clause: &[TheoryLit]) {
        // #8605: Cap applied_theory_lemmas to prevent unbounded heap growth.
        // Each entry is a heap-allocated Vec<TheoryLit>. When the set exceeds
        // the soft cap, clear it. Re-emitting already-applied lemmas is safe:
        // the SAT solver deduplicates clauses, so the only cost is redundant
        // NeedLemmas results that the DPLL(T) loop will recognize as already
        // present.
        if self.applied_theory_lemmas.len() >= APPLIED_LEMMAS_SOFT_CAP {
            self.applied_theory_lemmas.clear();
            self.applied_theory_lemmas.shrink_to_fit();
        }
        self.applied_theory_lemmas.insert(clause.to_vec());
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.propagate_impl()
    }

    /// Discover equalities implied by array axioms for Nelson-Oppen propagation (#4665).
    ///
    /// Delegates to `propagation.rs`. See `Self::propagate_equalities_impl`.
    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        self.propagate_equalities_impl()
    }

    fn push(&mut self) {
        self.scopes.push(self.trail.len());
        // Mark the array-var merge trail so pop() undoes exactly this scope's
        // merges (M1 persistent-structural-registration).
        self.array_var_merge_scopes
            .push(self.array_var_merge_log.len());
    }

    fn pop(&mut self) {
        let Some(mark) = self.scopes.pop() else {
            return;
        };
        let mut eq_graph_changed = !self.external_eqs.is_empty();
        while self.trail.len() > mark {
            let (term, prev) = self.trail.pop().expect("trail length checked above");
            let current = self.assigns.get(&term).copied();
            if self.is_equality_term(term)
                && Self::equality_assignment_affects_eq_graph(prev, current)
            {
                eq_graph_changed = true;
            }
            match prev {
                Some(v) => {
                    self.assigns.insert(term, v);
                }
                None => {
                    self.assigns.remove(&term);
                }
            }
        }
        // Clear external facts — they're re-derived each check cycle (#4665)
        self.external_diseqs.clear();
        self.external_diseq_reasons.clear();
        self.external_eqs.clear();
        self.external_eq_reasons.clear();
        self.sent_equalities.clear();
        self.sent_equality_replays.clear();
        self.sent_equality_replay_log.clear();
        self.sent_propagations.clear();
        // #8605: Shrink sent_propagations — each entry is (TheoryLit, Vec<TheoryLit>)
        // with heap-allocated reason vectors. Release bucket memory after clearing.
        self.sent_propagations.shrink_to_fit();
        // ROW2 dirty-entry scan: assignments were bulk-rewound and the sent-
        // propagation dedup memory dropped — every entry must re-derive.
        // (rebuild_assign_indices() would also mark this via assign_dirty;
        // explicit for safety.)
        self.row2_mark_all_dirty();
        // #6694: Clear applied-lemma dedup on pop so backtracking doesn't
        // suppress re-requesting ROW2 axioms in subsequent branches.
        self.applied_theory_lemmas.clear();
        // #8605: Shrink heap-allocated lemma dedup set after clearing. Each
        // entry is a Vec<TheoryLit> on the heap; clearing drops the Vecs but
        // the HashSet retains its bucket array. shrink_to_fit() releases the
        // bucket memory when the set was large before pop.
        self.applied_theory_lemmas.shrink_to_fit();
        // #6546: Clear event-driven ROW1 queue on backtrack since equalities
        // may no longer hold.
        self.pending_row1.clear();
        self.pending_row2_upward.clear();
        self.pending_self_store.clear();
        self.pending_store_chain.clear();
        self.pending_conflicting_stores.clear();
        self.pending_array_eqs.clear();
        self.pending_select_map.clear();
        self.pending_select_as_array.clear();
        self.pending_default_const.clear();
        self.pending_registered_equalities.clear();
        // NOTE: Do NOT clear requested_model_eqs here. The dedup set persists
        // across pop/push cycles within the same problem to prevent infinite
        // NeedModelEquality loops in the N-O fixpoint. Cleared only in reset().
        // M1: undo this scope's `array_vars` merges by truncation (O(1) per
        // merge), keeping the pop-invariant structural base intact. This is the
        // inverse of the append-only `merge_array_var_data`; `array_vars` is
        // therefore NOT rebuilt from scratch on pop. If the scope stack is
        // empty (defensive), fall back to undoing every recorded merge.
        let merge_mark = self.array_var_merge_scopes.pop().unwrap_or(0);
        while self.array_var_merge_log.len() > merge_mark {
            self.array_var_merge_log.pop();
            if let Some(undo) = self.array_var_merge_undo.pop() {
                if let Some(data) = self.array_vars.get_mut(&undo.target) {
                    data.stores_as_result.truncate(undo.stores_len as usize);
                    data.parent_selects.truncate(undo.selects_len as usize);
                    data.parent_stores.truncate(undo.parent_stores_len as usize);
                    data.prop_upward = undo.prev_prop_upward;
                }
            }
        }

        // M1 (persistent structural registration): a `pop()` never deletes a
        // term, so the STRUCTURAL caches (`select_cache`, `store_cache`,
        // `equality_cache`, `term_to_equalities`, `eq_pair_index`, and the
        // const/map/as-array/default caches) are pop-invariant and are kept.
        // Only the assignment/merge-derived array-var layer and the event
        // queues need rebuilding — signalled by `var_layer_dirty`, replayed
        // from the persisted structural caches by `replay_var_layer()` on the
        // next `populate_caches()`. `dirty` (full structural wipe) is left
        // untouched. The equality graph is rebuilt independently via
        // `assign_dirty` in `rebuild_assign_indices()`.
        self.var_layer_dirty = true;
        self.assign_dirty = true;
        // #6546: Invalidate prop_eq and upward snapshots so propagate_equalities()
        // and check_row2_upward_with_guidance() re-scan after backtracking.
        self.prop_eq_snapshot = None;
        self.final_check_snapshot = None;
        if eq_graph_changed {
            self.note_eq_graph_changed();
        }
    }

    fn reset(&mut self) {
        let eq_graph_changed = !self.eq_adj.is_empty()
            || self.equiv_class_cache_version.is_some()
            || !self.external_eqs.is_empty();
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        self.clear_term_caches();
        self.axiom_fingerprints.clear();
        self.row2_fingerprint_indices.clear();
        self.external_diseqs.clear();
        self.external_diseq_reasons.clear();
        self.external_eqs.clear();
        self.external_eq_reasons.clear();
        self.sent_equalities.clear();
        self.sent_equality_replays.clear();
        self.sent_equality_replay_log.clear();
        self.sent_propagations.clear();
        // #8594: Do NOT clear requested_model_eqs and requested_interface_eqs
        // in reset(). These are convergence dedup sets that must survive across
        // reset() calls in the non-persistent eager arm. In that arm, each
        // iteration creates a fresh theory (starting with empty sets), imports
        // persisted sets, but then DPLL's solve_impl() calls theory.reset()
        // before the theory runs -- wiping the imported data. By not clearing
        // these sets in reset(), the import/export persistence works correctly.
        //
        // For fresh theories (the non-persistent case), these fields are already
        // empty from construction, so skipping the clear is harmless.
        // For persistent theories (incremental push/pop), the sets should also
        // persist -- re-requesting the same model equality is wasteful.
        self.applied_theory_lemmas.clear();
        // ROW2 dirty-entry scan: full teardown.
        self.row2_invalidate_entries();
        self.dirty = true;
        self.assign_dirty = true;
        // M1 shadow union-find: dropped with the rest of the equality
        // indices; rebuilt by the next rebuild_assign_indices().
        self.shadow_uf.clear();
        self.shadow_uf_stale = true;
        self.prop_eq_snapshot = None;
        self.final_check_snapshot = None;
        if eq_graph_changed {
            self.note_eq_graph_changed();
        }
    }
}

impl ArraySolver<'_> {
    /// Validate that a conflict explanation is sound: every literal in the
    /// explanation must be true in the current assignment. If any literal
    /// is false or unassigned, the conflict is spurious (#6741).
    #[cfg(debug_assertions)]
    pub(crate) fn validate_conflict_explanation(&self, reasons: &[TheoryLit]) {
        for (i, lit) in reasons.iter().enumerate() {
            let actual_value = self.assigns.get(&lit.term).copied();
            debug_assert!(
                actual_value == Some(lit.value),
                "Array conflict explanation lit[{i}] unsound: \
                 term={:?} expected={} actual={actual_value:?} \
                 term_data={:?}",
                lit.term,
                lit.value,
                self.terms.get(lit.term)
            );
        }
    }
}
