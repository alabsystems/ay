// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reset and structural snapshot lifecycle operations for LRA.

use super::*;

impl LraSolver {
    pub(crate) fn reset_inner(&mut self) {
        // All bound slots are dropped with `vars` — stale-memo hazard for LIA.
        self.bump_bound_revision();
        if self.debug_lra_reset {
            safe_eprintln!(
                "[LRA_RESET] reset() called, clearing {} vars, term_to_var has {} entries",
                self.vars.len(),
                self.term_to_var.len()
            );
            for (i, info) in self.vars.iter().enumerate() {
                safe_eprintln!(
                    "[LRA_RESET]   var {}: lb={:?}, ub={:?}",
                    i,
                    info.lower.as_ref().map(|b| &b.value),
                    info.upper.as_ref().map(|b| &b.value)
                );
            }
        }
        self.rows.clear();
        self.vars.clear();
        self.col_index.clear();
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.next_var = 0;
        self.trail.clear();
        self.scopes.clear();
        // #inc-implied-trail: lockstep with `scopes`.
        self.implied_trail.clear();
        self.implied_trail_scopes.clear();
        self.asserted.clear();
        self.asserted_trail.clear();
        self.cross_theory_asserted.clear();
        self.cross_theory_asserted_trail.clear();
        self.cross_theory_asserted_scopes.clear();
        self.atom_cache.clear();
        self.ite_link_terms.clear();
        self.ite_link_terms_seen.clear();
        self.not_inner_cache.clear();
        self.const_bool_cache.clear();
        self.refinement_eligible_cache.clear();
        self.is_integer_sort_cache.clear();
        self.bound_atoms.clear();
        self.atom_slack.clear();
        self.expr_to_slack.clear();
        self.propagated_atoms.clear();
        // #inc-prop-trail: set nuked wholesale — drop the undo trail with it.
        self.propagated_trail.clear();
        self.propagated_trail_scopes.clear();
        // #8599: Shrink propagated_atoms after full reset to release memory.
        self.propagated_atoms.shrink_to_fit();
        self.propagation_dirty_vars.clear();
        self.var_to_atoms.clear();
        self.implied_bounds.clear();
        // #inc-cib-nodelta: overlay cleared — the next full sweep must rebuild.
        self.ib_overlay_complete = false;
        // #inc-implied-trail: overlay nuked wholesale — drop the undo trail
        // with it (its entries would otherwise restore stale bounds later).
        self.implied_trail.clear();
        self.implied_trail_scopes.clear();
        self.var_bound_gen.clear();
        self.row_computed_gen.clear();
        self.implied_tighten_streak.clear();
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        self.dirty = true;
        self.last_check_trail_pos = 0;
        self.bounds_tightened_since_simplex = true;
        // #8187: reset() clears simplex state — soundness gate flag is a
        // per-invocation latch, so clear for hygiene.
        self.post_simplex_bounds_added = false;
        self.vars_tightened_since_simplex.clear();
        // #inc-guard-memo: lifecycle reset — values/bounds may be rewritten
        // below, so the guard's clean memo no longer holds. Also breaks the
        // tracked-only chain (#inc-guard-chain) until a full verification.
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.bcp_implied_dry_streak = 0;
        self.bcp_cascade_dry_streak = 0;
        self.last_simplex_feasible = false;
        self.last_simplex_feasible_scopes.clear();
        self.feasible_value_snapshot.clear();
        self.pivots_at_last_snapshot = u64::MAX;
        self.phase_hint_cache.clear();
        // Clearing the cache changes the phase suggestions; advance the epoch so
        // the SAT-side seeder does not skip the next (now-stale) re-seed.
        self.phase_hint_epoch = self.phase_hint_epoch.wrapping_add(1);
        self.rows_at_check_start = 0;
        self.pending_equalities.clear();
        self.propagated_equality_pairs.clear();
        self.propagated_disequality_pairs.clear();
        self.fixed_term_value_table.clear();
        self.fixed_term_value_members.clear();
        self.pending_fixed_term_equalities.clear();
        self.pending_offset_equalities.clear();
        self.trivial_conflict = None;
        self.to_int_terms.clear();
        self.injected_to_int_axioms.clear();
        self.basic_var_to_row.clear();
        self.touched_rows.clear();
        self.propagate_direct_touched_rows_pending = false;
        self.implied_bounds_fresh = false;
        self.unassigned_atom_count.clear();
        self.registered_atoms.clear();
        self.atom_index.clear();
        self.compound_use_index.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.last_compound_propagations_queued = 0;
        self.last_compound_wake_dirty_hits = 0;
        self.last_compound_wake_candidates = 0;
        self.infeasible_heap.clear();
        self.in_infeasible_heap.clear();
        self.heap_epoch = 1;
        self.heap_stale = true;
        // #warm-simplex: vars are dropped wholesale — reset the warm
        // structures alongside the heap membership vec.
        self.warm_invalidate();
        self.warm.nonbasic_stamp.clear();
        self.warm.delta_stamp.clear();
        self.disequality_trail.clear();
        self.disequality_trail_scopes.clear();
        self.shared_disequality_trail.clear();
        self.shared_disequality_trail_scopes.clear();
        self.pending_diseq_splits.clear();
        self.pending_expr_splits.clear();
        self.pivot_row_cache.clear();
        self.lra_basis_region_basis_epoch = 0;
        self.lra_basis_region_requests.clear();
        self.lra_basis_region_candidate = None;
        self.negation_partners.clear();
        // #8620: Clear slack_var_set that was previously missed, causing
        // stale slack variable identifiers to persist across resets.
        self.slack_var_set.clear();
        // Fix A1: drop the theory-prop JIT — reset() clears atom_index and
        // restarts var numbering, so the compiled tables (and their
        // fingerprint) are stale for whatever is registered next.
        self.theory_prop_jit = ay_jit::TheoryPropJit::new();
        self.theory_prop_jit_compiled = false;
        // STAGE B: registered_atoms + asserted were both cleared above, so the
        // decision-candidate index is empty.
        self.decision_index.eq.clear();
        self.decision_index.ineq.clear();
    }

    pub(crate) fn soft_reset_inner(&mut self) {
        // Bound slots are cleared wholesale below — stale-memo hazard for LIA.
        self.bump_bound_revision();
        // Restart boundary: install any compiled artifacts that became ready
        // since the previous solve iteration. Today this is a backend-neutral
        // seam shared by the compiled-substitute backends, including EXTERNAL_CODEGEN.
        self.drain_lra_basis_region_requests_at_safe_boundary();
        let _installed = self.pivot_row_cache.install_ready_results();

        self.asserted.clear();
        self.asserted_trail.clear();
        self.cross_theory_asserted.clear();
        self.cross_theory_asserted_trail.clear();
        self.trail.clear();
        self.scopes.clear();
        // #inc-implied-trail: lockstep with `scopes`.
        self.implied_trail.clear();
        self.implied_trail_scopes.clear();
        self.cross_theory_asserted_scopes.clear();
        self.propagated_equality_pairs.clear();
        self.propagated_disequality_pairs.clear();
        self.pending_equalities.clear();
        self.fixed_term_value_table.clear();
        self.fixed_term_value_members.clear();
        self.pending_fixed_term_equalities.clear();
        self.pending_offset_equalities.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.propagated_atoms.clear();
        // #inc-prop-trail: set nuked wholesale — drop the undo trail with it.
        self.propagated_trail.clear();
        self.propagated_trail_scopes.clear();
        // #8599: Shrink propagated_atoms after soft_reset to release memory.
        self.propagated_atoms.shrink_to_fit();
        self.propagation_dirty_vars.clear();
        self.propagation_dirty_vars
            .extend(self.atom_index.keys().copied());
        self.propagation_dirty_vars
            .extend(self.compound_use_index.keys().copied());
        self.last_compound_propagations_queued = 0;
        self.last_compound_wake_dirty_hits = 0;
        self.last_compound_wake_candidates = 0;
        self.implied_bounds.clear();
        // #inc-cib-nodelta: overlay cleared — the next full sweep must rebuild.
        self.ib_overlay_complete = false;
        // #inc-implied-trail: overlay nuked wholesale — drop the undo trail
        // with it (its entries would otherwise restore stale bounds later).
        self.implied_trail.clear();
        self.implied_trail_scopes.clear();
        self.var_bound_gen.clear();
        self.row_computed_gen.clear();
        self.implied_tighten_streak.clear();
        self.trivial_conflict = None;
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        self.dirty = true;
        self.last_check_trail_pos = 0;
        self.bounds_tightened_since_simplex = true;
        // #8187: hard reset — soundness gate flag is per-invocation, clear
        // for hygiene.
        self.post_simplex_bounds_added = false;
        self.vars_tightened_since_simplex.clear();
        // #inc-guard-memo: lifecycle reset — values/bounds may be rewritten
        // below, so the guard's clean memo no longer holds. Also breaks the
        // tracked-only chain (#inc-guard-chain) until a full verification.
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.bcp_implied_dry_streak = 0;
        self.bcp_cascade_dry_streak = 0;
        self.last_simplex_feasible = false;
        self.last_simplex_feasible_scopes.clear();
        self.feasible_value_snapshot.clear();
        self.pivots_at_last_snapshot = u64::MAX;
        self.phase_hint_cache.clear();
        // Clearing the cache changes the phase suggestions; advance the epoch so
        // the SAT-side seeder does not skip the next (now-stale) re-seed.
        self.phase_hint_epoch = self.phase_hint_epoch.wrapping_add(1);
        self.rows_at_check_start = 0;
        for var_info in &mut self.vars {
            var_info.lower = None;
            var_info.upper = None;
            var_info.value = InfRational::default();
        }
        for row in &self.rows {
            let basic = row.basic_var as usize;
            if basic < self.vars.len() {
                self.vars[basic].value = InfRational::from_rat(row.constant.clone());
            }
        }
        self.bound_atoms.clear();
        self.injected_to_int_axioms.clear();
        self.touched_rows.clear();
        for i in 0..self.rows.len() {
            self.touched_rows.insert(i);
        }
        self.propagate_direct_touched_rows_pending = false;
        self.implied_bounds_fresh = false;
        self.recount_unassigned_atoms();
        self.infeasible_heap.clear();
        // #inc-heap-epoch: O(1) logical clear of heap membership.
        self.bump_heap_epoch();
        self.heap_stale = true;
        // #warm-simplex: values/bounds rewritten wholesale above — all warm
        // tracking is stale.
        self.warm_invalidate();
        self.disequality_trail.clear();
        self.disequality_trail_scopes.clear();
        self.shared_disequality_trail.clear();
        self.shared_disequality_trail_scopes.clear();
        self.pending_diseq_splits.clear();
        self.pending_expr_splits.clear();
        self.pivot_row_cache.clear_lra_basis_region_artifacts();
        self.lra_basis_region_requests.clear();
        self.lra_basis_region_candidate = None;
        // STAGE B: asserted was cleared but registered_atoms preserved — every
        // registered non-distinct atom is now an unasserted decision candidate.
        self.rebuild_decision_index();
    }

    pub(crate) fn restore_from_structural_snapshot_inner(
        terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>> {
        Self::try_from_snapshot(terms, snapshot)
    }

    pub(crate) fn export_structural_snapshot_inner(&self) -> Option<Box<dyn std::any::Any>> {
        if self.registered_atoms.is_empty() {
            return None;
        }
        Some(Box::new(LraStructuralSnapshot {
            rows: self.rows.clone(),
            vars: self.vars.clone(),
            term_to_var: self.term_to_var.clone(),
            var_to_term: self.var_to_term.clone(),
            next_var: self.next_var,
            atom_cache: self.atom_cache.clone(),
            ite_link_terms: self.ite_link_terms.clone(),
            ite_link_terms_seen: self.ite_link_terms_seen.clone(),
            registered_atoms: self.registered_atoms.clone(),
            atom_index: self.atom_index.clone(),
            compound_use_index: self.compound_use_index.clone(),
            var_to_atoms: self.var_to_atoms.clone(),
            atom_slack: self.atom_slack.clone(),
            expr_to_slack: self.expr_to_slack.clone(),
            slack_var_set: self.slack_var_set.clone(),
            propagated_equality_pairs: self.propagated_equality_pairs.clone(),
            propagated_disequality_pairs: self.propagated_disequality_pairs.clone(),
            basic_var_to_row: self.basic_var_to_row.clone(),
            col_index: self.col_index.clone(),
            to_int_terms: self.to_int_terms.clone(),
            unassigned_atom_count: self.unassigned_atom_count.clone(),
            not_inner_cache: self.not_inner_cache.clone(),
            const_bool_cache: self.const_bool_cache.clone(),
            refinement_eligible_cache: self.refinement_eligible_cache.clone(),
            is_integer_sort_cache: self.is_integer_sort_cache.clone(),
            bcp_implied_dry_streak: 0,
            bcp_cascade_dry_streak: 0,
            max_row_width: self.max_row_width,
            negation_partners: self.negation_partners.clone(),
            // Fix A1: persist the compiled theory-prop JIT alongside the
            // atom_index it was compiled from. Interpreted tables are
            // deep-copied; the native code region is shared via Arc.
            // (Former `AY_LRA_JIT_PERSIST` kill-switch removed; persistence
            // is the default and now permanent.)
            theory_prop_jit: if self.theory_prop_jit_compiled {
                Some(self.theory_prop_jit.clone())
            } else {
                None
            },
        }))
    }

    pub(crate) fn import_structural_snapshot_inner(&mut self, snapshot: Box<dyn std::any::Any>) {
        let Ok(snap) = snapshot.downcast::<LraStructuralSnapshot>() else {
            return;
        };
        // Imported vars replace every bound slot — stale-memo hazard for LIA.
        self.bump_bound_revision();
        self.rows = snap.rows;
        self.vars = snap.vars;
        self.term_to_var = snap.term_to_var;
        self.var_to_term = snap.var_to_term;
        self.next_var = snap.next_var;
        self.atom_cache = snap.atom_cache;
        self.ite_link_terms = snap.ite_link_terms;
        self.ite_link_terms_seen = snap.ite_link_terms_seen;
        self.registered_atoms = snap.registered_atoms;
        self.atom_index = snap.atom_index;
        self.compound_use_index = snap.compound_use_index;
        self.var_to_atoms = snap.var_to_atoms;
        self.atom_slack = snap.atom_slack;
        self.expr_to_slack = snap.expr_to_slack;
        self.slack_var_set = snap.slack_var_set;
        self.propagated_equality_pairs = snap.propagated_equality_pairs;
        self.propagated_disequality_pairs = snap.propagated_disequality_pairs;
        self.basic_var_to_row = snap.basic_var_to_row;
        self.col_index = snap.col_index;
        self.to_int_terms = snap.to_int_terms;
        self.unassigned_atom_count = snap.unassigned_atom_count;
        self.not_inner_cache = snap.not_inner_cache;
        self.const_bool_cache = snap.const_bool_cache;
        self.refinement_eligible_cache = snap.refinement_eligible_cache;
        self.is_integer_sort_cache = snap.is_integer_sort_cache;
        self.persistent_unsupported_atoms.clear();
        self.persistent_unsupported_trail.clear();
        self.persistent_unsupported_scope_marks.clear();
        for var_info in &mut self.vars {
            var_info.lower = None;
            var_info.upper = None;
            var_info.value = InfRational::default();
        }
        for row in &self.rows {
            let basic = row.basic_var as usize;
            if basic < self.vars.len() {
                self.vars[basic].value = InfRational::from_rat(row.constant.clone());
            }
        }
        self.touched_rows.clear();
        for i in 0..self.rows.len() {
            self.touched_rows.insert(i);
        }
        self.propagate_direct_touched_rows_pending = false;
        self.implied_bounds_fresh = false;
        self.in_infeasible_heap.resize(self.vars.len(), 0);
        self.heap_stale = true;
        // #warm-simplex: imported snapshot replaced vars/values — all warm
        // tracking is stale.
        self.warm_invalidate();
        self.propagation_dirty_vars
            .extend(self.atom_index.keys().copied());
        self.propagation_dirty_vars
            .extend(self.compound_use_index.keys().copied());
        self.recount_unassigned_atoms();
        self.dirty = true;
        self.bounds_tightened_since_simplex = true;
        // #8187: restore_from_snapshot — soundness gate flag is per-invocation.
        self.post_simplex_bounds_added = false;
        self.vars_tightened_since_simplex.clear();
        // #inc-guard-memo: lifecycle reset — values/bounds may be rewritten
        // below, so the guard's clean memo no longer holds. Also breaks the
        // tracked-only chain (#inc-guard-chain) until a full verification.
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.bcp_implied_dry_streak = 0;
        self.bcp_cascade_dry_streak = 0;
        self.max_row_width = snap.max_row_width;
        self.negation_partners = snap.negation_partners;
        // Fix A1: restore the persisted theory-prop JIT. The snapshot's JIT
        // was compiled for the snapshot's atom_index, which this import just
        // restored — so the compiled tables are valid as-is. Any later atom
        // registration flips `theory_prop_jit_compiled` to false and the
        // fingerprint check in compile_theory_propagation_jit() decides
        // whether a rebuild is actually needed.
        match snap.theory_prop_jit {
            Some(jit) => {
                self.theory_prop_jit = jit;
                self.theory_prop_jit_compiled = true;
            }
            None => {
                self.theory_prop_jit = ay_jit::TheoryPropJit::new();
                self.theory_prop_jit_compiled = false;
            }
        }
        // Policy decision (Fix A1): pivot_row_cache is NOT persisted across
        // snapshot transfer. Unlike the theory-prop JIT (which was eagerly
        // recompiled per instance — the measured 59%), the pivot-row cache is
        // populated lazily behind COMPILE_THRESHOLD use counts, so a fresh
        // instance pays no eager compile cost; its entries self-validate via
        // CompiledPivotRow::matches() but its use-count/backoff budgets and
        // background-compiler queues are per-instance policy state that is
        // not Clone. Clearing remains the sound, cheap choice.
        self.pivot_row_cache.clear();
        self.lra_basis_region_basis_epoch = 0;
        self.lra_basis_region_requests.clear();
        self.lra_basis_region_candidate = None;
        // STAGE B: registered_atoms was replaced from the snapshot — rebuild the
        // decision-candidate index against the imported atoms and current
        // (possibly non-empty) assertion state.
        self.rebuild_decision_index();
    }
}
