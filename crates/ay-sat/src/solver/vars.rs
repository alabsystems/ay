// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable allocation, freeze/melt protection, and dynamic resizing.

use super::*;

impl Solver {
    /// Allocate a new variable in the solver
    ///
    /// Returns the newly allocated variable. This is useful for incremental
    /// solving where new variables need to be added dynamically.
    pub fn new_var(&mut self) -> Variable {
        let var = self.new_var_internal();
        // New variables allocated via the public API are user-visible and should be
        // included in returned models.
        self.user_num_vars = self.user_num_vars.max(self.num_vars);
        var
    }

    /// Ensure the solver has at least `num_vars` variables
    ///
    /// If the solver already has enough variables, this is a no-op.
    /// Otherwise, new variables are allocated to reach the requested count.
    /// This is useful for incremental solving where the total number of
    /// variables may not be known upfront.
    pub fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        // Invalidate IC3 assumption cache (#8443): new variables change
        // the solver's variable space.
        self.cold.assumption_cache_valid = false;

        // Batch-resize all solver-level Vecs to the target size in one pass,
        // avoiding N individual push() calls and N redundant subsystem
        // ensure_num_vars() invocations (Phase 3 of #5089).
        // #nia-oom: literal indexing needs 2 slots per variable. Use checked
        // arithmetic so an absurd/untrusted `num_vars` can never silently wrap
        // to a too-small capacity (→ later out-of-bounds), turning a corrupt
        // count into a clear failure rather than memory unsafety. (This is the
        // unguarded primitive Trust's UnboundedAllocation obligation targets;
        // callers already pass content-derived, bounded sizes.)
        let lit_capacity = num_vars
            .checked_mul(2)
            .expect("ensure_num_vars: literal capacity (num_vars * 2) overflows usize");
        self.vals.resize(lit_capacity, 0); // literal-indexed: 2 per variable
        self.var_data.resize(num_vars, VarData::UNASSIGNED);
        // Always resize proof ID arrays unconditionally (#8069: Phase 2a).
        self.unit_proof_id.resize(num_vars, 0);
        self.unit_proof_sign.resize(num_vars, 0);
        self.phase.resize(num_vars, 0);
        self.target_phase.resize(num_vars, 0);
        self.best_phase.resize(num_vars, 0);
        self.min.minimize_flags.resize(num_vars, 0);
        self.cold.level0_proof_id.resize(num_vars, 0);
        self.cold.level0_proof_sign.resize(num_vars, 0);
        self.cold.freeze_counts.resize(num_vars, 0);
        self.cold.forced_phase.resize(num_vars, 0);
        // Grow external↔internal variable index mappings (identity mapping
        // for newly added variables). Without this, inprocessing passes
        // (decompose, sweep, congruence) panic on externalize() because i2e
        // is shorter than num_vars. Bug: ensure_num_vars skipped e2i/i2e,
        // so Solver::new(0) followed by ensure_num_vars(N) left i2e empty.
        let old_len = self.cold.e2i.len();
        for idx in old_len..num_vars {
            let v = idx as u32;
            self.cold.e2i.push(v);
            self.cold.i2e.push(v);
        }
        self.subsume_dirty.resize(num_vars, true);
        self.l0_gc_dirty.resize(num_vars, false); // #7981: must track all variables including scope selectors
        self.dirty_watches.resize(num_vars * 2, false);
        if let Some(ref mut gc_occ) = self.gc_occ {
            gc_occ.ensure_num_vars(num_vars);
        }
        self.cold.factor_candidate_marks.resize(num_vars, 0);
        self.var_lifecycle.ensure_num_vars(num_vars);
        self.probe_parent.resize(num_vars, None);
        self.lambda.resize(num_vars, None);
        self.cold.scope_selector_set.resize(num_vars, false);
        self.cold.was_scope_selector.resize(num_vars, false);
        // These three arrays are indexed by decision level (0..=num_vars),
        // matching the constructor's num_vars + 1 allocation (#5513).
        self.glue_stamp.resize(num_vars + 1, 0);
        self.shrink_stamp.resize(num_vars, 0);
        self.vivify_analyzed.resize(num_vars, false);
        self.min
            .minimize_level_seen
            .resize(num_vars + 1, minimization_state::LevelSeen::EMPTY);
        if let Some(ref mut witness) = self.cold.solution_witness {
            witness.resize(num_vars, None);
        }
        self.num_vars = num_vars;
        // Recompute ghost guard: chrono-BT requires num_vars > CHRONO_LEVEL_LIMIT (#8466).
        // Incremental mode (push/pop) also creates ghost literals (#8489).
        self.ghost_guard_needed =
            num_vars > CHRONO_LEVEL_LIMIT as usize || self.cold.has_ever_scoped;

        debug_assert!(
            self.unit_proof_id.len() == self.num_vars,
            "BUG: unit_proof_id length must track num_vars"
        );
        debug_assert_eq!(
            self.cold.e2i.len(),
            self.num_vars,
            "BUG: e2i length must track num_vars"
        );
        debug_assert_eq!(
            self.cold.i2e.len(),
            self.num_vars,
            "BUG: i2e length must track num_vars"
        );

        // Subsystem batch resize — each called once with the final target.
        self.watches.ensure_num_vars(num_vars);
        self.vsids.ensure_num_vars(num_vars);
        self.conflict.ensure_num_vars(num_vars);
        self.lit_marks.ensure_num_vars(num_vars);
        self.inproc.ensure_num_vars(num_vars);

        // `ensure_num_vars` is an incremental-solving API, so include any newly
        // allocated variables in returned models.
        self.user_num_vars = self.user_num_vars.max(self.num_vars);
    }

    /// Freeze a variable, protecting it from elimination by BVE and other
    /// preprocessing techniques.
    ///
    /// Use freeze/melt for:
    /// - Assumption literals that must not be eliminated
    /// - Theory-critical variables from theory solvers
    /// - User-tracked variables for model extraction
    ///
    /// This uses reference counting: multiple freeze() calls require the same
    /// number of melt() calls to unfreeze. Uses saturating arithmetic.
    ///
    /// # Panics
    /// Panics if the variable index is out of bounds.
    pub fn freeze(&mut self, var: Variable) {
        let idx = var.index();
        assert!(idx < self.num_vars, "freeze: variable out of bounds");
        self.cold.freeze_counts[idx] = self.cold.freeze_counts[idx].saturating_add(1);
    }

    /// Unfreeze a variable, allowing elimination when freeze count reaches 0.
    ///
    /// Each melt() decrements the freeze count. The variable becomes eligible
    /// for elimination only when the count reaches 0. Uses saturating arithmetic
    /// so extra melt() calls on an unfrozen variable are safe (no underflow).
    ///
    /// # Panics
    /// Panics if the variable index is out of bounds.
    pub fn melt(&mut self, var: Variable) {
        let idx = var.index();
        assert!(idx < self.num_vars, "melt: variable out of bounds");
        self.cold.freeze_counts[idx] = self.cold.freeze_counts[idx].saturating_sub(1);
    }

    /// Check if a variable is frozen (protected from elimination).
    ///
    /// Returns true if the freeze count is greater than 0.
    ///
    /// # Panics
    /// Panics if the variable index is out of bounds.
    pub fn is_frozen(&self, var: Variable) -> bool {
        let idx = var.index();
        assert!(idx < self.num_vars, "is_frozen: variable out of bounds");
        self.cold.freeze_counts[idx] > 0
    }

    /// Set the initial decision polarity for a variable.
    ///
    /// The solver will try this polarity first when branching on this variable,
    /// overriding target phases and saved phases. The hint persists across
    /// `solve_with_assumptions()` calls until cleared.
    ///
    /// IC3 uses this to bias cube polarity: when checking if a cube
    /// `{a, !b, c}` is reachable, setting phases for cube variables
    /// reduces the average number of decisions per SAT call by 2-5x.
    ///
    /// CaDiCaL: `phase(int lit)` / `phases.forced` (phases.cpp:31-43).
    ///
    /// # Panics
    /// Panics if the variable index is out of bounds.
    pub fn set_phase(&mut self, var: Variable, positive: bool) {
        let idx = var.index();
        assert!(idx < self.num_vars, "set_phase: variable out of bounds");
        self.cold.forced_phase[idx] = if positive { 1 } else { -1 };
    }

    /// Clear the externally-set phase hint for a specific variable.
    ///
    /// After clearing, the solver reverts to internal phase saving
    /// (target phase, saved phase, or default) for this variable.
    ///
    /// CaDiCaL: `unphase(int lit)` (phases.cpp:45-54).
    ///
    /// # Panics
    /// Panics if the variable index is out of bounds.
    pub fn clear_phase(&mut self, var: Variable) {
        let idx = var.index();
        assert!(idx < self.num_vars, "clear_phase: variable out of bounds");
        self.cold.forced_phase[idx] = 0;
    }

    /// Clear all externally-set phase hints.
    ///
    /// Resets all variables to solver-internal phase saving.
    pub fn clear_phases(&mut self) {
        self.cold.forced_phase.fill(0);
    }

    /// Internal variable allocation — allocates a new variable and resizes all
    /// solver-level data structures.
    ///
    /// Used by `new_var()` (public API) and `push()` (scope selector allocation).
    pub(super) fn new_var_internal(&mut self) -> Variable {
        // The assumption cache stays VALID across new_var (#8443 follow-up):
        // every per-variable structure below grows eagerly, vsids
        // ensure_num_vars pushes the new variable into both the decision
        // heap and the VMTF queue, and clauses referencing it are deferred
        // by add_clause to the incremental reset's attach path while the
        // cache is valid. Incremental MaxSAT (OLL) allocates totalizer
        // variables before almost every solve; invalidating here forced a
        // full O(num_vars + clauses) reset per core and per exhaust probe.
        // Destructive arena changes still invalidate through the
        // inprocessing_modified_clause_db / reconstruction gates in
        // can_use_incremental_reset.

        let var = Variable(self.num_vars as u32);
        self.num_vars += 1;
        // Recompute ghost guard: chrono-BT requires num_vars > CHRONO_LEVEL_LIMIT (#8466).
        // Incremental mode (push/pop) also creates ghost literals (#8489).
        self.ghost_guard_needed =
            self.num_vars > CHRONO_LEVEL_LIMIT as usize || self.cold.has_ever_scoped;

        // Assign a fresh external index for this new internal variable.
        // New variables always get the next external index (= e2i.len()).
        let ext_var = self.cold.e2i.len() as u32;
        self.cold.e2i.push(var.0);
        self.cold.i2e.push(ext_var);

        // Two entries per variable: positive literal and negative literal
        self.vals.push(0);
        self.vals.push(0);
        self.var_data.push(VarData::UNASSIGNED);
        // Always grow proof ID arrays unconditionally (#8069: Phase 2a).
        self.unit_proof_id.push(0);
        self.unit_proof_sign.push(0);
        self.phase.push(0);
        self.target_phase.push(0);
        self.best_phase.push(0);

        self.min.minimize_flags.push(0);
        self.cold.level0_proof_id.push(0);
        self.cold.level0_proof_sign.push(0);
        self.cold.freeze_counts.push(0);
        self.cold.forced_phase.push(0);
        self.subsume_dirty.push(true); // new variables are dirty for subsumption
        self.l0_gc_dirty.push(false); // #7981: must track all variables including scope selectors
                                      // Two literal indices per variable (positive and negative).
        self.dirty_watches.push(false);
        self.dirty_watches.push(false);
        self.cold.factor_candidate_marks.push(0);
        self.var_lifecycle.push_active();
        self.probe_parent.push(None);
        self.lambda.push(None);
        self.cold.scope_selector_set.push(false);
        self.cold.was_scope_selector.push(false);
        self.glue_stamp.push(0); // indexed by level; max level grows with num_vars
        self.shrink_stamp.push(0);
        self.min
            .minimize_level_seen
            .push(minimization_state::LevelSeen::EMPTY);
        if let Some(ref mut witness) = self.cold.solution_witness {
            witness.push(None);
        }

        debug_assert!(
            self.unit_proof_id.len() == self.num_vars,
            "BUG: unit_proof_id length must track num_vars"
        );
        debug_assert!(
            self.unit_proof_sign.len() == self.num_vars,
            "BUG: unit_proof_sign length must track num_vars"
        );

        self.watches.ensure_num_vars(self.num_vars);
        self.vsids.ensure_num_vars(self.num_vars);
        self.conflict.ensure_num_vars(self.num_vars);
        self.lit_marks.ensure_num_vars(self.num_vars);
        self.inproc.ensure_num_vars(self.num_vars);

        // Grow gc_occ so clauses containing the new variable's literals are
        // tracked by collect_level0_garbage. Without this, SBVA/factorize
        // grow num_vars but gc_occ stays at its original capacity, causing
        // add_clause to silently drop new-variable literals from gc_occ.
        // Then collect_level0_garbage cannot find those clauses, leaving
        // false level-0 literals that corrupt BCP (#8078).
        if let Some(ref mut gc_occ) = self.gc_occ {
            gc_occ.ensure_num_vars(self.num_vars);
        }

        var
    }
}
