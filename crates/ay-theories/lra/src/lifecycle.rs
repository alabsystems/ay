// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor, snapshot restoration, config, and initialization for LRA.
//!
//! `new()`, `from_snapshot()`, `set_terms()`/`unset_terms()`,
//! `soft_reset_warm()`, `terms()`, and mode setters. Scope management
//! (push/pop), full/soft reset, and structural snapshots are in
//! `lifecycle_scope`.

use super::*;

impl LraSolver {
    /// Create a new LRA solver.
    ///
    /// Takes `&TermStore` to populate initial caches. The reference is NOT stored;
    /// only a raw pointer is kept for subsequent `set_terms` calls.
    #[must_use]
    pub fn new(terms: &TermStore) -> Self {
        Self {
            deferred_eq_atoms: Vec::new(),
            a5_core: std::env::var_os("AY_A5_CORE").is_some(),
            terms_ptr: std::ptr::from_ref(terms),
            rows: Vec::new(),
            vars: Vec::new(),
            term_to_var: HashMap::default(),
            var_to_term: HashMap::default(),
            next_var: 0,
            trail: Vec::new(),
            bound_revision: 0,
            scopes: Vec::new(),
            asserted: HashMap::default(),
            asserted_trail: Vec::new(),
            cross_theory_asserted: HashMap::default(),
            cross_theory_asserted_trail: Vec::new(),
            cross_theory_asserted_scopes: Vec::new(),
            atom_cache: HashMap::default(),
            ite_link_terms: Vec::new(),
            ite_link_terms_seen: HashSet::default(),
            current_parsing_atom: None,
            dirty: true,
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::default(),
            propagated_disequality_pairs: HashSet::default(),
            trivial_conflict: None,
            bound_atoms: HashSet::default(),
            persistent_unsupported_atoms: HashSet::default(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1, // non-zero seed for xorshift32
            pivot_rng: 1,
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_lra: lra_debug_flags().debug_lra,
            debug_lra_bounds: lra_debug_flags().debug_lra_bounds,
            debug_lra_assert: lra_debug_flags().debug_lra_assert,
            debug_lra_reset: lra_debug_flags().debug_lra_reset,
            debug_lra_nelson_oppen: lra_debug_flags().debug_lra_nelson_oppen,
            debug_intern: lra_debug_flags().debug_intern,
            // Per-theory runtime statistics (#4706, consolidated #8841).
            stats: stats::LraStats::default(),
            registered_atoms: HashSet::default(),
            decision_index: DecisionCandidateIndex::default(),
            atom_index: HashMap::default(),
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::default(),
            combined_theory_mode: false,
            atom_slack: HashMap::default(),
            expr_to_slack: HashMap::default(),
            slack_var_set: HashSet::default(),
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::default(),
            fixed_term_value_members: HashMap::default(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            col_index: Vec::new(),
            pivot_work_vec: Vec::new(),
            pivot_work_dirty: Vec::new(),
            pivot_row_coeffs_buf: Vec::new(),
            pivot_row_constant_buf: Rational::zero(),
            pivot_subst_i64_buf: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            pending_expr_splits: Vec::new(),
            bounds_tightened_since_simplex: true,
            post_simplex_bounds_added: false,
            vars_tightened_since_simplex: Vec::new(),
            guard_clean_valid: false,
            last_simplex_verified: false,
            guard_tracked_only: false,
            rows_len_at_last_implied: 0,
            ib_overlay_complete: false,
            warm_reuse_hint: false,
            implied_trail: Vec::new(),
            implied_trail_scopes: Vec::new(),
            propagated_trail: Vec::new(),
            propagated_trail_scopes: Vec::new(),
            eager_repropagate_on_pop: false,
            direct_bounds_changed_since_implied: true,
            bcp_implied_single_pass: false,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: Vec::new(),
            row_computed_gen: Vec::new(),
            implied_tighten_streak: Vec::new(),
            implied_tighten_scratch: Vec::new(),
            implied_tighten_touched: Vec::new(),
            implied_work_done: 0,
            big_bound_seen: false,
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            feasible_value_snapshot: Vec::new(),
            pivots_at_last_snapshot: u64::MAX,
            phase_hint_cache: HashMap::default(),
            phase_hint_epoch: 0,
            rows_at_check_start: 0,
            to_int_terms: Vec::new(),
            injected_to_int_axioms: HashSet::default(),
            propagation_dirty_vars: DenseU32Set::default(),
            compound_use_index: HashMap::default(),
            var_to_atoms: HashMap::default(),
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            basic_var_to_row: HashMap::default(),
            touched_rows: DenseIdxSet::default(),
            propagate_direct_touched_rows_pending: false,
            implied_bounds_fresh: false,
            disequality_trail: Vec::new(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            unassigned_atom_count: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            heap_epoch: 1,
            in_infeasible_heap: Vec::new(),
            heap_stale: true,
            float_simplex: simplex::float_simplex::FloatSimplex::new(),
            reason_seen_buf: HashSet::default(),
            not_inner_cache: HashMap::default(),
            const_bool_cache: HashMap::default(),
            refinement_eligible_cache: HashMap::default(),
            is_integer_sort_cache: HashMap::default(),
            bcp_implied_dry_streak: 0,
            bcp_cascade_dry_streak: 0,
            max_row_width: 0,
            dirty_vars_scratch: Vec::new(),
            newly_bounded_scratch: HashSet::default(),
            theory_prop_jit: ay_jit::TheoryPropJit::new(),
            theory_prop_jit_compiled: false,
            theory_prop_results: Vec::new(),
            pivot_row_cache: ay_jit::PivotRowCache::new(),
            lra_basis_region_requests: Vec::new(),
            lra_basis_region_candidate: None,
            lra_basis_region_basis_epoch: 0,
            no_theory_propagation: lra_debug_flags().no_theory_propagation,
            no_implied_bounds: lra_debug_flags().no_implied_bounds,
            no_bound_refinement: lra_debug_flags().no_bound_refinement,
            max_fixpoint_rounds: lra_debug_flags().max_fixpoint_rounds,
            negation_partners: Vec::new(),
            standalone_simplex_mode: false,
            propagation_candidates_buf: Vec::new(),
            propagation_seen_buf: HashSet::default(),
            touched_rows_snapshot_buf: DenseIdxSet::default(),
            newly_bounded_sorted_buf: Vec::new(),
            propagation_output_buf: Vec::new(),
            interval_reason_seen_buf: HashSet::default(),
            all_newly_bounded_buf: DenseU32Set::default(),
        }
    }

    /// Construct an `LraSolver` directly from a structural snapshot, avoiding
    /// the allocate-then-overwrite pattern of `new()` + `import_structural_snapshot()`.
    ///
    /// Returns `Some(solver)` if the snapshot downcasts successfully, `None` otherwise.
    /// The returned solver is in a clean assertion state (same as after `import_structural_snapshot`):
    /// all bounds are cleared, basic variable values are set to row constants, and
    /// `touched_rows` is empty.
    ///
    /// #6590: This eliminates ~50 empty collection allocations per split-loop iteration
    /// when a snapshot is available from a previous iteration.
    pub fn from_snapshot(terms: &TermStore, snapshot: Box<dyn std::any::Any>) -> Option<Self> {
        Self::try_from_snapshot(terms, snapshot).ok()
    }

    pub(crate) fn try_from_snapshot(
        terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>> {
        let mut snap = snapshot.downcast::<LraStructuralSnapshot>()?;
        let var_count = snap.vars.len();
        // Fix A1: adopt the persisted theory-prop JIT when present. It was
        // compiled for exactly the atom_index this snapshot restores; later
        // atom registrations re-validate via the atom-index fingerprint.
        let (theory_prop_jit, theory_prop_jit_compiled) = match snap.theory_prop_jit.take() {
            Some(jit) => (jit, true),
            None => (ay_jit::TheoryPropJit::new(), false),
        };
        // Build propagation_dirty_vars from the atom and compound indices.
        let mut propagation_dirty_vars = DenseU32Set::default();
        propagation_dirty_vars.extend(snap.atom_index.keys().copied());
        propagation_dirty_vars.extend(snap.compound_use_index.keys().copied());
        let mut solver = Self {
            deferred_eq_atoms: Vec::new(),
            a5_core: std::env::var_os("AY_A5_CORE").is_some(),
            terms_ptr: std::ptr::from_ref(terms),
            // Structural fields from snapshot (moved, not cloned):
            rows: snap.rows,
            vars: snap.vars,
            term_to_var: snap.term_to_var,
            var_to_term: snap.var_to_term,
            next_var: snap.next_var,
            atom_cache: snap.atom_cache,
            ite_link_terms: snap.ite_link_terms,
            ite_link_terms_seen: snap.ite_link_terms_seen,
            registered_atoms: snap.registered_atoms,
            // Rebuilt from registered_atoms after construction (below).
            decision_index: DecisionCandidateIndex::default(),
            atom_index: snap.atom_index,
            compound_use_index: snap.compound_use_index,
            var_to_atoms: snap.var_to_atoms,
            atom_slack: snap.atom_slack,
            expr_to_slack: snap.expr_to_slack,
            slack_var_set: snap.slack_var_set,
            propagated_equality_pairs: snap.propagated_equality_pairs,
            propagated_disequality_pairs: snap.propagated_disequality_pairs,
            basic_var_to_row: snap.basic_var_to_row,
            col_index: snap.col_index,
            pivot_work_vec: Vec::new(),
            pivot_work_dirty: Vec::new(),
            pivot_row_coeffs_buf: Vec::new(),
            pivot_row_constant_buf: Rational::zero(),
            pivot_subst_i64_buf: Vec::new(),
            to_int_terms: snap.to_int_terms,
            unassigned_atom_count: snap.unassigned_atom_count,
            not_inner_cache: snap.not_inner_cache,
            const_bool_cache: snap.const_bool_cache,
            refinement_eligible_cache: snap.refinement_eligible_cache,
            is_integer_sort_cache: snap.is_integer_sort_cache,
            // Assertion-derived fields start clean:
            trail: Vec::new(),
            bound_revision: 0,
            scopes: Vec::new(),
            asserted: HashMap::default(),
            asserted_trail: Vec::new(),
            cross_theory_asserted: HashMap::default(),
            cross_theory_asserted_trail: Vec::new(),
            cross_theory_asserted_scopes: Vec::new(),
            current_parsing_atom: None,
            dirty: true,
            pending_equalities: Vec::new(),
            trivial_conflict: None,
            bound_atoms: HashSet::default(),
            persistent_unsupported_atoms: HashSet::default(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1,
            pivot_rng: 1,
            debug_lra: lra_debug_flags().debug_lra,
            debug_lra_bounds: lra_debug_flags().debug_lra_bounds,
            debug_lra_assert: lra_debug_flags().debug_lra_assert,
            debug_lra_reset: lra_debug_flags().debug_lra_reset,
            debug_lra_nelson_oppen: lra_debug_flags().debug_lra_nelson_oppen,
            debug_intern: lra_debug_flags().debug_intern,
            stats: stats::LraStats::default(),
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::default(),
            combined_theory_mode: false,
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::default(),
            fixed_term_value_members: HashMap::default(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            pending_expr_splits: Vec::new(),
            bounds_tightened_since_simplex: true,
            post_simplex_bounds_added: false,
            vars_tightened_since_simplex: Vec::new(),
            guard_clean_valid: false,
            last_simplex_verified: false,
            guard_tracked_only: false,
            rows_len_at_last_implied: 0,
            ib_overlay_complete: false,
            warm_reuse_hint: false,
            implied_trail: Vec::new(),
            implied_trail_scopes: Vec::new(),
            propagated_trail: Vec::new(),
            propagated_trail_scopes: Vec::new(),
            eager_repropagate_on_pop: false,
            direct_bounds_changed_since_implied: true,
            bcp_implied_single_pass: false,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: vec![0; var_count],
            row_computed_gen: Vec::new(),
            implied_tighten_streak: Vec::new(),
            implied_tighten_scratch: Vec::new(),
            implied_tighten_touched: Vec::new(),
            implied_work_done: 0,
            big_bound_seen: false,
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            feasible_value_snapshot: Vec::new(),
            pivots_at_last_snapshot: u64::MAX,
            phase_hint_cache: HashMap::default(),
            phase_hint_epoch: 0,
            rows_at_check_start: 0,
            injected_to_int_axioms: HashSet::default(),
            propagation_dirty_vars,
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            touched_rows: DenseIdxSet::default(),
            propagate_direct_touched_rows_pending: false,
            implied_bounds_fresh: false,
            disequality_trail: Vec::new(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            heap_epoch: 1,
            in_infeasible_heap: vec![0; var_count],
            heap_stale: true,
            float_simplex: simplex::float_simplex::FloatSimplex::new(),
            reason_seen_buf: HashSet::default(),
            bcp_implied_dry_streak: 0,
            bcp_cascade_dry_streak: 0,
            max_row_width: 0,
            dirty_vars_scratch: Vec::new(),
            newly_bounded_scratch: HashSet::default(),
            theory_prop_jit,
            theory_prop_jit_compiled,
            theory_prop_results: Vec::new(),
            // Policy decision (Fix A1): pivot_row_cache is not persisted —
            // it is lazily populated behind COMPILE_THRESHOLD use counts (no
            // eager per-instance compile cost) and holds non-clonable
            // background-compiler state. See import_structural_snapshot_inner.
            pivot_row_cache: ay_jit::PivotRowCache::new(),
            lra_basis_region_requests: Vec::new(),
            lra_basis_region_candidate: None,
            lra_basis_region_basis_epoch: 0,
            no_theory_propagation: lra_debug_flags().no_theory_propagation,
            no_implied_bounds: lra_debug_flags().no_implied_bounds,
            no_bound_refinement: lra_debug_flags().no_bound_refinement,
            max_fixpoint_rounds: lra_debug_flags().max_fixpoint_rounds,
            negation_partners: snap.negation_partners,
            standalone_simplex_mode: false,
            propagation_candidates_buf: Vec::new(),
            propagation_seen_buf: HashSet::default(),
            touched_rows_snapshot_buf: DenseIdxSet::default(),
            newly_bounded_sorted_buf: Vec::new(),
            propagation_output_buf: Vec::new(),
            interval_reason_seen_buf: HashSet::default(),
            all_newly_bounded_buf: DenseU32Set::default(),
        };
        // Clear variable bounds and restore simplex invariant (same as import_structural_snapshot).
        for var_info in &mut solver.vars {
            var_info.lower = None;
            var_info.upper = None;
            var_info.value = InfRational::default();
        }
        for row in &solver.rows {
            let basic = row.basic_var as usize;
            if basic < solver.vars.len() {
                solver.vars[basic].value = InfRational::from_rat(row.constant.clone());
            }
        }
        // #6617: unassigned_atom_count is initialized from snapshot above, so no
        // full recount needed.
        // STAGE B: assertion state starts clean, so every registered non-distinct
        // atom is an unasserted decision candidate — rebuild the index to match.
        solver.rebuild_decision_index();
        Ok(solver)
    }

    /// Kani-only constructor: initializes only the pointer field, avoids
    /// `TermStore::new()` and `lra_debug_flags()` which trigger deep
    /// BTree/HashMap symbolic exploration that CBMC cannot handle (#6612).
    #[cfg(kani)]
    pub(crate) fn new_kani_minimal(ptr: *const TermStore) -> Self {
        Self {
            terms_ptr: ptr,
            rows: Vec::new(),
            vars: Vec::new(),
            term_to_var: HashMap::default(),
            var_to_term: HashMap::default(),
            next_var: 0,
            trail: Vec::new(),
            bound_revision: 0,
            scopes: Vec::new(),
            asserted: HashMap::default(),
            asserted_trail: Vec::new(),
            cross_theory_asserted: HashMap::default(),
            cross_theory_asserted_trail: Vec::new(),
            cross_theory_asserted_scopes: Vec::new(),
            atom_cache: HashMap::default(),
            ite_link_terms: Vec::new(),
            ite_link_terms_seen: HashSet::default(),
            current_parsing_atom: None,
            dirty: false,
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::default(),
            propagated_disequality_pairs: HashSet::default(),
            trivial_conflict: None,
            bound_atoms: HashSet::default(),
            persistent_unsupported_atoms: HashSet::default(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1,
            pivot_rng: 1,
            debug_lra: false,
            debug_lra_bounds: false,
            debug_lra_assert: false,
            debug_lra_reset: false,
            debug_lra_nelson_oppen: false,
            debug_intern: false,
            stats: stats::LraStats::default(),
            registered_atoms: HashSet::default(),
            decision_index: DecisionCandidateIndex::default(),
            atom_index: HashMap::default(),
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::default(),
            combined_theory_mode: false,
            atom_slack: HashMap::default(),
            expr_to_slack: HashMap::default(),
            slack_var_set: HashSet::default(),
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::default(),
            fixed_term_value_members: HashMap::default(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            col_index: Vec::new(),
            pivot_work_vec: Vec::new(),
            pivot_work_dirty: Vec::new(),
            pivot_row_coeffs_buf: Vec::new(),
            pivot_row_constant_buf: Rational::zero(),
            pivot_subst_i64_buf: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            bounds_tightened_since_simplex: false,
            post_simplex_bounds_added: false,
            vars_tightened_since_simplex: Vec::new(),
            guard_clean_valid: false,
            last_simplex_verified: false,
            guard_tracked_only: false,
            rows_len_at_last_implied: 0,
            ib_overlay_complete: false,
            warm_reuse_hint: false,
            implied_trail: Vec::new(),
            implied_trail_scopes: Vec::new(),
            propagated_trail: Vec::new(),
            propagated_trail_scopes: Vec::new(),
            eager_repropagate_on_pop: false,
            direct_bounds_changed_since_implied: false,
            bcp_implied_single_pass: false,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: Vec::new(),
            row_computed_gen: Vec::new(),
            implied_tighten_streak: Vec::new(),
            implied_tighten_scratch: Vec::new(),
            implied_tighten_touched: Vec::new(),
            implied_work_done: 0,
            big_bound_seen: false,
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            feasible_value_snapshot: Vec::new(),
            pivots_at_last_snapshot: u64::MAX,
            phase_hint_cache: HashMap::default(),
            phase_hint_epoch: 0,
            rows_at_check_start: 0,
            to_int_terms: Vec::new(),
            injected_to_int_axioms: HashSet::default(),
            propagation_dirty_vars: DenseU32Set::default(),
            compound_use_index: HashMap::default(),
            var_to_atoms: HashMap::default(),
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            basic_var_to_row: HashMap::default(),
            touched_rows: DenseIdxSet::default(),
            propagate_direct_touched_rows_pending: false,
            implied_bounds_fresh: false,
            disequality_trail: Vec::new(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            unassigned_atom_count: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            heap_epoch: 1,
            in_infeasible_heap: Vec::new(),
            heap_stale: true,
            float_simplex: simplex::float_simplex::FloatSimplex::new(),
            reason_seen_buf: HashSet::default(),
            not_inner_cache: HashMap::default(),
            const_bool_cache: HashMap::default(),
            refinement_eligible_cache: HashMap::default(),
            is_integer_sort_cache: HashMap::default(),
            dirty_vars_scratch: Vec::new(),
            bcp_implied_dry_streak: 0,
            bcp_cascade_dry_streak: 0,
            max_row_width: 0,
            theory_prop_jit: ay_jit::TheoryPropJit::new(),
            theory_prop_jit_compiled: false,
            theory_prop_results: Vec::new(),
            pivot_row_cache: ay_jit::PivotRowCache::new(),
            lra_basis_region_requests: Vec::new(),
            lra_basis_region_candidate: None,
            lra_basis_region_basis_epoch: 0,
            negation_partners: Vec::new(),
            standalone_simplex_mode: false,
            propagation_output_buf: Vec::new(),
            interval_reason_seen_buf: HashSet::default(),
            all_newly_bounded_buf: DenseU32Set::default(),
        }
    }

    /// Enable standalone-simplex mode (#8257).
    ///
    /// This skips post-simplex propagation and speculative model-equality
    /// discovery that require a DPLL(T) driver, while retaining the
    /// unsupported-atom and disequality soundness gates. It also eliminates the
    /// O(rows * width * rounds) implied-bounds overhead when only a standalone
    /// simplex feasibility/optimization result is needed.
    pub fn set_standalone_simplex_mode(&mut self) {
        self.standalone_simplex_mode = true;
    }

    /// Enable standalone-simplex mode for a verification-only caller.
    ///
    /// Used by `verify_lra_conflict_semantic` and `verify_lra_propagation` in
    /// the DPLL(T) verification pipeline. New non-verification callers should
    /// use [`Self::set_standalone_simplex_mode`].
    pub fn set_verification_mode(&mut self) {
        self.set_standalone_simplex_mode();
    }

    /// Disable (or re-enable) LRA theory propagation for this solver instance.
    ///
    /// Per-instance counterpart of the process-global `AY_NO_THEORY_PROPAGATION`
    /// debug flag (#8319). When disabled:
    /// - `propagate()` discards all pending propagations
    ///   (`theory_solver/propagation.rs`), and
    /// - if bound refinement is ALSO disabled (`no_bound_refinement`),
    ///   BCP-time implied-bounds computation is skipped entirely
    ///   (`run_post_simplex_propagation` skip gate, `check_atoms.rs`).
    ///   With refinement enabled the BCP computation is kept: its derived
    ///   bounds feed BP_REFINE dynamic atom creation, which is load-bearing
    ///   for eager-arm completeness (DRAGON_3 depth-1 flips sat→unknown
    ///   without it).
    ///
    /// Used by the CHC BMC transition-system lane: on DRAGON-class QF_LIA
    /// sat-type model searches, BCP-time implied-bounds propagation causes a
    /// CDCL search livelock (long interval-reconstructed reasons -> weak
    /// learned clauses; suppressed early conflicts trip the #9505 adaptive
    /// theory-decision mode; LP-model phase hints override phase saving).
    /// With propagation off, the same query solves ~100x faster
    /// (the development design notes).
    ///
    /// Note: callers must set this BEFORE solving begins; it is not part of
    /// the push/pop trail. Structural-snapshot import does not modify it
    /// (`import_structural_snapshot_inner` only restores tableau/atom state),
    /// but `from_snapshot`/`try_from_snapshot` construct a fresh solver from
    /// the process-global flag, so re-apply after those constructors.
    pub fn set_no_theory_propagation(&mut self, disabled: bool) {
        self.no_theory_propagation = disabled;
    }

    /// Set the TermStore pointer for the next operation batch (#6590 Packet 2).
    ///
    /// # Safety contract
    /// The caller must ensure the `TermStore` outlives any subsequent calls to
    /// `register_atom`, `check`, `assert_literal`, etc. before `unset_terms`.
    pub fn set_terms(&mut self, terms: &TermStore) {
        self.terms_ptr = std::ptr::from_ref(terms);
    }

    /// Clear the TermStore pointer after an operation batch (#6590 Packet 2).
    pub fn unset_terms(&mut self) {
        self.terms_ptr = std::ptr::null();
    }

    /// Warm soft-reset: clear assertion state but preserve simplex variable
    /// values and basis (#6590 Packet 3).
    ///
    /// Like `soft_reset()`, this clears bounds, assertion trails, and conflict
    /// state so the solver is ready for a new set of assertions. Unlike
    /// `soft_reset()`, it keeps variable values from the previous iteration.
    /// When the same (or similar) atoms are re-asserted, `check()` calls
    /// `restore_feasibility()` which only pivots variables whose bounds have
    /// been violated — matching Z3's persistent `lar_solver` warm-start.
    pub fn soft_reset_warm(&mut self) {
        // Bound slots are cleared wholesale below — stale-memo hazard for LIA.
        self.bump_bound_revision();
        self.asserted.clear();
        self.asserted_trail.clear();
        self.cross_theory_asserted.clear();
        self.cross_theory_asserted_trail.clear();
        self.trail.clear();
        self.scopes.clear();
        self.cross_theory_asserted_scopes.clear();
        self.pending_equalities.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        self.propagated_atoms.clear();
        // #inc-prop-trail: set nuked wholesale — drop the undo trail with it.
        self.propagated_trail.clear();
        self.propagated_trail_scopes.clear();
        // #8599: Shrink propagated_atoms after warm reset to release memory.
        self.propagated_atoms.shrink_to_fit();
        // Preserve any dirty vars already accumulated by the current warm
        // iteration, then reseed the structural keys needed for the next pass.
        // This keeps compound wakeups alive across persistent split-loop
        // warm resets instead of starting each round from a blank dirty set.
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
        // #8187: The post_simplex_bounds_added soundness gate flag is reset
        // at each check entry, so its value after soft_reset is irrelevant;
        // clear it for hygiene so a stale `true` can't accidentally be read
        // before the next check() call.
        self.post_simplex_bounds_added = false;
        // #8008: Reset full-check conflict counter. Note: deferred-simplex
        // mode was attempted (#8187) but shown to cause false UNSAT — AY
        // always runs BCP simplex. This counter is kept for statistics.
        self.stats.full_check_conflict_count = 0;
        self.vars_tightened_since_simplex.clear();
        // #inc-guard-memo: warm reset rewrites variable values below.
        // Also breaks the tracked-only chain (#inc-guard-chain).
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.clear();
        self.last_simplex_feasible = false;
        self.last_simplex_feasible_scopes.clear();
        self.rows_at_check_start = 0;

        // Preserve already-encoded model-equality pairs across warm iterations.
        // The persistent split loop keeps the SAT solver alive, so fixed-term and
        // offset equalities requested in an earlier round are still available as
        // SAT atoms. Clearing this set would re-request the same equality batch
        // every warm iteration and can starve convergence on large chains.
        // WARM: clear bounds but KEEP variable values from previous iteration.
        // The simplex basis (row structure, basic/non-basic assignment) persists.
        // Values approximate the previous feasible solution; restore_feasibility()
        // will fix any variables whose new bounds are violated.
        for var_info in &mut self.vars {
            var_info.lower = None;
            var_info.upper = None;
            // var_info.value preserved — this is the warm-start win
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
        self.disequality_trail.clear();
        self.disequality_trail_scopes.clear();
        self.shared_disequality_trail.clear();
        self.shared_disequality_trail_scopes.clear();
        self.pending_diseq_splits.clear();
        self.pending_expr_splits.clear();
        self.pivot_row_cache.clear_lra_basis_region_artifacts();
        self.lra_basis_region_requests.clear();
        self.lra_basis_region_candidate = None;
        // STAGE B: warm reset cleared asserted but preserved registered_atoms —
        // every registered non-distinct atom is again an unasserted candidate.
        self.rebuild_decision_index();
    }

    /// Access the TermStore via the stored raw pointer.
    ///
    /// Returns a reference with a lifetime detached from `&self` so that
    /// calling `self.terms()` does not prevent subsequent `&mut self` access
    /// to other fields. This is sound because the raw pointer's validity is
    /// guaranteed by the `set_terms()` caller, not by `&self`.
    ///
    /// # Thread Safety
    ///
    /// This method dereferences a raw pointer through `&self`, which means
    /// concurrent calls from multiple threads would be a data race on the
    /// TermStore (even though the pointer value itself is not mutated).
    /// LraSolver deliberately does NOT implement `Sync` to prevent this:
    /// `&LraSolver` cannot be shared across threads. All access is via
    /// `&mut self` (exclusive ownership), which Rust's borrow checker
    /// enforces at compile time.
    ///
    /// # Panics
    /// Panics if `terms_ptr` is null (i.e., `set_terms` was not called).
    #[inline]
    #[allow(clippy::needless_lifetimes)]
    #[allow(unsafe_code)]
    pub fn terms<'t>(&self) -> &'t TermStore {
        let ptr = self.terms_ptr;
        assert!(
            !ptr.is_null(),
            "BUG: LraSolver::terms() called without set_terms()"
        );
        // SAFETY: The TermStore pointer is set by set_terms() and guaranteed
        // alive for the duration of the operation batch. The lifetime 't is
        // independent of &self, allowing concurrent &mut self field access
        // to other fields. This is sound because:
        // 1. The pointer is non-null (checked above).
        // 2. The TermStore is alive and not mutably borrowed for the duration
        //    of the set_terms/unset_terms bracket (caller invariant).
        // 3. LraSolver is !Sync, so this method cannot be called concurrently
        //    from multiple threads.
        unsafe { &*ptr }
    }

    /// Enable integer mode: strict bounds are canonicalized to non-strict.
    /// `expr < 0` becomes `expr <= -1`, `expr > 0` becomes `expr >= 1`.
    pub fn set_integer_mode(&mut self, enabled: bool) {
        self.integer_mode = enabled;
    }

    /// Enable combined theory mode: suppress unsupported-atom marking for
    /// unknown function/term catch-all arms in `parse_linear_expr`.
    /// Cross-theory terms (array selects, UF applications) are expected in
    /// combined solvers and handled by the Nelson-Oppen loop (#5524).
    pub fn set_combined_theory_mode(&mut self, enabled: bool) {
        self.combined_theory_mode = enabled;
    }

    /// Whether combined theory mode is enabled (see `set_combined_theory_mode`).
    pub fn combined_theory_mode(&self) -> bool {
        self.combined_theory_mode
    }

    /// #uflia-eager-sweep: opt into the pre-#inc-implied-trail /
    /// pre-#inc-prop-trail pop semantics (wholesale-clear the propagation
    /// memory on every pop, forcing a full re-derivation/re-propagation
    /// sweep on the next check). For the eager DPLL(T) combined-theory
    /// lanes, whose inline theory-conflict engine depends on that sweep;
    /// see the `eager_repropagate_on_pop` field doc.
    pub fn set_eager_repropagate_on_pop(&mut self, enabled: bool) {
        self.eager_repropagate_on_pop = enabled;
    }

    /// Drain buffered disequality split requests collected during batch evaluation (#6259).
    ///
    /// When `check()` finds multiple violated single-variable disequalities, it returns
    /// the first via `NeedDisequalitySplit` and buffers the rest here. The DPLL(T) split
    /// loop should call this method to retrieve all remaining splits and process them in
    /// a single iteration, avoiding O(N) solver restarts.
    pub fn drain_pending_diseq_splits(&mut self) -> Vec<DisequalitySplitRequest> {
        std::mem::take(&mut self.pending_diseq_splits)
    }

    /// Drain buffered expression split requests collected during batch evaluation (#8707).
    ///
    /// When `check()` finds multiple violated multi-variable disequalities
    /// (e.g., from `(distinct E1 E2 ... En)` over arithmetic expressions), it
    /// returns the first via `NeedExpressionSplit` and buffers the rest here.
    /// The DPLL(T) split loop should call this method to retrieve all remaining
    /// splits and process them in a single iteration, avoiding O(N) solver
    /// restarts.
    pub fn drain_pending_expr_splits(&mut self) -> Vec<ExpressionSplitRequest> {
        std::mem::take(&mut self.pending_expr_splits)
    }
}
