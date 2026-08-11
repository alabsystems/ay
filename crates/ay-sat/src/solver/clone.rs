// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT solver cloning for IC3/PDR frame reuse (#8432).
//!
//! IC3/PDR creates many incremental SAT queries at different frame levels.
//! Currently each frame level re-initializes solver state. Solver cloning
//! lets IC3 fork a solver at a frame checkpoint and reuse its learned
//! clauses and VSIDS scores, avoiding re-learning.
//!
//! The `clone_for_incremental()` method performs a deep copy of the
//! solver's essential state (clauses, watches, trail, VSIDS, phases)
//! while resetting non-essential state (JIT, proofs, diagnostics,
//! tracing). The cloned solver is ready for independent incremental
//! solving.
//!
//! Reference: CaDiCaL's copy constructor (`solver.cpp`) performs a
//! similar selective deep copy.

use super::*;

impl Solver {
    /// Create a deep copy for IC3/PDR frame reuse with a clean search state.
    ///
    /// This is the primary entry point for IC3 solver cloning (#8432).
    /// It produces an independent solver that shares the same clause base
    /// (including IC3 lemma protection bits) and VSIDS scores, but with
    /// a clean search state ready for new IC3 queries.
    ///
    /// The clone preserves:
    /// - All clauses (original and learned) with IC3_LEMMA_BIT flags
    /// - VSIDS variable activity scores and heap ordering
    /// - Phase saving arrays (saved, target, best phases)
    /// - IC3 mode flag and constraint activation variable
    /// - Level-0 unit propagations (proven facts)
    ///
    /// The clone resets:
    /// - Trail above level 0 (search decisions and non-root propagations)
    /// - Decision level to 0
    /// - Conflict/decision counters to 0
    /// - BVE reconstruction stack (not relevant for IC3 clones)
    /// - JIT compiled code, proofs, diagnostics, tracing
    ///
    /// The returned solver is fully independent: mutations to one do not
    /// affect the other.
    ///
    /// Reference: GipSAT (rIC3) clones frame solvers to share learned
    /// lemmas between frames, avoiding re-learning.
    #[must_use]
    pub fn clone_for_ic3(&self) -> Self {
        let mut clone = self.clone_for_incremental();

        // Reset search state to level 0: keep only root-level assignments.
        // This is what makes clone_for_ic3 different from clone_for_incremental:
        // the clone starts with a clean trail but retains proven unit facts.

        // Partition trail into level-0 (keep) and above (discard).
        let level0_end = if clone.trail_lim.is_empty() {
            // No decisions were made — entire trail is level 0.
            clone.trail.len()
        } else {
            // trail_lim[0] is the trail position of the first decision.
            clone.trail_lim[0]
        };

        // Clear assignments for variables above level 0.
        for &lit in &clone.trail[level0_end..] {
            let var_idx = lit.variable().index();
            // Clear vals[] (positive and negative literal indices).
            let pos_idx = var_idx * 2;
            let neg_idx = pos_idx + 1;
            if pos_idx < clone.vals.len() {
                clone.vals[pos_idx] = 0;
            }
            if neg_idx < clone.vals.len() {
                clone.vals[neg_idx] = 0;
            }
            // Reset var_data to unassigned.
            if var_idx < clone.var_data.len() {
                clone.var_data[var_idx] = VarData::UNASSIGNED;
            }
        }

        // Truncate trail to level-0 entries only.
        clone.trail.truncate(level0_end);
        clone.trail_lim.clear();
        clone.qhead = clone.trail.len();
        clone.decision_level = 0;

        // Reset search counters — the clone starts a fresh search.
        clone.num_conflicts = 0;
        clone.conflicts_since_restart = 0;
        clone.num_decisions = 0;
        clone.num_propagations = 0;
        clone.num_search_propagations = 0;
        clone.search_ticks = [0; 2];

        // Ensure IC3 mode is active on the clone.
        if !clone.cold.ic3_mode {
            clone.set_ic3_mode();
        }

        // Re-insert now-unassigned variables into the VSIDS heap.
        // After clearing above-level-0 assignments, those variables need
        // to be back in the decision heap with their preserved activity
        // scores so they are eligible for branching.
        for var_idx in 0..clone.num_vars {
            let pos_idx = var_idx * 2;
            if pos_idx < clone.vals.len() && clone.vals[pos_idx] == 0 {
                clone.vsids.insert_into_heap(Variable(var_idx as u32));
            }
        }

        // Clear domain restriction — IC3 caller sets it per query.
        clone.active_domain = None;
        clone.decision_domain = None;
        clone.bucket_queue_active = false;
        clone.domain_restarts = 0;

        clone
    }

    /// Create a deep copy of this solver for incremental IC3/PDR frame reuse.
    ///
    /// Deep-copies the essential solving state:
    /// - Clause arena (all original and learned clauses)
    /// - Watch lists (2WL structure)
    /// - VSIDS/VMTF variable scores and heap
    /// - Trail, variable assignments, and decision levels
    /// - Phase information (saved, target, best phases)
    /// - Conflict analysis workspace
    /// - Restart and reduction scheduling state
    /// - Incremental scoping state (push/pop selectors)
    ///
    /// Resets non-essential/non-clonable state:
    /// - JIT compiled code (must be recompiled if needed)
    /// - Proof logging (cloned solver produces no proofs)
    /// - Diagnostic tracing (TLA, decision trace, diagnostic trace)
    /// - Forward checker (proof verification)
    /// - Progress observer callbacks
    /// - Inprocessing engines (re-initialized fresh)
    ///
    /// The cooperative-cancellation interrupt handle is PRESERVED (shared via the
    /// `Arc`): a clone used for an incremental query must honor the same
    /// timeout/interrupt as its parent, otherwise a long inprocessing pass on the
    /// clone runs unbounded past the deadline (the closure-based `should_stop` is
    /// only threaded into the CDCL main loop, not inprocessing).
    ///
    /// The returned solver is independent: modifications to either the
    /// original or the clone do not affect the other.
    ///
    /// For IC3/PDR use cases, prefer `clone_for_ic3()` which additionally
    /// resets the search state to level 0 for clean frame reuse.
    #[must_use]
    pub fn clone_for_incremental(&self) -> Self {
        let num_vars = self.num_vars;
        let mut stats = self.stats.clone();
        stats.clear_bcp_learned_1963_blocker_certs();

        // Clone the cold state with selective resets for non-clonable fields.
        let cold = Box::new(self.cold.clone_for_incremental(num_vars));

        Self {
            // ── HOT: BCP inner loop ──────────────────────────────────
            vals: self.vals.clone(),
            watches: self.watches.clone(),
            arena: self.arena.clone(),
            trail: self.trail.clone(),
            trail_lim: self.trail_lim.clone(),
            qhead: self.qhead,
            decision_level: self.decision_level,
            var_data: self.var_data.clone(),
            phase: self.phase.clone(),
            chrono_enabled: self.chrono_enabled,
            ghost_guard_needed: self.ghost_guard_needed,
            lambda: self.lambda.clone(),
            suppress_phase_saving: self.suppress_phase_saving,
            deferred_watch_list: WatchList::new(),
            deferred_replacement_watches: Vec::new(),
            num_vars,
            user_num_vars: self.user_num_vars,
            has_empty_clause: self.has_empty_clause,
            num_propagations: self.num_propagations,
            num_search_propagations: self.num_search_propagations,
            no_conflict_until: self.no_conflict_until,
            search_ticks: self.search_ticks,
            stable_mode: self.stable_mode,
            active_branch_heuristic: self.active_branch_heuristic,
            probing_mode: false,
            last_conflict_clause_ref: None,
            last_conflict_clause_id: 0,

            // ── WARM: per-conflict / per-decision ────────────────────
            num_conflicts: self.num_conflicts,
            conflicts_since_restart: self.conflicts_since_restart,
            num_decisions: self.num_decisions,
            vsids: self.vsids.clone(),
            conflict: self.conflict.clone(),
            target_phase: self.target_phase.clone(),
            best_phase: self.best_phase.clone(),
            target_trail_len: self.target_trail_len,
            best_trail_len: self.best_trail_len,
            suppress_reduce_db: false,
            // No proof manager for the clone — IC3 clones don't need proofs.
            proof_manager: None,
            #[cfg(debug_assertions)]
            solve_proof_mode: None,
            chrono_reuse_trail: self.chrono_reuse_trail,
            stats,
            num_original_clauses: self.num_original_clauses,
            fixed_count: self.fixed_count,
            unit_proof_id: self.unit_proof_id.clone(),
            unit_proof_sign: self.unit_proof_sign.clone(),
            pending_theory_unit_proof_ids: Vec::new(),
            reason_clause_marks: self.reason_clause_marks.clone(),
            reason_clause_epoch: self.reason_clause_epoch,
            reason_marks_invalidated: self.reason_marks_invalidated,
            bump_order_sort_buf: Vec::new(),
            backbone_seen: self.backbone_seen.clone(),
            vivify_analyzed: vec![false; num_vars],
            vivify_analyzed_to_clear: Vec::with_capacity(64),
            glue_stamp: self.glue_stamp.clone(),
            glue_stamp_counter: self.glue_stamp_counter,
            shrink_stamp: self.shrink_stamp.clone(),
            shrink_stamp_counter: self.shrink_stamp_counter,
            shrink_enabled: self.shrink_enabled,
            reap: reap::Reap::new(),
            ws_shrink_entries: Vec::new(),
            ws_shrink_result: Vec::new(),
            ws_shrink_block_lits: Vec::new(),
            ws_shrink_chain: Vec::new(),
            tiers: self.tiers.clone(),
            min: self.min.clone(),
            phase_init: self.phase_init.clone(),
            pending_theory_conflicts: std::collections::VecDeque::new(),
            pending_garbage_count: 0,
            watches_disconnected: false,
            defer_stale_reason_cleanup: false,
            defer_proof_deletions: false,
            deferred_proof_deletions: Vec::new(),
            earliest_affected_trail_pos: None,
            stale_reasons: Vec::new(),
            hbr_enabled: self.hbr_enabled,
            lrat_probe_parent_chain_enabled: self.lrat_probe_parent_chain_enabled,
            lrat_proof_clamp_probe_rescue_enabled: self.lrat_proof_clamp_probe_rescue_enabled,
            inprocessing_yield_productivity_rescue_enabled: self
                .inprocessing_yield_productivity_rescue_enabled,
            inprocessing_yield_rescue_backbone_cooldown_enabled: self
                .inprocessing_yield_rescue_backbone_cooldown_enabled,
            bounded_backbone_zero_decompose_backoff_enabled: self
                .bounded_backbone_zero_decompose_backoff_enabled,
            hbr_lits: Vec::with_capacity(32),
            probe_parent: vec![None; num_vars],
            var_lifecycle: self.var_lifecycle.clone(),
            lit_marks: self.lit_marks.clone(),
            subsume_dirty: self.subsume_dirty.clone(),
            l0_gc_dirty: self.l0_gc_dirty.clone(),
            dirty_watches: vec![false; num_vars * 2],
            dirty_watch_list: Vec::new(),
            gc_occ: None,         // Rebuilt on demand
            gc_occ_scratch: None, // Scratch allocation, rebuilt on demand
            inproc_ctrl: self.inproc_ctrl.clone(),
            inproc_ctrl_pre_proof: self.inproc_ctrl_pre_proof.clone(),
            preprocessing_quick_mode: self.preprocessing_quick_mode,
            // Re-initialize inprocessing engines fresh (cold state,
            // not needed for IC3 short queries).
            inproc: inproc_engines::InprocessingEngines::new(num_vars),

            // ── JIT: reset all (not transferable between solvers) ────
            #[cfg(feature = "jit")]
            jit_conflict_processor: None,
            #[cfg(feature = "jit")]
            jit_conflict_output: ay_jit::conflict_jit::ConflictProcessorOutput::new(num_vars),

            // ── COLD: boxed restart/proof/incremental/tracing state ──
            cold,
            provenance: self.provenance.clone(),
            dip: self.dip.clone(),
            active_domain: self.active_domain.clone(),
            decision_domain: self.decision_domain.clone(),
            bucket_queue_active: self.bucket_queue_active,
            domain_restarts: self.domain_restarts,
            relevancy_branching: self.relevancy_branching,
            relevancy_buf: Vec::new(),
            relevancy_decisions: self.relevancy_decisions,
            relevancy_hard: self.relevancy_hard,
            wander_abort_armed: false,
            wander_abort_tripped: false,
            wander_abort_base_conflicts: 0,
            wander_abort_base_decisions: 0,
        }
    }
}

impl cold::ColdState {
    /// Clone cold state for incremental solver cloning (#8432).
    ///
    /// Deep-copies scheduling and search state. Resets non-clonable
    /// fields (tracing, proof, forward checker, observer, interrupt).
    pub(super) fn clone_for_incremental(&self, num_vars: usize) -> Self {
        #[cfg(not(all(debug_assertions, feature = "jit")))]
        let _ = num_vars;

        Self {
            // Restart EMA state
            lbd_ema_fast: self.lbd_ema_fast,
            theory_continue_polls: 0,
            lbd_ema_slow: self.lbd_ema_slow,
            lbd_ema_fast_biased: self.lbd_ema_fast_biased,
            lbd_ema_slow_biased: self.lbd_ema_slow_biased,
            lbd_ema_fast_exp: self.lbd_ema_fast_exp,
            lbd_ema_slow_exp: self.lbd_ema_slow_exp,
            saved_lbd_ema_fast: self.saved_lbd_ema_fast,
            saved_lbd_ema_slow: self.saved_lbd_ema_slow,
            saved_lbd_ema_fast_biased: self.saved_lbd_ema_fast_biased,
            saved_lbd_ema_slow_biased: self.saved_lbd_ema_slow_biased,
            saved_lbd_ema_fast_exp: self.saved_lbd_ema_fast_exp,
            saved_lbd_ema_slow_exp: self.saved_lbd_ema_slow_exp,
            ema_swapped: self.ema_swapped,
            glucose_restarts: self.glucose_restarts,
            theory_conflict_ratio: self.theory_conflict_ratio,
            ext_conflict_count: self.ext_conflict_count,
            trail_ema_slow: self.trail_ema_slow,
            trail_ema_count: self.trail_ema_count,
            consecutive_ema_restarts: self.consecutive_ema_restarts,
            geometric_restarts: self.geometric_restarts,
            geometric_initial: self.geometric_initial,
            geometric_factor: self.geometric_factor,
            restart_min_conflicts: self.restart_min_conflicts,
            stable_ema_gate: self.stable_ema_gate,
            focused_restart_gate: self.focused_restart_gate,
            dense_mutex_focused_restart_gate_experiment: self
                .dense_mutex_focused_restart_gate_experiment,
            luby_idx: self.luby_idx,
            theory_luby_idx: self.theory_luby_idx,
            restart_base: self.restart_base,
            restarts: self.restarts,
            stable_mode_start_conflicts: self.stable_mode_start_conflicts,
            stable_phase_init: self.stable_phase_init,
            stable_phase_length: self.stable_phase_length,
            stable_phase_count: self.stable_phase_count,
            mode_switch_count: self.mode_switch_count,
            mode_lock: self.mode_lock,
            probe_ticks: self.probe_ticks,
            vivify_ticks: self.vivify_ticks,
            stabilize_tick_inc: self.stabilize_tick_inc,
            focused_ticks_at_entry: self.focused_ticks_at_entry,
            mode_equiticks_cached: self.mode_equiticks_cached,
            branch_selector_mode: self.branch_selector_mode,
            branch_mab: self.branch_mab.clone(),
            stabilize_tick_limit: self.stabilize_tick_limit,
            last_target_improve_conflicts: self.last_target_improve_conflicts,
            stable_tick_hardcap: self.stable_tick_hardcap,
            eqt_progress_cached: self.eqt_progress_cached,
            reluctant_u: self.reluctant_u,
            reluctant_v: self.reluctant_v,
            reluctant_countdown: self.reluctant_countdown,
            reluctant_ticked_at: self.reluctant_ticked_at,

            // Reduction scheduling
            next_reduce_db: self.next_reduce_db,
            num_reductions: self.num_reductions,
            original_clause_boundary: self.original_clause_boundary,
            last_inprobe_reduction: self.last_inprobe_reduction,
            next_inprobe_conflict: self.next_inprobe_conflict,
            incremental_inprobe_clause_divisor: self.incremental_inprobe_clause_divisor,
            inprobe_phases: self.inprobe_phases,
            uniform_formula_cache: self.uniform_formula_cache,
            learned_clause_trail: self.learned_clause_trail.clone(),
            num_eager_subsumptions: self.num_eager_subsumptions,
            next_flush: self.next_flush,
            flush_inc: self.flush_inc,
            num_flushes: self.num_flushes,
            num_arena_compactions: self.num_arena_compactions,
            num_arena_compaction_skips: self.num_arena_compaction_skips,
            factor_skip_counts: self.factor_skip_counts,
            arena_compaction_pending: self.arena_compaction_pending,
            scoped_clauses_reclaimed: self.scoped_clauses_reclaimed,
            eager_subsumed: self.eager_subsumed,
            max_learned_clauses: self.max_learned_clauses,
            max_clause_db_bytes: self.max_clause_db_bytes,
            conflict_budget: self.conflict_budget,
            decision_budget: self.decision_budget,
            bumpreason_saved_decisions: self.bumpreason_saved_decisions,
            bumpreason_decision_rate: self.bumpreason_decision_rate,
            bumpreason_delay_remaining: self.bumpreason_delay_remaining,
            bumpreason_delay_interval: self.bumpreason_delay_interval,
            last_vivify_ticks: self.last_vivify_ticks,
            last_vivify_irred_ticks: self.last_vivify_irred_ticks,
            vivify_irred_delay_multiplier: self.vivify_irred_delay_multiplier,

            // Random decisions
            randomized_deciding: 0,
            random_decision_phases: self.random_decision_phases,
            next_random_decision: self.next_random_decision,
            random_var_freq: self.random_var_freq,

            // BVE state
            bve_effort_permille: self.bve_effort_permille,
            subsume_effort_permille: self.subsume_effort_permille,
            bve_phases: self.bve_phases,
            subsume_ran_since_bve: self.subsume_ran_since_bve,
            last_bve_fixed: self.last_bve_fixed,
            bve_marked: self.bve_marked,
            last_bve_marked: self.last_bve_marked,
            last_bve_clauses: self.last_bve_clauses,
            last_collect_fixed: self.last_collect_fixed,
            last_collect_trail_pos: self.last_collect_trail_pos,
            last_full_l0_gc_fixed: self.last_full_l0_gc_fixed,
            clause_db_changes: self.clause_db_changes,
            bve_resolutions: self.bve_resolutions,
            first_extension_var_index: self.first_extension_var_index,
            er_proof_log: self.er_proof_log.clone(),

            // Factorization state
            factor_rounds: self.factor_rounds,
            factor_factored_total: self.factor_factored_total,
            factor_extension_vars_total: self.factor_extension_vars_total,
            factor_candidate_marks: self.factor_candidate_marks.clone(),
            factor_marked_epoch: self.factor_marked_epoch,
            factor_last_completed_epoch: self.factor_last_completed_epoch,
            last_factor_ticks: self.last_factor_ticks,

            // SBVA state
            sbva_rounds: self.sbva_rounds,
            sbva_groups_total: self.sbva_groups_total,
            sbva_extension_vars_total: self.sbva_extension_vars_total,
            last_sbva_ticks: self.last_sbva_ticks,

            // Tick scheduling
            last_sweep_ticks: self.last_sweep_ticks,
            last_backbone_ticks: self.last_backbone_ticks,
            last_probe_ticks: self.last_probe_ticks,
            last_subsume_ticks: self.last_subsume_ticks,
            last_bve_ticks: self.last_bve_ticks,
            bve_consecutive_unproductive: self.bve_consecutive_unproductive,
            last_transred_ticks: self.last_transred_ticks,
            last_bce_ticks: self.last_bce_ticks,
            backbone_phases: self.backbone_phases,
            backbone_post_vivify_binary_admission: self.backbone_post_vivify_binary_admission,
            backbone_consecutive_empty: self.backbone_consecutive_empty,
            next_bounded_backbone_conflict: self.next_bounded_backbone_conflict,
            htr_consecutive_empty: self.htr_consecutive_empty,
            component_stats: self.component_stats.clone(),
            intree_rounds: self.intree_rounds,
            intree_failed: self.intree_failed,
            intree_vars_set: self.intree_vars_set,
            last_inprocessing_overhead_ms: self.last_inprocessing_overhead_ms,
            post_rebuild_props_baseline: 0,
            post_rebuild_bcp_pending: false,
            post_rebuild_is_full: false,
            instantiate_rebuilt_watches: false,
            disconnected_deletions: 0,
            last_round_simplifications: self.last_round_simplifications,
            consecutive_low_productivity_rounds: self.consecutive_low_productivity_rounds,

            // Variable mapping
            eliminated_ext_vals: self.eliminated_ext_vals.clone(),
            e2i: self.e2i.clone(),
            i2e: self.i2e.clone(),
            compact_next_conflict: self.compact_next_conflict,
            compact_count: self.compact_count,
            freeze_counts: self.freeze_counts.clone(),

            // LRAT/proof state (copied for clause ID consistency)
            clause_ids: self.clause_ids.clone(),
            clause_ids_disabled: self.clause_ids_disabled,
            bcp_learned_clause_birth_conflicts: self.bcp_learned_clause_birth_conflicts.clone(),
            clause_birth_solve: self.clause_birth_solve.clone(),
            level0_proof_id: self.level0_proof_id.clone(),
            level0_proof_sign: self.level0_proof_sign.clone(),
            lrat_level0_unit_materialize_cursor: 0,
            proof_bookkeeping_budget: None,
            next_clause_id: self.next_clause_id,
            next_original_clause_id: self.next_original_clause_id,
            lrat_enabled: false, // No LRAT in cloned solver
            unsat_certificate_enabled: self.unsat_certificate_enabled,
            ambient_artifacts_enabled: self.ambient_artifacts_enabled,
            retain_unsat_certificate: self.retain_unsat_certificate,
            backward_proof_limits: self.backward_proof_limits.clone(),
            backward_proof_failure: None,
            dense_factor_bve_lrat_route_enabled: false,
            circuit_bve_lrat_route_enabled: false,
            bve_lrat_scout_route_enabled: false,
            fmla_decompose_lrat_preflight_route_enabled: false,
            fmla_decompose_lrat_preflight_route_consumed: true,
            jump_reasons_enabled: self.jump_reasons_enabled,
            empty_clause_in_proof: false,
            empty_clause_lrat_id: None,
            empty_clause_scope_depth: 0,
            clause_trace: None, // Not cloned — no SMT proof in clone

            // Incremental scope state
            scope_selectors: self.scope_selectors.clone(),
            scope_var_starts: self.scope_var_starts.clone(),
            scope_reconstruction_starts: self.scope_reconstruction_starts.clone(),
            #[cfg(debug_assertions)]
            scope_selector_axiom_ids: self.scope_selector_axiom_ids.clone(),
            has_been_incremental: self.has_been_incremental,
            symmetry_oneshot: self.symmetry_oneshot,
            tainted_vars: self.tainted_vars.clone(),
            has_ever_scoped: self.has_ever_scoped,
            has_solved_once: self.has_solved_once,
            constraint: Vec::new(), // Constraints are per-solve
            unsat_constraint: false,

            // JIT cold state (reset)
            #[cfg(feature = "jit")]
            code_cache: ay_jit::CodeCacheManager::with_default_budget(),
            jit_disabled: self.jit_disabled,

            // Incremental lifetime counters
            lifetime_conflicts: self.lifetime_conflicts,
            lifetime_decisions: self.lifetime_decisions,
            lifetime_propagations: self.lifetime_propagations,
            lifetime_restarts: self.lifetime_restarts,
            incremental_solve_count: self.incremental_solve_count,
            active_assumption_count: 0, // per-solve state, reset in clone
            last_between_solve_reduce_conflicts: self.last_between_solve_reduce_conflicts,

            // Lazy theory reasons (per-solve, reset)
            lazy_theory_reasons: Vec::new(),
            lazy_theory_propagated: Vec::new(),
            lazy_materialization_failed: false,
            extension_trusted_lemmas: self.extension_trusted_lemmas,

            // Streaming core (per-solve, reset)
            streaming_core: None,
            streaming_core_num_originals: 0,
            scope_selector_set: self.scope_selector_set.clone(),
            was_scope_selector: self.was_scope_selector.clone(),
            root_satisfied_saved: Vec::new(),
            inprocessing_modified_clause_db: self.inprocessing_modified_clause_db,
            l0_gc_modified_clause_db: self.l0_gc_modified_clause_db,

            // Lookahead
            last_lookahead_conflict: self.last_lookahead_conflict,
            next_lookahead_conflict: self.next_lookahead_conflict,
            lookahead_decision: None,

            // Phase hints and rephasing
            forced_phase: self.forced_phase.clone(),
            rephase_enabled: self.rephase_enabled,
            rephase_count: self.rephase_count,
            rephase_count_stable: self.rephase_count_stable,
            rephase_count_focused: self.rephase_count_focused,
            next_rephase: self.next_rephase,
            stable_only_rephase_enabled: self.stable_only_rephase_enabled,
            flip_search_enabled: self.flip_search_enabled,
            flip_last_ticks: self.flip_last_ticks,
            flip_stats: self.flip_stats.clone(),
            cold_restart_count: self.cold_restart_count,
            cold_restart_last_conflict: self.cold_restart_last_conflict,
            cold_restart_enabled: self.cold_restart_enabled,
            cold_restart_fo_enabled: self.cold_restart_fo_enabled,
            cold_restart_fp_enabled: self.cold_restart_fp_enabled,

            // Preprocessing
            preprocess_enabled: self.preprocess_enabled,
            preprocess_watches_valid: self.preprocess_watches_valid,
            preprocess_deadline: None,
            solve_deadline: None,
            incremental_watch_boundary: self.incremental_watch_boundary,
            symmetry_enabled: self.symmetry_enabled,
            symmetry_stats: self.symmetry_stats.clone(),

            // Tracing (NOT cloned — these own file handles / writers)
            tla_trace: None,
            diagnostic_trace: None,
            decision_trace: None,
            replay_trace: None,
            diagnostic_pass: DiagnosticPass::None,
            solution_witness: None,
            bcp_lean_route_enabled: self.bcp_lean_route_enabled,
            forward_checker: None, // Not cloned — proof verification

            // Diagnostics
            last_unknown_reason: None,
            last_unknown_detail: None,
            finalize_sat_fail_count: 0,
            // Soundness poison MUST survive incremental cloning: dropping it
            // would let a clone derive an unsound UNSAT from a truncated
            // clause (#oversized).
            oversized_clause_poison: self.oversized_clause_poison,

            // Runtime: the cooperative-cancellation handle IS preserved across an
            // incremental clone. A child solver spawned for an incremental query
            // (e.g. the core-guided / OLL loop clones the base solver per query)
            // must honor the same timeout/interrupt as its parent; otherwise a
            // long inprocessing pass on the clone runs unbounded past the deadline
            // (the closure-based `should_stop` is only threaded into the CDCL main
            // loop, not inprocessing). The handle is a cheap `Arc` clone.
            interrupt: self.interrupt.clone(),
            process_memory_interrupt: false,
            process_memory_interrupt_pending: false,
            backbone_binary_cursor: 0,
            process_memory_armed_at: None,
            trace_ext_conflict: self.trace_ext_conflict,
            bve_limit: self.bve_limit,
            bve_trace: self.bve_trace,
            elimfast_disabled: self.elimfast_disabled,
            sparse_band_bve_preprocess_unlock: self.sparse_band_bve_preprocess_unlock,
            // Giant raw-BVE unlock (lever 3): the route flag is config-derived
            // and travels with the clone; the qualification latch and the
            // lever-2 instantiate phase stamps are per-solve scheduling state
            // and reset like the other transient BVE bookkeeping.
            bve_giant_raw_unlock: self.bve_giant_raw_unlock,
            bve_giant_raw_qualified: false,
            // Post-factor BVE reopen (opt-in): the pre-factor latches and the
            // qualification flag are per-solve scheduling state, reset on clone
            // like the other transient BVE bookkeeping above.
            pre_factor_active_clauses: 0,
            pre_factor_num_vars: 0,
            bve_post_factor_qualified: false,
            bve_elim_phase_seq: 0,
            bve_instantiate_done_seq: u64::MAX,
            subst_auto_collapse: self.subst_auto_collapse,
            subst_auto_capped: self.subst_auto_capped,
            subst_auto_giant: self.subst_auto_giant,
            bcp_telemetry_enabled: self.bcp_telemetry_enabled,
            bcp_trail_lookahead_prefetch: self.bcp_trail_lookahead_prefetch,
            bcp_search_inplace_watch_scan: self.bcp_search_inplace_watch_scan,
            bcp_advance_saved_pos_after_unassigned_move: self
                .bcp_advance_saved_pos_after_unassigned_move,
            bcp_learned_1963_false_saved_pos_reset: self.bcp_learned_1963_false_saved_pos_reset,
            bcp_learned_1963_true_tail_relocation: self.bcp_learned_1963_true_tail_relocation,
            bcp_learned_1963_used5_fsw_saved_pos_reset: self
                .bcp_learned_1963_used5_fsw_saved_pos_reset,
            bcp_learned_1963_fsw_conflict_saved_pos_reset: self
                .bcp_learned_1963_fsw_conflict_saved_pos_reset,
            bcp_learned_618_true_tail_relocation: self.bcp_learned_618_true_tail_relocation,
            bcp_learned_no_replacement_saved_pos_update: self
                .bcp_learned_no_replacement_saved_pos_update,
            bcp_learned_1963_fsw_gent_skip: self.bcp_learned_1963_fsw_gent_skip,
            bcp_learned_no_replacement_scan_pressure: self.bcp_learned_no_replacement_scan_pressure,
            bcp_learned_1963_identity_profile: self.bcp_learned_1963_identity_profile,
            bcp_learned_1963_pressure_reduction: self.bcp_learned_1963_pressure_reduction,
            bcp_learned_1963_pressure_retention: self.bcp_learned_1963_pressure_retention,
            bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: self
                .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh,
            bcp_learned_617_tail_reorder: self.bcp_learned_617_tail_reorder,
            bcp_learned_18_tail_reorder: self.bcp_learned_18_tail_reorder,
            bcp_learned_1963_tail_reorder: self.bcp_learned_1963_tail_reorder,
            bcp_learned_1963_tail_reorder_swap_budget: self
                .bcp_learned_1963_tail_reorder_swap_budget,
            progress_enabled: false,
            observer: None,                  // Not cloneable (Box<dyn>)
            portfolio_clause_exporter: None, // Not cloneable (Box<dyn>)
            portfolio_clause_importer: None, // Not cloneable (Box<dyn>)
            sat_comp_main_conflict_pruning: self.sat_comp_main_conflict_pruning,
            last_progress_time: None,
            solve_start_time: None,
            #[cfg(ay_logging)]
            log_enabled: self.log_enabled,
            original_ledger: self.original_ledger.clone(),
            incremental_original_boundary: self.incremental_original_boundary,

            // IC3 assumption cache (#8443): reset in clone — the clone
            // starts with no cached assumption state.
            prev_assumptions: Vec::new(),
            assumption_cache_valid: false,
            assumption_cache_trail_len: 0,
            ic3_new_clauses_pending: false,
            ic3_mode: self.ic3_mode,
            inc_engine_reset_mode: self.inc_engine_reset_mode,
            unguarded_theory_conflict_lemmas: self.unguarded_theory_conflict_lemmas,
            domain_bcp_min_vars: self.domain_bcp_min_vars,
            ic3_constrain_act: self.ic3_constrain_act,
            ic3_constrained_offsets: Vec::new(),

            // Persistent IC3 assumption tracking buffers (#8569 Gap 1):
            // start empty in clone, lazily grown on first IC3 query.
            ic3_is_assumption: Vec::new(),
            ic3_assumption_lit: Vec::new(),
            ic3_assumption_indices: Vec::new(),
            ic3_domain_bitmap_buf: Vec::new(),
            ic3_domain_set_indices: Vec::new(),
            ic3_domain_cache_boundary: 0,
            ic3_domain_cache_expanded: Vec::new(),
            ic3_domain_cache_hash: 0,
            ic3_baseline_arena_words: self.ic3_baseline_arena_words,

            // Persistent reusable buffers (#8602): start empty in clone,
            // will be lazily grown on first use.
            reduce_indices_buf: Vec::new(),
            reduce_candidates_buf: Vec::new(),
            gc_seen_buf: Vec::new(),
            lrat_level0_vars_buf: Vec::new(),
            proof_mirrored_units: Vec::new(),
            lrat_delete_unit_hints_buf: Vec::new(),
            lrat_materialize_hints_buf: Vec::new(),
            bve_body_scratch: Default::default(),
            #[cfg(all(debug_assertions, feature = "jit"))]
            debug_jit_flags_buf: Vec::new(),
            #[cfg(all(debug_assertions, feature = "jit"))]
            debug_interp_output: ay_jit::conflict_jit::ConflictProcessorOutput::new(num_vars),

            #[cfg(debug_assertions)]
            pending_forward_check: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that cloning a solver mid-solve produces two independent
    /// solvers that both yield correct results.
    #[test]
    fn test_clone_for_incremental_basic() {
        // Build a satisfiable formula: (x1 OR x2) AND (NOT x1 OR x3)
        let mut solver = Solver::new(3);
        let x1 = Literal::positive(Variable(0));
        let x2 = Literal::positive(Variable(1));
        let x3 = Literal::positive(Variable(2));
        let not_x1 = Literal::negative(Variable(0));

        solver.add_clause(vec![x1, x2]);
        solver.add_clause(vec![not_x1, x3]);

        // Clone before solving
        let mut clone = solver.clone_for_incremental();

        // Both should produce SAT
        let result_original = solver.solve();
        let result_clone = clone.solve();

        assert!(result_original.is_sat(), "original solver should be SAT");
        assert!(result_clone.is_sat(), "cloned solver should be SAT");
    }

    #[test]
    fn test_clone_preserves_stable_phase_init_8140() {
        let mut solver = Solver::new(3);
        solver.set_stable_phase_init(4096);
        solver.cold.stable_phase_length = 123;

        let mut clone = solver.clone_for_incremental();
        clone.reset_search_state();

        assert_eq!(clone.cold.stable_phase_length, 4096);
    }

    /// Test that the clone is independent: adding clauses to one
    /// does not affect the other.
    #[test]
    fn test_clone_independence() {
        let mut solver = Solver::new(2);
        let x1 = Literal::positive(Variable(0));
        let x2 = Literal::positive(Variable(1));
        let not_x1 = Literal::negative(Variable(0));
        let not_x2 = Literal::negative(Variable(1));

        // Add satisfiable clause
        solver.add_clause(vec![x1, x2]);

        // Clone
        let mut clone = solver.clone_for_incremental();

        // Make original UNSAT by adding contradictory unit clauses
        solver.add_clause(vec![not_x1]);
        solver.add_clause(vec![not_x2]);

        let result_original = solver.solve();
        let result_clone = clone.solve();

        assert!(
            result_original.is_unsat(),
            "original should be UNSAT after adding contradictory clauses"
        );
        assert!(
            result_clone.is_sat(),
            "clone should still be SAT (not affected by original's new clauses)"
        );
    }

    /// Test cloning preserves learned clause state.
    #[test]
    fn test_clone_preserves_learned_clauses() {
        // Create a satisfiable formula with enough structure that the solver
        // learns clauses during the first solve. Use 6 variables with a mix
        // of positive and negative clauses that force backtracking.
        let mut solver = Solver::new(6);
        let x: Vec<_> = (0..6).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..6).map(|i| Literal::negative(Variable(i))).collect();

        // Implication chains that force conflicts and learning:
        // x0 => x1 (i.e., ~x0 OR x1)
        solver.add_clause(vec![nx[0], x[1]]);
        // x1 => x2
        solver.add_clause(vec![nx[1], x[2]]);
        // x2 => x3
        solver.add_clause(vec![nx[2], x[3]]);
        // ~x3 OR ~x0 OR x4 (creates a conflict path with x0..x3 chain)
        solver.add_clause(vec![nx[3], nx[0], x[4]]);
        // x0 OR x5 (ensures satisfiability: x0=F, x5=T is always an escape)
        solver.add_clause(vec![x[0], x[5]]);
        // ~x4 OR x5 (propagation chain)
        solver.add_clause(vec![nx[4], x[5]]);
        // At least one of x0, x1 must be true
        solver.add_clause(vec![x[0], x[1]]);

        // Solve first to generate learned clauses
        let result1 = solver.solve();
        assert!(result1.is_sat(), "first solve should be SAT");

        // Clone after solving (should preserve learned clauses)
        let clone = solver.clone_for_incremental();

        // The clone should have the same num_vars
        assert_eq!(clone.num_vars, solver.num_vars);

        // The clone's arena should contain the same clauses
        // (We can't directly compare arenas, but we can verify solve correctness)
        let mut clone2 = clone;
        let result2 = clone2.solve();
        assert!(result2.is_sat(), "cloned solver should also be SAT");
    }

    /// Test that cloning an UNSAT solver preserves the UNSAT state.
    #[test]
    fn test_clone_unsat_formula() {
        let mut solver = Solver::new(1);
        let x = Literal::positive(Variable(0));
        let not_x = Literal::negative(Variable(0));

        solver.add_clause(vec![x]);
        solver.add_clause(vec![not_x]);

        // Solve to establish UNSAT
        let result = solver.solve();
        assert!(result.is_unsat(), "should be UNSAT");

        // Clone the UNSAT solver
        let mut clone = solver.clone_for_incremental();
        let result_clone = clone.solve();
        assert!(
            result_clone.is_unsat(),
            "cloned UNSAT solver should remain UNSAT"
        );
    }

    /// Test cloning with assumptions works correctly.
    #[test]
    fn test_clone_with_assumptions() {
        let mut solver = Solver::new(3);
        let x1 = Literal::positive(Variable(0));
        let x2 = Literal::positive(Variable(1));
        let x3 = Literal::positive(Variable(2));
        let not_x1 = Literal::negative(Variable(0));

        // (x1 OR x2) AND (NOT x1 OR x3) — satisfiable
        solver.add_clause(vec![x1, x2]);
        solver.add_clause(vec![not_x1, x3]);

        let mut clone = solver.clone_for_incremental();

        // Solve with assumptions on clone
        let result = clone.solve_with_assumptions(&[not_x1]);
        assert!(
            result.is_sat(),
            "clone with assumption NOT x1 should be SAT (x2=true, x3 free)"
        );
    }

    // ── IC3-specific clone tests (#8432) ────────────────────────────

    /// Test that clone_for_ic3 preserves VSIDS activity scores.
    #[test]
    fn test_ic3_clone_preserves_vsids_activities() {
        let mut solver = Solver::new(4);
        let x: Vec<_> = (0..4).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..4).map(|i| Literal::negative(Variable(i))).collect();

        // Create a formula that generates conflicts to build VSIDS scores.
        // x0 => x1, x1 => x2, x2 => ~x3, x3 required.
        solver.add_clause(vec![nx[0], x[1]]);
        solver.add_clause(vec![nx[1], x[2]]);
        solver.add_clause(vec![nx[2], nx[3]]);
        solver.add_clause(vec![x[0], x[3]]);
        solver.add_clause(vec![x[3], x[2]]);

        solver.set_ic3_mode();

        // Solve to build up VSIDS activities from conflict analysis.
        let _ = solver.solve();

        // Record activities before cloning.
        let activities_before: Vec<f64> =
            (0..4).map(|i| solver.vsids.activity(Variable(i))).collect();

        let clone = solver.clone_for_ic3();

        // Verify activities are preserved in the clone.
        for (i, &orig) in activities_before.iter().enumerate() {
            let cloned = clone.vsids.activity(Variable(i as u32));
            assert!(
                (orig - cloned).abs() < f64::EPSILON,
                "VSIDS activity for var {i} differs: original={orig}, clone={cloned}"
            );
        }
    }

    /// Test that clone_for_ic3 preserves IC3 lemma protection bits.
    #[test]
    fn test_ic3_clone_preserves_lemma_bits() {
        let mut solver = Solver::new(4);
        let x: Vec<_> = (0..4).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..4).map(|i| Literal::negative(Variable(i))).collect();

        // Base formula.
        solver.add_clause(vec![x[0], x[1]]);
        solver.add_clause(vec![nx[0], x[2]]);

        solver.set_ic3_mode();

        // Add an IC3 lemma (blocking clause). This clause gets the
        // IC3_LEMMA_BIT flag set in the arena header.
        solver.add_ic3_lemma(vec![nx[1], x[3]]);

        // Count IC3 lemmas in original.
        let original_ic3_count = solver
            .arena
            .active_indices()
            .filter(|&idx| solver.arena.is_ic3_lemma(idx))
            .count();
        assert!(
            original_ic3_count > 0,
            "original should have at least one IC3 lemma"
        );

        // Clone for IC3.
        let clone = solver.clone_for_ic3();

        // Count IC3 lemmas in clone — should match original.
        let clone_ic3_count = clone
            .arena
            .active_indices()
            .filter(|&idx| clone.arena.is_ic3_lemma(idx))
            .count();
        assert_eq!(
            original_ic3_count, clone_ic3_count,
            "clone should preserve IC3 lemma count: original={original_ic3_count}, clone={clone_ic3_count}"
        );
    }

    /// Test that clone_for_ic3 produces a clean search state at level 0.
    #[test]
    fn test_ic3_clone_clean_state() {
        let mut solver = Solver::new(4);
        let x: Vec<_> = (0..4).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..4).map(|i| Literal::negative(Variable(i))).collect();

        solver.add_clause(vec![x[0], x[1]]);
        solver.add_clause(vec![nx[0], x[2]]);
        solver.add_clause(vec![x[2], x[3]]);
        solver.add_clause(vec![nx[2], nx[3], x[0]]);

        solver.set_ic3_mode();

        // Solve to build up search state (trail, decisions, etc.).
        let _ = solver.solve();

        let clone = solver.clone_for_ic3();

        // Clone should be at decision level 0.
        assert_eq!(
            clone.decision_level, 0,
            "clone should be at decision level 0"
        );

        // Clone trail_lim should be empty (no decisions).
        assert!(
            clone.trail_lim.is_empty(),
            "clone should have empty trail_lim (no decisions above level 0)"
        );

        // Clone conflict/decision counters should be reset.
        assert_eq!(clone.num_conflicts, 0, "clone conflicts should be 0");
        assert_eq!(clone.num_decisions, 0, "clone decisions should be 0");

        // IC3 mode should be active.
        assert!(clone.cold.ic3_mode, "clone should have IC3 mode active");
    }

    /// Test that clone_for_ic3 is independent: modifying the clone's
    /// clause database does not affect the original.
    #[test]
    fn test_ic3_clone_independence() {
        let mut solver = Solver::new(3);
        let x: Vec<_> = (0..3).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..3).map(|i| Literal::negative(Variable(i))).collect();

        solver.add_clause(vec![x[0], x[1]]);
        solver.add_clause(vec![nx[0], x[2]]);

        solver.set_ic3_mode();

        let mut clone = solver.clone_for_ic3();

        // Count original arena clauses.
        let original_count_before = solver.arena.active_indices().count();

        // Add IC3 lemma to clone only.
        clone.add_ic3_lemma(vec![nx[1], nx[2]]);

        // Make clone UNSAT by adding contradictory unit clauses.
        clone.add_clause(vec![nx[0]]);
        clone.add_clause(vec![nx[1]]);
        clone.add_clause(vec![nx[2]]);

        // Original clause count should be unchanged.
        let original_count_after = solver.arena.active_indices().count();
        assert_eq!(
            original_count_before, original_count_after,
            "original arena should not change when clone is modified"
        );

        // Original should still be SAT.
        let result_original = solver.solve();
        assert!(result_original.is_sat(), "original should still be SAT");

        // Clone should be UNSAT.
        let result_clone = clone.solve();
        assert!(
            result_clone.is_unsat(),
            "clone should be UNSAT after adding contradictions"
        );
    }

    /// Test that clone_for_ic3 can solve after cloning.
    #[test]
    fn test_ic3_clone_can_solve() {
        let mut solver = Solver::new(5);
        let x: Vec<_> = (0..5).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..5).map(|i| Literal::negative(Variable(i))).collect();

        // A formula encoding a simple transition system.
        // State: x0, x1. Next-state: x2, x3. Constraint: x4.
        solver.add_clause(vec![x[0], x[1]]); // initial state
        solver.add_clause(vec![nx[0], x[2]]); // transition: x0 => x2
        solver.add_clause(vec![nx[1], x[3]]); // transition: x1 => x3
        solver.add_clause(vec![x[4], nx[2]]); // constraint

        solver.set_ic3_mode();

        // Solve with the original.
        let result1 = solver.solve();
        assert!(result1.is_sat(), "original should be SAT");

        // Clone for IC3 frame reuse.
        let mut clone = solver.clone_for_ic3();

        // Add a blocking clause (IC3 lemma) to the clone.
        clone.add_ic3_lemma(vec![nx[0], x[1]]);

        // Solve the clone with assumptions (IC3 query pattern).
        let result2 = clone.solve_with_assumptions(&[x[0]]);
        assert!(
            result2.is_sat(),
            "clone should be SAT with assumption x0 (x1 forced by lemma)"
        );

        // Another query with different assumptions.
        let result3 = clone.solve_with_assumptions(&[nx[0], nx[1]]);
        // (nx[0], nx[1]) contradicts (x[0] | x[1]), should be UNSAT.
        assert!(
            result3.is_unsat(),
            "clone should be UNSAT with contradictory assumptions"
        );
    }

    /// Test that clone_for_ic3 preserves IC3 mode and constraint activation.
    #[test]
    fn test_ic3_clone_preserves_ic3_config() {
        let mut solver = Solver::new(4);
        let x: Vec<_> = (0..4).map(|i| Literal::positive(Variable(i))).collect();

        solver.add_clause(vec![x[0], x[1]]);

        solver.set_ic3_mode();
        // Use variable 3 as constraint activation variable.
        solver.set_constrain_activation(Variable(3));

        let clone = solver.clone_for_ic3();

        assert!(clone.is_ic3_mode(), "clone should be in IC3 mode");
        assert_eq!(
            clone.constrain_activation(),
            Some(Variable(3)),
            "clone should preserve constraint activation variable"
        );
    }

    /// Regression evidence for #8432: an IC3 clone carries the reuse metadata
    /// that frame-level solver forking needs, while still starting from a clean
    /// search state.
    #[test]
    fn test_ic3_clone_preserves_reuse_metadata() {
        let mut solver = Solver::new(4);
        let x: Vec<_> = (0..4).map(|i| Literal::positive(Variable(i))).collect();
        let nx: Vec<_> = (0..4).map(|i| Literal::negative(Variable(i))).collect();

        solver.add_clause(vec![x[0], x[1]]);
        solver.add_clause(vec![nx[1], x[2]]);
        assert!(solver.add_preserved_learned(vec![nx[0], x[1], x[2]]));
        assert_eq!(
            solver.num_learned_clauses(),
            1,
            "test setup should install one trusted learned clause"
        );

        solver.set_ic3_mode();
        solver.set_var_phase(Variable(0), true);
        solver.set_var_phase(Variable(1), false);
        solver.set_phase(Variable(2), false);
        solver.target_phase[0] = -1;
        solver.target_phase[1] = 1;
        solver.best_phase[2] = 1;
        solver.best_phase[3] = -1;
        solver.target_trail_len = 2;
        solver.best_trail_len = 3;
        solver.stats.bcp_binary_path_hits = 7;
        solver.stats.lbd_sum = 11;
        solver.stats.lbd_count = 3;
        solver.stats.assumption_cache_hits = 5;
        solver.stats.assumption_cache_levels_reused = 8;
        solver.num_conflicts = 13;
        solver.num_decisions = 21;

        let saved_phase = solver.phase[..4].to_vec();
        let target_phase = solver.target_phase[..4].to_vec();
        let best_phase = solver.best_phase[..4].to_vec();
        let learned_before = solver.num_learned_clauses();

        let mut clone = solver.clone_for_ic3();

        assert_eq!(
            clone.num_learned_clauses(),
            learned_before,
            "clone should retain trusted learned clauses for frame reuse"
        );
        assert_eq!(
            &clone.phase[..4],
            saved_phase.as_slice(),
            "clone should preserve saved phase hints"
        );
        assert_eq!(
            &clone.target_phase[..4],
            target_phase.as_slice(),
            "clone should preserve target phase hints"
        );
        assert_eq!(
            &clone.best_phase[..4],
            best_phase.as_slice(),
            "clone should preserve best phase hints"
        );
        assert_eq!(
            clone.cold.forced_phase[2], -1,
            "clone should preserve IC3 forced phase hints"
        );
        assert_eq!(clone.target_trail_len, 2);
        assert_eq!(clone.best_trail_len, 3);
        assert_eq!(clone.stats.bcp_binary_path_hits, 7);
        assert_eq!(clone.stats.lbd_sum, 11);
        assert_eq!(clone.stats.lbd_count, 3);
        assert_eq!(clone.stats.assumption_cache_hits, 5);
        assert_eq!(clone.stats.assumption_cache_levels_reused, 8);

        assert_eq!(
            clone.num_conflicts, 0,
            "IC3 clone should reset search conflict counters"
        );
        assert_eq!(
            clone.num_decisions, 0,
            "IC3 clone should reset search decision counters"
        );

        let result = clone.solve_with_assumptions(&[x[0], nx[1], nx[2]]);
        assert!(
            result.is_unsat(),
            "cloned trusted learned clause should participate in propagation"
        );
    }
}
