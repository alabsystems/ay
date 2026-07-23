// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver constructors: `new`, `with_proof`, `with_proof_output`, `build`.

use super::*;

impl Solver {
    /// Create a new solver with n variables (no proof logging)
    pub fn new(num_vars: usize) -> Self {
        Self::build(num_vars, None)
    }

    /// Create a new solver with DRAT proof logging (text format)
    pub fn with_proof(num_vars: usize, writer: impl Write + Send + 'static) -> Self {
        Self::with_proof_output(num_vars, ProofOutput::drat_text(writer))
    }

    /// Create a new solver with proof logging (DRAT or LRAT)
    ///
    /// For LRAT proofs, use `ProofOutput::lrat_text()` or `ProofOutput::lrat_binary()`.
    /// Note: LRAT proof requires knowing the number of original clauses, which is
    /// determined after all clauses are added. Construct a `ProofOutput::lrat_text()`
    /// or `ProofOutput::lrat_binary()` with an estimate of the clause count.
    pub fn with_proof_output(num_vars: usize, proof_output: ProofOutput) -> Self {
        Self::build(num_vars, Some(proof_output))
    }

    /// Shared constructor: all Solver initialization in one place.
    fn build(num_vars: usize, proof_output: Option<ProofOutput>) -> Self {
        let has_proof = proof_output.is_some();
        let lrat_enabled = proof_output.as_ref().is_some_and(ProofOutput::is_lrat);
        // Removed 100k cap for BV performance (#757) - BV CNF has ~3-5 clauses/var
        let clauses_capacity = num_vars.saturating_mul(4);
        let literals_capacity = clauses_capacity.saturating_mul(3); // avg 3 lits/clause
        #[allow(unused_mut)]
        let mut solver = Self {
            num_vars,
            user_num_vars: num_vars,
            arena: ClauseArena::with_capacity(clauses_capacity, literals_capacity),

            watches: WatchedLists::new(num_vars),
            watches_disconnected: false,
            defer_stale_reason_cleanup: false,
            defer_proof_deletions: false,
            deferred_proof_deletions: Vec::new(),
            earliest_affected_trail_pos: None,
            stale_reasons: Vec::new(),
            vsids: VSIDS::new(num_vars),
            conflict: ConflictAnalyzer::new(num_vars),
            vals: vec![0i8; num_vars * 2],
            var_data: vec![VarData::UNASSIGNED; num_vars],
            // Always allocate unit_proof_id unconditionally (#8069: Phase 2a).
            // Clause IDs are always tracked for deferred backward proof
            // reconstruction, so unit proof IDs must also always be available.
            unit_proof_id: vec![0; num_vars],
            unit_proof_sign: vec![0; num_vars],
            pending_theory_unit_proof_ids: Vec::new(),
            // Pre-size to arena capacity for ensure_reason_clause_marks_current()
            // lazy rebuild (#8569). BCP no longer calls mark_reason_clause().
            // Arena word count = clauses * HEADER_WORDS + literals.
            reason_clause_marks: vec![
                0;
                clauses_capacity * crate::clause_arena::HEADER_WORDS
                    + literals_capacity
            ],
            reason_clause_epoch: 1,
            reason_marks_invalidated: false,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            qhead: 0,
            phase: vec![0i8; num_vars],
            target_phase: vec![0i8; num_vars],
            best_phase: vec![0i8; num_vars],
            target_trail_len: 0,
            best_trail_len: 0,
            no_conflict_until: 0,
            suppress_phase_saving: false,
            suppress_reduce_db: false,
            proof_manager: proof_output.map(|output| ProofManager::new(output, num_vars)),
            #[cfg(debug_assertions)]
            solve_proof_mode: None,
            conflicts_since_restart: 0,
            // Stabilization state (start in focused mode)
            stable_mode: false,
            active_branch_heuristic: BranchHeuristic::Vmtf,
            search_ticks: [0; 2],
            num_conflicts: 0,
            num_original_clauses: 0,
            chrono_enabled: true,
            // Ghost literal guard is only needed when chrono-BT can actually fire.
            // Chrono-BT fires when decision_level - jump_level > CHRONO_LEVEL_LIMIT.
            // This requires decision_level > CHRONO_LEVEL_LIMIT, which requires
            // num_vars > CHRONO_LEVEL_LIMIT (#8466).
            ghost_guard_needed: num_vars > CHRONO_LEVEL_LIMIT as usize,
            lambda: vec![None; num_vars],
            chrono_reuse_trail: true, // CaDiCaL-style trail reuse (re-enabled #112)
            stats: solver_stats::SolverStats::new(),
            num_decisions: 0,
            bump_order_sort_buf: Vec::new(),
            backbone_seen: vec![false; num_vars],
            vivify_analyzed: vec![false; num_vars],
            vivify_analyzed_to_clear: Vec::with_capacity(64),
            num_propagations: 0,
            pending_garbage_count: 0,
            inproc_ctrl: if has_proof {
                inproc_control::InprocessingControls::new().with_proof_overrides(lrat_enabled)
            } else {
                inproc_control::InprocessingControls::new()
            },
            inproc_ctrl_pre_proof: if has_proof {
                Some(inproc_control::InprocessingControls::new())
            } else {
                None
            },
            preprocessing_quick_mode: true,
            inproc: inproc_engines::InprocessingEngines::new(num_vars),
            subsume_dirty: vec![true; num_vars], // all dirty initially so first round processes everything
            l0_gc_dirty: vec![false; num_vars],  // no fixed variables yet
            dirty_watches: vec![false; num_vars * 2], // no stale entries initially
            dirty_watch_list: Vec::new(),        // no dirty entries initially
            gc_occ: None,
            gc_occ_scratch: None,
            probing_mode: false,
            hbr_enabled: true, // Re-enabled: probe_parent array fixes #3419
            lrat_probe_parent_chain_enabled: false,
            lrat_proof_clamp_probe_rescue_enabled: false,
            inprocessing_yield_productivity_rescue_enabled: false,
            inprocessing_yield_rescue_backbone_cooldown_enabled: false,
            bounded_backbone_zero_decompose_backoff_enabled: false,
            hbr_lits: Vec::with_capacity(32),
            probe_parent: vec![None; num_vars],
            deferred_watch_list: WatchList::new(),
            deferred_replacement_watches: Vec::new(),
            fixed_count: 0,
            var_lifecycle: lifecycle::VarLifecycle::new(num_vars),
            lit_marks: LitMarks::new(num_vars),
            last_conflict_clause_ref: None,
            last_conflict_clause_id: 0,
            has_empty_clause: false,
            // Glue recomputation stamp table
            glue_stamp: vec![0u32; num_vars + 1], // indexed by decision level (0..=max_level)
            glue_stamp_counter: 0u32,
            // Block-level shrinking stamp table
            shrink_stamp: vec![0u32; num_vars],
            shrink_stamp_counter: 0,
            shrink_enabled: true,
            reap: reap::Reap::new(),
            ws_shrink_entries: Vec::new(),
            ws_shrink_result: Vec::new(),
            ws_shrink_block_lits: Vec::new(),
            ws_shrink_chain: Vec::new(),
            tiers: tier_state::TierState::new(),
            min: minimization_state::MinimizationState::new(num_vars),
            phase_init: phase_init_state::PhaseInitState::new(num_vars),
            cold: Box::new(cold::ColdState::new(
                num_vars,
                clauses_capacity,
                lrat_enabled,
            )),
            provenance: crate::clause_provenance::ProvenanceTracker::new(),
            dip: dip::DipManager::new(),
            active_domain: None,
            decision_domain: None,
            bucket_queue_active: false,
            domain_restarts: 0,
            relevancy_branching: false,
            relevancy_buf: Vec::new(),
            relevancy_decisions: 0,
            relevancy_hard: false,
            wander_abort_armed: false,
            wander_abort_tripped: false,
            wander_abort_base_conflicts: 0,
            wander_abort_base_decisions: 0,
            pending_theory_conflicts: std::collections::VecDeque::new(),
            #[cfg(feature = "jit")]
            jit_conflict_processor: None,
            #[cfg(feature = "jit")]
            jit_conflict_output: ay_jit::conflict_jit::ConflictProcessorOutput::new(num_vars),
        };

        // Debug builds: full checking (every derived clause RUP-verified, #4564).
        // Release proof output is emit-only unless verification is explicitly enabled.
        if solver.proof_manager.is_some() {
            #[cfg(debug_assertions)]
            {
                solver.cold.forward_checker =
                    Some(crate::forward_checker::ForwardChecker::new(num_vars));
            }
        }

        solver
    }
}
