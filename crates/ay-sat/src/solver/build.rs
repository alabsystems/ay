// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver constructors: `new`, `with_proof`, `with_proof_output`, `build`.

use super::construction::{Construction, Ordinary};
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

    /// Create a solver that also knows how many clauses are coming.
    ///
    /// Without the hint the clause arena is pre-sized from `num_vars` alone —
    /// `num_vars * 4` clauses of 3 literals each — which is guesswork the DIMACS
    /// loaders do not need to do: they have parsed the header before they
    /// construct the solver. On the SAT-COMP 2026 reference instance
    /// (6 737 543 vars / 18 002 239 clauses) the guess reserves 27 M clauses and
    /// 80.9 M literals against a real 18 M and ~54 M, and on a variable-heavy
    /// formula it over-reserves by far more.
    ///
    /// The hint is advisory: the arena grows normally if it turns out low.
    pub fn with_clause_hint(num_vars: usize, num_clauses: usize) -> Self {
        Self::build_uncounted(num_vars, None, Some(num_clauses))
    }

    /// Reserve clause-arena room for a CNF of known shape.
    ///
    /// This is the trusted-producer counterpart of [`Self::with_clause_hint`].
    /// That constructor takes a *parsed* count (a DIMACS header) and is
    /// deliberately clamped to the `num_vars`-derived guess so a bogus header
    /// cannot reserve gigabytes. This method takes a count the caller derived
    /// from its own encoding plan, so there is nothing to distrust and no
    /// clamp: an eager lowering that produces 51.9 M clauses over 564 k
    /// variables is under-served by `num_vars * 4` by two orders of magnitude,
    /// and the arena then doubles all the way up from that guess — ending one
    /// doubling past what was needed, holding ~660 MB it never writes.
    ///
    /// Advisory: the arena grows normally if the hint turns out low, and the
    /// reservation is capped at the arena's addressable limit. Reserving
    /// capacity stores nothing and changes no search state.
    pub fn reserve_clause_capacity(&mut self, num_clauses: usize, num_literals: usize) {
        self.arena.reserve_clauses(num_clauses, num_literals);
        self.cold.original_ledger.reserve(num_clauses, num_literals);
    }

    /// Shared constructor: all Solver initialization in one place.
    fn build(num_vars: usize, proof_output: Option<ProofOutput>) -> Self {
        Self::build_uncounted(num_vars, proof_output, None)
    }

    fn build_uncounted(
        num_vars: usize,
        proof_output: Option<ProofOutput>,
        clause_hint: Option<usize>,
    ) -> Self {
        match Self::build_with_hint(num_vars, proof_output, clause_hint, &Ordinary) {
            Ok(solver) => solver,
            Err(never) => match never {},
        }
    }

    pub(super) fn build_with_hint<A: Construction>(
        num_vars: usize,
        proof_output: Option<ProofOutput>,
        clause_hint: Option<usize>,
        a: &A,
    ) -> Result<Self, A::Error> {
        a.metadata::<Self>()?;
        a.unsupported(
            num_vars > (1usize << 30),
            "SAT namespace exceeds packed watch bound",
        )?;
        a.unsupported(
            proof_output.is_some(),
            "counted proof writer construction not admitted",
        )?;
        a.unsupported(
            ay_core::misc_cli_flags().sat_mem_probe,
            "counted memory diagnostic construction not admitted",
        )?;
        let has_proof = proof_output.is_some();
        let lrat_enabled = proof_output.as_ref().is_some_and(ProofOutput::is_lrat);
        // Removed 100k cap for BV performance (#757) - BV CNF has ~3-5 clauses/var
        let clauses_capacity = match clause_hint {
            // Trust the header, with a little slack for clauses preprocessing
            // adds, but never reserve more than the num_vars-derived guess would
            // have: this may only shrink the reservation, never grow it.
            Some(n) => n
                .saturating_add(n / 8)
                .min(num_vars.saturating_mul(4))
                .max(1),
            None => num_vars.saturating_mul(4),
        };
        let literals_capacity = clauses_capacity.saturating_mul(3); // avg 3 lits/clause
                                                                    // `--sat-mem-probe`: attribute construction memory per sub-structure.
                                                                    //
                                                                    // AY pays ~849 resident bytes per variable before it has seen a clause —
                                                                    // a two-clause CNF that merely mentions variable 6737543 costs 5.72 GB,
                                                                    // and that tax costs 17 instances of the official SAT-COMP 2026 set
                                                                    // outright. Static attribution only reaches ~169 B/var, so this builds
                                                                    // each num_vars-sized sub-structure standalone and reports what it
                                                                    // actually commits. Diagnostic only: the probes are dropped immediately
                                                                    // and nothing here runs without the env var.
        if ay_core::misc_cli_flags().sat_mem_probe {
            let mut last = ay_sys::current_footprint_bytes();
            let step = |label: &str, live: &mut usize| {
                let now = ay_sys::current_footprint_bytes();
                let delta = now.saturating_sub(*live);
                eprintln!(
                    "c mem_probe {label:<26} {:>10.1} MB  {:>7.1} B/var",
                    delta as f64 / 1e6,
                    delta as f64 / num_vars.max(1) as f64,
                );
                *live = now;
            };
            let a = ClauseArena::with_capacity(clauses_capacity, literals_capacity);
            step("ClauseArena::with_capacity", &mut last);
            let w = WatchedLists::new(num_vars);
            step("WatchedLists::new", &mut last);
            let v = VSIDS::new(num_vars);
            step("VSIDS::new", &mut last);
            let c = ConflictAnalyzer::new(num_vars);
            step("ConflictAnalyzer::new", &mut last);
            let i = inproc_engines::InprocessingEngines::new(num_vars);
            step("InprocessingEngines::new", &mut last);
            let l = lifecycle::VarLifecycle::new(num_vars);
            step("VarLifecycle::new", &mut last);
            let m = LitMarks::new(num_vars);
            step("LitMarks::new", &mut last);
            let mn = minimization_state::MinimizationState::new(num_vars);
            step("MinimizationState::new", &mut last);
            let p = phase_init_state::PhaseInitState::new(num_vars);
            step("PhaseInitState::new", &mut last);
            // (ConflictProcessorOutput is behind the `jit` feature and measured
            // 0.0 B/var, so it is not probed here — referencing `ay_jit`
            // unconditionally breaks any build without that feature.)
            drop((a, w, v, c, i, l, m, mn, p));
        }

        #[allow(unused_mut)]
        let mut solver = Self {
            num_vars,
            user_num_vars: num_vars,
            arena: a.choose(
                || ClauseArena::with_capacity(clauses_capacity, literals_capacity),
                |owner| {
                    ClauseArena::try_with_capacity_counted(
                        clauses_capacity,
                        literals_capacity,
                        owner,
                    )
                },
            )?,

            watches: a.choose(
                || WatchedLists::new(num_vars),
                |owner| WatchedLists::try_new_counted(num_vars, owner),
            )?,
            watches_disconnected: false,
            defer_stale_reason_cleanup: false,
            defer_binary_unlink: false,
            l0_gc_sweep_active: false,
            defer_proof_deletions: false,
            deferred_proof_deletions: Vec::new(),
            earliest_affected_trail_pos: None,
            stale_reasons: Vec::new(),
            vsids: a.choose(
                || VSIDS::new(num_vars),
                |owner| VSIDS::try_new_counted(num_vars, owner),
            )?,
            conflict: a.choose(
                || ConflictAnalyzer::new(num_vars),
                |owner| ConflictAnalyzer::try_new_counted(num_vars, owner),
            )?,
            vals: a.filled(num_vars * 2, 0i8)?,
            var_data: a.filled(num_vars, VarData::UNASSIGNED)?,
            // Always allocate unit_proof_id unconditionally (#8069: Phase 2a).
            // Clause IDs are always tracked for deferred backward proof
            // reconstruction, so unit proof IDs must also always be available.
            unit_proof_id: a.filled(num_vars, 0)?,
            unit_proof_sign: a.filled(num_vars, 0)?,
            pending_theory_unit_proof_ids: Vec::new(),
            // Grown on demand, never pre-sized. This used to be
            // `a.filled(clauses_capacity * HEADER_WORDS + literals_capacity, 0)?`,
            // and since both capacities are derived from `num_vars` alone
            // (`num_vars * 4` clauses, `* 3` literals each) rather than from the
            // formula's actual size, it committed `num_vars * 24` ZEROED bytes
            // before a single clause was read: 647 MB on a 6.7 M-variable
            // SAT-COMP 2026 instance whose real arena is 380 MB, and it is
            // resident immediately because `a.filled(n, 0)?` writes.
            //
            // Nothing needed it eagerly. Every access site already handles a
            // short vector: `mark_reason_clause` falls into
            // `mark_reason_clause_cold`, which resizes; `refresh_reason_clause_marks`
            // resizes to `arena.len()`; and the conditioning reader is
            // bounds-checked. Instances that never reach inprocessing now never
            // allocate it at all.
            reason_clause_marks: Vec::new(),
            reason_clause_epoch: 1,
            reason_marks_invalidated: false,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            qhead: 0,
            phase: a.filled(num_vars, 0i8)?,
            target_phase: a.filled(num_vars, 0i8)?,
            best_phase: a.filled(num_vars, 0i8)?,
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
            two_stage_clause_management: false,
            two_stage_warm: ay_core::sat_ab_switches().two_stage_warm_scores_kissat == Some(true),
            // Ghost literal guard is only needed when chrono-BT can actually fire.
            // Chrono-BT fires when decision_level - jump_level > CHRONO_LEVEL_LIMIT.
            // This requires decision_level > CHRONO_LEVEL_LIMIT, which requires
            // num_vars > CHRONO_LEVEL_LIMIT (#8466).
            ghost_guard_needed: num_vars > CHRONO_LEVEL_LIMIT as usize,
            lambda: a.filled(num_vars, None)?,
            chrono_reuse_trail: true, // CaDiCaL-style trail reuse (re-enabled #112)
            stats: solver_stats::SolverStats::new(),
            num_decisions: 0,
            bump_order_sort_buf: Vec::new(),
            backbone_seen: a.filled(num_vars, false)?,
            vivify_analyzed: a.filled(num_vars, false)?,
            vivify_analyzed_to_clear: a.reserved(64)?,
            num_propagations: 0,
            num_search_propagations: 0,
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
            inproc: a.choose(
                || inproc_engines::InprocessingEngines::new(num_vars),
                |owner| inproc_engines::InprocessingEngines::try_new_counted(num_vars, owner),
            )?,
            subsume_dirty: a.filled(num_vars, true)?, // all dirty initially so first round processes everything
            l0_gc_dirty: a.filled(num_vars, false)?,  // no fixed variables yet
            dirty_watches: a.filled(num_vars * 2, false)?, // no stale entries initially
            dirty_watch_list: Vec::new(),             // no dirty entries initially
            gc_occ: None,
            gc_occ_scratch: None,
            probing_mode: false,
            hbr_enabled: true, // Re-enabled: probe_parent array fixes #3419
            lrat_probe_parent_chain_enabled: false,
            lrat_proof_clamp_probe_rescue_enabled: false,
            inprocessing_yield_productivity_rescue_enabled: false,
            inprocessing_yield_rescue_backbone_cooldown_enabled: false,
            bounded_backbone_zero_decompose_backoff_enabled: false,
            hbr_lits: a.reserved(32)?,
            probe_parent: a.filled(num_vars, None)?,
            deferred_watch_list: WatchList::new(),
            deferred_replacement_watches: Vec::new(),
            fixed_count: 0,
            var_lifecycle: lifecycle::VarLifecycle::build_admitted(num_vars, a)?,
            lit_marks: a.choose(
                || LitMarks::new(num_vars),
                |owner| LitMarks::try_new_counted(num_vars, owner),
            )?,
            last_conflict_clause_ref: None,
            last_conflict_clause_id: 0,
            has_empty_clause: false,
            // Glue recomputation stamp table
            glue_stamp: a.filled(num_vars + 1, 0u32)?, // indexed by decision level (0..=max_level)
            glue_stamp_counter: 0u32,
            // Block-level shrinking stamp table
            shrink_stamp: a.filled(num_vars, 0u32)?,
            shrink_stamp_counter: 0,
            shrink_enabled: true,
            reap: reap::Reap::new(),
            ws_shrink_entries: Vec::new(),
            ws_shrink_result: Vec::new(),
            ws_shrink_block_lits: Vec::new(),
            ws_shrink_chain: Vec::new(),
            tiers: tier_state::TierState {
                kissat_rule: ay_core::sat_ab_switches().reduce_kissat_tiers == Some(true),
                ..a.choose(tier_state::TierState::new, |owner| {
                    tier_state::TierState::build_admitted(&construction::Counted(owner))
                })?
            },
            min: minimization_state::MinimizationState::build_admitted(num_vars, a)?,
            phase_init: phase_init_state::PhaseInitState::build_admitted(num_vars, a)?,
            cold: a.boxed(cold::ColdState::new(
                num_vars,
                clauses_capacity,
                lrat_enabled,
                a,
            )?)?,
            provenance: crate::clause_provenance::ProvenanceTracker::new(),
            dip: dip::DipManager::new(),
            active_domain: None,
            decision_domain: None,
            bucket_queue_active: false,
            domain_restarts: 0,
            relevancy_branching: false,
            indep_support: Vec::new(),
            indep_support_frozen: Vec::new(),
            relevancy_frontier: relevancy_frontier::RelevancyFrontier::default(),
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
            jit_conflict_output: a.choose(
                || ay_jit::conflict_jit::ConflictProcessorOutput::new(num_vars),
                |owner| {
                    ay_jit::conflict_jit::ConflictProcessorOutput::try_new_counted(num_vars, owner)
                },
            )?,
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

        Ok(solver)
    }
}
