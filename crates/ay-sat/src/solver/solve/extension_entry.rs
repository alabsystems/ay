// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extension-mode entry points and initialization for DPLL(T) solving.

use super::super::*;
use super::theory_callback::ExtensionCallback;

impl Solver {
    /// Solve with an extension extracted from the SAT clause database during the
    /// initial preprocess stage.
    ///
    /// The builder sees a snapshot of the current active irredundant clauses,
    /// may consume some of them into an extension, and may freeze variables
    /// before SAT preprocessing continues. The extension then joins the normal
    /// extension propagation loop for BCP/CDCL.
    pub fn solve_with_preprocessing_extension<E, B>(
        &mut self,
        build_extension: B,
    ) -> VerifiedSatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
    {
        VerifiedSatResult::from_validated(
            self.solve_with_preprocessing_extension_raw(build_extension),
        )
    }

    /// Interruptible variant of `solve_with_preprocessing_extension`.
    pub fn solve_interruptible_with_preprocessing_extension<E, B, F>(
        &mut self,
        build_extension: B,
        should_stop: F,
    ) -> VerifiedSatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(
            self.solve_interruptible_with_preprocessing_extension_raw(build_extension, should_stop),
        )
    }

    /// Solve with a theory extension for eager DPLL(T) integration
    ///
    /// The extension is called after each propagation phase to check for
    /// theory propagations. If the extension returns clauses, they are added
    /// to SAT and propagation continues. If the extension returns a conflict,
    /// SAT handles it like any other conflict.
    ///
    /// This is the recommended way to integrate theory solvers for eager
    /// DPLL(T) where theory propagation happens during SAT search.
    pub fn solve_with_extension(&mut self, ext: &mut dyn Extension) -> VerifiedSatResult {
        VerifiedSatResult::from_validated(self.solve_with_extension_raw(ext))
    }

    /// Solve with a theory extension under a set of assumption literals (#LNS).
    ///
    /// Combines eager-DPLL(T) theory propagation (like `solve_with_extension`)
    /// with assumption-based solving (like `solve_with_assumptions`), reusing the
    /// existing assumption+extension CDCL loop (`solve_with_assumptions_impl` with
    /// `eager_ext`, the same path the scoped-extension case uses). The assumptions
    /// are temporary and automatically retracted on return, so a caller can solve
    /// many different assumption sets over the same constraint database without
    /// rebuilding — the foundation for a rebuild-free Large Neighborhood Search.
    pub fn solve_with_extension_and_assumptions(
        &mut self,
        ext: &mut dyn Extension,
        assumptions: &[Literal],
    ) -> VerifiedSatResult {
        VerifiedSatResult::from_validated(
            self.solve_with_extension_and_assumptions_raw(ext, assumptions),
        )
    }

    fn solve_with_extension_and_assumptions_raw(
        &mut self,
        ext: &mut dyn Extension,
        assumptions: &[Literal],
    ) -> SatResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        if self.arena.has_oversized_clause() {
            let result = self.declare_unknown_with_reason(SatUnknownReason::ClauseTooLarge);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            self.reset_constraint();
            return result;
        }
        if let Some(result) = self.finish_stopped_sat_entry(&|| false) {
            // This API owns a one-shot constraint just like the ordinary
            // assumption entry. A stop must not leak it into the retry.
            self.reset_constraint();
            return result;
        }
        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            self.reset_constraint();
            return result;
        }
        let combined = self.compose_scope_assumptions(assumptions);
        let result = match self.solve_with_assumptions_impl(
            &combined,
            None::<&fn() -> bool>,
            None,
            None,
            Some(ext),
        ) {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve_with_extension_and_assumptions()")
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        // Reset the temporary assumption/constraint scope so repeated calls with
        // different assumption sets don't leak state (mirrors
        // `solve_with_assumptions_raw`; omitting this hung the 2nd LNS call).
        self.reset_constraint();
        result
    }

    /// Solve with a theory extension AND an interrupt callback (#6296).
    ///
    /// Combines `solve_with_extension` (theory phase hints, propagation) with
    /// `solve_interruptible` (timeout/interrupt support). The `should_stop`
    /// closure is polled every 100 conflicts and every 1000 decisions.
    pub fn solve_interruptible_with_extension<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> VerifiedSatResult
    where
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(
            self.solve_interruptible_with_extension_raw(ext, should_stop),
        )
    }

    /// Continue solving with an extension after adding new clauses (#8256).
    ///
    /// Unlike `solve_interruptible_with_extension`, this preserves VSIDS scores,
    /// CHB ratings, learned clauses, and EMA state across iterations. Only the
    /// trail and watches are rebuilt. This makes split-loop iterations O(clauses)
    /// instead of O(clauses + arena_rebuild + heap_rebuild + counter_reset).
    ///
    /// REQUIRES: The solver has already been initialized via a prior full solve.
    /// New clauses may have been added via `add_clause()` since the last solve.
    pub fn continue_solving_with_extension<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> VerifiedSatResult
    where
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(
            self.continue_solving_with_extension_raw(ext, should_stop),
        )
    }

    /// Resume solving after a budget-exhausted interruption (#8256).
    ///
    /// Unlike `continue_solving_with_extension`, this does NOT reset the trail,
    /// flush learned clauses, or rebuild VSIDS state. It simply re-enters the
    /// CDCL loop from the current state with a new should_stop closure.
    ///
    /// This is safe when:
    /// 1. The prior solve returned Unknown(Interrupted) due to should_stop
    /// 2. No new clauses have been added via add_clause()
    /// 3. The theory extension is in the same state (same trail position)
    ///
    /// On simple_startup_10nodes, continue_solving_with_extension spends ~2ms
    /// per budget-exhausted iteration on trail reset + VSIDS rebuild + learned
    /// clause flush. With 30+ iterations in 30s, this is 60ms+ of pure overhead.
    /// More critically, flushing non-core learned clauses discards search progress.
    /// resume_solving preserves the entire search state including learned clauses.
    pub fn resume_solving_with_extension<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> VerifiedSatResult
    where
        F: Fn() -> bool,
    {
        VerifiedSatResult::from_validated(self.resume_solving_with_extension_raw(ext, should_stop))
    }

    /// Internal resume implementation — re-enters CDCL loop without trail reset.
    fn resume_solving_with_extension_raw<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        // Oversized-clause poison (see `ClauseArena::add` / `declare_unsat`): a
        // clause too large for the arena's 16-bit length field was stored
        // truncated. SAT stays sound, but UNSAT is untrustworthy. The scoped
        // paths below can return UNSAT directly (AssumeResult::Unsat) without
        // routing through `declare_unsat`, so gate the whole solve to Unknown
        // up front when the arena is poisoned.
        if self.arena.has_oversized_clause() {
            let result = self.declare_unknown_with_reason(SatUnknownReason::ClauseTooLarge);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if let Some(result) = self.finish_stopped_sat_entry(&should_stop) {
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.progress_enabled || self.has_observer() {
            self.cold.solve_start_time = Some(ay_core::time::Instant::now());
            self.cold.last_progress_time = None;
        }

        // No trail reset, no learned clause flush, no VSIDS rebuild.
        // Simply re-enter the CDCL loop from the current state.

        let mut callback = ExtensionCallback { ext };
        let result = self.cdcl_loop(&mut callback, should_stop);
        self.clear_lazy_reason_tables();
        result
    }

    /// Internal lightweight re-solve that preserves heuristic state.
    ///
    /// #8399: Safe recovery variant that flushes non-core learned clauses
    /// before re-solving. This prevents the sc-8 non-convergence pattern
    /// where stale learned clauses lock the solver into revisiting the
    /// same search region, while preserving VSIDS/CHB scores and phase
    /// saving that help the search on ~15 other benchmarks.
    ///
    /// What is preserved:
    /// - VSIDS heap scores and variable ordering
    /// - CHB ratings
    /// - Phase saving (saved polarities)
    ///
    /// What is flushed/reset:
    /// - Learned clauses with LBD > CORE_LBD (2) — these cause non-convergence
    /// - Restart counters (LBD EMA, Luby index) — fresh restart schedule
    /// - Conflict-since-restart counter — fresh restart window
    fn continue_solving_with_extension_raw<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY across solve() calls.

        if let Some(result) = self.finish_stopped_sat_entry(&should_stop) {
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.progress_enabled || self.has_observer() {
            self.cold.solve_start_time = Some(ay_core::time::Instant::now());
            self.cold.last_progress_time = None;
        }

        // Trail reset: undo ALL assignments including level-0.
        // Save phase for each variable before clearing (phase saving).
        if self.decision_level > 0 {
            self.backtrack(0);
        }
        for i in 0..self.trail.len() {
            let lit = self.trail[i];
            let var = lit.variable();
            // Save phase (CaDiCaL backtrack.cpp:14)
            self.phase[var.index()] = lit.sign_i8();
            // Clear vals entries
            let base = var.index() * 2;
            ay_prefetch::val_set(&mut self.vals, base, 0);
            ay_prefetch::val_set(&mut self.vals, base + 1, 0);
            // Push back to VSIDS heap
            self.vsids.insert_into_heap(var);
            self.vsids.vmtf_on_unassign(var);
        }
        // Clear conflict analysis state
        self.conflict.clear(&mut self.var_data);
        self.var_data.fill(VarData::UNASSIGNED);
        self.bump_reason_graph_epoch();
        // Clear trail
        self.trail.clear();
        self.trail_lim.clear();
        self.decision_level = 0;
        self.qhead = 0;
        // Clear LRAT proof tracking
        self.unit_proof_id.fill(0);
        self.unit_proof_sign.fill(0);
        self.cold.level0_proof_id.fill(0);
        self.cold.level0_proof_sign.fill(0);
        self.cold.lrat_level0_unit_materialize_cursor = 0;
        self.cold.lrat_level0_unit_materialize_pinned.clear();
        // Reset fixed variable tracking
        self.var_lifecycle.reset_fixed();
        self.fixed_count = 0;
        self.l0_gc_dirty.iter_mut().for_each(|d| *d = false);

        // #8399: Flush non-core learned clauses to prevent search stalls.
        //
        // The sc-8 non-convergence pattern: stale learned clauses from prior
        // iterations encode search-space pruning that was valid for the old
        // disequality branch but biases the solver into the same dead-end
        // region when a new disequality is added. Core clauses (LBD <= 2)
        // are nearly universally useful and safe to keep.
        //
        // This is modeled after between_solve_reduce (#8435) but more
        // aggressive: we flush ALL non-core learned clauses, not just a
        // fraction. The trail is empty so no reason clause protection needed.
        {
            let mut flushed = 0u64;
            let learned_indices: Vec<usize> = self
                .arena
                .active_indices()
                .filter(|&idx| self.arena.is_learned(idx) && self.arena.lbd(idx) > CORE_LBD)
                .collect();

            for idx in &learned_indices {
                if !self.arena.is_active(*idx) {
                    continue;
                }

                // Mark watched literals dirty for lazy flush.
                if !self.watches_disconnected {
                    let clause_len = self.arena.len_of(*idx);
                    if clause_len > 2 {
                        let (w0, w1) = self.arena.watched_literals(*idx);
                        if w0.index() < self.dirty_watches.len() {
                            self.dirty_watches[w0.index()] = true;
                        }
                        if w1.index() < self.dirty_watches.len() {
                            self.dirty_watches[w1.index()] = true;
                        }
                    }
                    self.delete_binary_clause_watches(*idx);
                }

                // Occ list maintenance.
                if let Some(ref mut gc_occ) = self.gc_occ {
                    let lits = self.arena.literals(*idx).to_vec();
                    gc_occ.remove_clause(*idx, &lits);
                }

                self.stats.clear_bcp_learned_1963_blocker_cert(*idx);
                self.arena.delete(*idx);
                self.cold.clause_db_changes += 1;
                flushed += 1;
            }

            if flushed > 0 {
                tracing::debug!(
                    flushed,
                    core_kept = self.arena.active_clause_count(),
                    "#8399 continue_solving: flushed non-core learned clauses"
                );
            }
        }

        // #8399: Decay VSIDS scores to make variable ordering more exploratory.
        //
        // When preserving VSIDS scores across split-loop iterations, the
        // variable ordering can lock into a search trajectory that was optimal
        // for the previous clause set but suboptimal after new theory conflict
        // clauses are added. Multiplicative decay (0.5x) preserves relative
        // ordering while reducing score magnitude, which effectively makes the
        // bump from new conflicts more influential in steering the search.
        //
        // This is equivalent to CaDiCaL's `stablebump` (bump.cpp): after a
        // restart, recent activity dominates over stale activity because the
        // bump increment exceeds halved historical scores.
        //
        // A factor of 0.5 is aggressive enough to allow new conflicts to
        // redirect the search, while still preserving the relative variable
        // ordering from the previous iteration (which is approximately correct
        // for the shared clause structure).
        self.vsids.decay_all_scores(0.5);

        // #8399: Reset restart counters for a fresh search schedule.
        // Stale LBD EMAs from the previous iteration's search make the
        // Glucose restart heuristic either too eager or too reluctant.
        // Resetting gives the new iteration a clean restart profile.
        self.cold.lbd_ema_fast = 0.0;
        self.cold.lbd_ema_slow = 0.0;
        self.cold.lbd_ema_fast_biased = 0.0;
        self.cold.lbd_ema_slow_biased = 0.0;
        self.cold.lbd_ema_fast_exp = 1.0;
        self.cold.lbd_ema_slow_exp = 1.0;
        self.cold.luby_idx = 1;
        self.conflicts_since_restart = 0;
        // Reset reluctant doubling state for fresh Luby schedule.
        self.cold.reluctant_u = 1;
        self.cold.reluctant_v = 1;
        self.cold.reluctant_countdown = RELUCTANT_INIT;
        self.cold.reluctant_ticked_at = 0;

        // Update clause counts (new clauses may have been added, old learned flushed).
        self.num_original_clauses = self.arena.active_clause_count();
        self.cold.original_clause_boundary = self.arena.len();

        // Streaming UNSAT core bitmap (#8250).
        // Issued-original max, not next_original_clause_id - 1: the latter
        // jumps past derived IDs (b93692341 follow-up).
        let num_originals = self.cold.issued_original_clause_id_max;
        if num_originals > 0 {
            self.cold.streaming_core_num_originals = num_originals;
            if let Some(ref mut bitmap) = self.cold.streaming_core {
                bitmap.clear();
                bitmap.resize(num_originals as usize, false);
            } else {
                self.cold.streaming_core = Some(vec![false; num_originals as usize]);
            }
        } else {
            self.cold.streaming_core_num_originals = 0;
            self.cold.streaming_core = None;
        }

        // Watch rebuild: add_clause() does NOT attach watches, so we must
        // rebuild all watches from scratch. Also needed because we flushed
        // learned clauses above.
        self.watches.clear();
        self.watches.ensure_num_vars(self.num_vars);
        self.initialize_watches();

        // Unit propagation + extension init.
        if let Some(conflict_ref) = self.process_initial_clauses() {
            self.record_level0_conflict_chain(conflict_ref);
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }
        ext.init();
        if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        self.disable_extension_inprocessing();

        // Clear stale lazy reasons from prior solve (#8467).
        // Uses the safe method that also clears trail FLAG_LAZY_THEORY_REASON flags.
        self.clear_lazy_reason_tables();

        let mut callback = ExtensionCallback { ext };
        let result = self.cdcl_loop(&mut callback, should_stop);
        self.clear_lazy_reason_tables();
        result
    }

    /// Internal interruptible extension solve returning raw `SatResult`.
    fn solve_interruptible_with_extension_raw<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        // Oversized-clause poison (see `ClauseArena::add` / `declare_unsat`): a
        // clause too large for the arena's 16-bit length field was stored
        // truncated. SAT stays sound, but UNSAT is untrustworthy. The scoped
        // paths below can return UNSAT directly (AssumeResult::Unsat) without
        // routing through `declare_unsat`, so gate the whole solve to Unknown
        // up front when the arena is poisoned.
        if self.arena.has_oversized_clause() {
            let result = self.declare_unknown_with_reason(SatUnknownReason::ClauseTooLarge);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if let Some(result) = self.finish_stopped_sat_entry(&should_stop) {
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions_with_extension_interruptible(ext, should_stop);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        // #8423: Scoped extension support with interrupt callback.
        let assumptions = self.compose_scope_assumptions(&[]);
        let result = match self.solve_with_assumptions_impl(
            &assumptions,
            Some(&should_stop),
            None,
            None,
            Some(ext),
        ) {
            AssumeResult::Sat(model) => self
                .sat_from_assume_model(model, "solve_interruptible_with_extension() scoped path"),
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    fn solve_interruptible_with_preprocessing_extension_raw<E, B, F>(
        &mut self,
        build_extension: B,
        should_stop: F,
    ) -> SatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        // Oversized-clause poison (see `ClauseArena::add` / `declare_unsat`): a
        // clause too large for the arena's 16-bit length field was stored
        // truncated. SAT stays sound, but UNSAT is untrustworthy. The scoped
        // paths below can return UNSAT directly (AssumeResult::Unsat) without
        // routing through `declare_unsat`, so gate the whole solve to Unknown
        // up front when the arena is poisoned.
        if self.arena.has_oversized_clause() {
            let result = self.declare_unknown_with_reason(SatUnknownReason::ClauseTooLarge);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.has_empty_clause {
            if let Some(result) = self.finish_stopped_sat_entry(&should_stop) {
                return result;
            }
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            if let Some(result) = self.finish_stopped_sat_entry(&should_stop) {
                return result;
            }
            let result = self
                .solve_no_assumptions_with_preprocessing_extension(build_extension, should_stop);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        debug_assert!(
            self.cold.scope_selectors.is_empty(),
            "solve_interruptible_with_preprocessing_extension() with non-empty \
             scope_selectors is not supported"
        );
        self.trace_sat_result(&SatResult::Unknown);
        self.finish_tla_trace();
        self.declare_unknown_with_reason(SatUnknownReason::UnsupportedConfig)
    }

    /// Internal extension solve returning raw `SatResult`.
    fn solve_with_extension_raw(&mut self, ext: &mut dyn Extension) -> SatResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        // Oversized-clause poison (see `ClauseArena::add` / `declare_unsat`): a
        // clause too large for the arena's 16-bit length field was stored
        // truncated. SAT stays sound, but UNSAT is untrustworthy. The scoped
        // paths below can return UNSAT directly (AssumeResult::Unsat) without
        // routing through `declare_unsat`, so gate the whole solve to Unknown
        // up front when the arena is poisoned.
        if self.arena.has_oversized_clause() {
            let result = self.declare_unknown_with_reason(SatUnknownReason::ClauseTooLarge);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if let Some(result) = self.finish_stopped_sat_entry(&|| false) {
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions_with_extension(ext);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        // #8423: Scoped extension support. When scope_selectors are non-empty,
        // compose scope assumptions and run the assumption-based CDCL loop with
        // full extension callbacks (propagate, check, backtrack, suggest).
        // Previously this path rejected extensions entirely. Now the extension
        // is wired into the assumption loop via the eager_ext parameter.
        let assumptions = self.compose_scope_assumptions(&[]);
        let result = match self.solve_with_assumptions_impl(
            &assumptions,
            None::<&fn() -> bool>,
            None,
            None,
            Some(ext),
        ) {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve_with_extension() scoped path")
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    fn solve_with_preprocessing_extension_raw<E, B>(&mut self, build_extension: B) -> SatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
    {
        self.solve_interruptible_with_preprocessing_extension_raw(build_extension, || false)
    }

    pub(super) fn solve_no_assumptions_with_extension(
        &mut self,
        ext: &mut dyn Extension,
    ) -> SatResult {
        let mut callback = ExtensionCallback { ext };
        let result = self.solve_no_assumptions_with_theory_backend(&mut callback, || false);
        self.clear_lazy_reason_tables();
        result
    }

    /// Interruptible extension solve: combines extension callbacks with a
    /// `should_stop` closure for timeout/interrupt support (#6296).
    pub(super) fn solve_no_assumptions_with_extension_interruptible<F>(
        &mut self,
        ext: &mut dyn Extension,
        should_stop: F,
    ) -> SatResult
    where
        F: Fn() -> bool,
    {
        let mut callback = ExtensionCallback { ext };
        let result = self.solve_no_assumptions_with_theory_backend(&mut callback, should_stop);
        self.clear_lazy_reason_tables();
        result
    }

    pub(super) fn solve_no_assumptions_with_preprocessing_extension<E, B, F>(
        &mut self,
        mut build_extension: B,
        should_stop: F,
    ) -> SatResult
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        if let Some(reason) = self.solve_stop_reason(&should_stop) {
            return self.declare_unknown_with_reason(reason);
        }

        let init_result = self.init_solve();
        if let Some(reason) = self.solve_stop_reason(&should_stop) {
            return self.declare_unknown_with_reason(reason);
        }
        if let Some(result) = init_result {
            return result;
        }

        let mut extension = if self.cold.has_been_incremental {
            None
        } else {
            self.prepare_preprocessing_extension(&mut build_extension)
        };

        if let Some(reason) = self.solve_stop_reason(&should_stop) {
            if let Some(pending) = extension.as_ref() {
                self.cancel_preprocessing_extension(pending);
            }
            return self.declare_unknown_with_reason(reason);
        }

        let preprocess_outcome = if self.cold.preprocess_enabled {
            Some(self.preprocess_interruptible(&should_stop))
        } else {
            None
        };

        if let Err(result) = self.finish_preprocessing_extension_transaction(
            &mut extension,
            preprocess_outcome,
            &should_stop,
        ) {
            return result;
        }

        // JIT-compile static clauses into native propagation functions.
        // This happens once, after preprocessing, before the search loop.
        // Mirrors solve/mod.rs to ensure extension/theory paths get JIT benefit.
        // Uses adaptive compilation (#8203) for size-dependent strategy.

        let Some(mut extension) = extension else {
            return self.solve_remaining_no_assumptions(should_stop);
        };

        self.disable_extension_inprocessing();

        {
            let irredundant = self.arena.active_clause_count() as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.total_conflicts().saturating_add(limit);
        }

        let extension = &mut extension.prepared;
        extension.extension.init();
        let mut callback = ExtensionCallback {
            ext: &mut extension.extension,
        };
        self.cdcl_loop(&mut callback, should_stop)
    }

    fn solve_remaining_no_assumptions<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        {
            let irredundant = self.num_original_clauses as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.total_conflicts().saturating_add(limit);
        }

        if let Some(reason) = self.solve_stop_reason(&should_stop) {
            return self.declare_unknown_with_reason(reason);
        }

        if let Some(sat) = self.try_lucky_phases() {
            if let Some(reason) = self.solve_stop_reason(&should_stop) {
                return self.declare_unknown_with_reason(reason);
            }
            if sat {
                self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
                return self.declare_sat_from_current_assignment();
            }
            return self.declare_unsat();
        }
        if let Some(reason) = self.solve_stop_reason(&should_stop) {
            return self.declare_unknown_with_reason(reason);
        }

        self.try_warmup();

        if self.try_walk() {
            let candidate = self.get_model_from_phases();
            let mut reconstructed = candidate.clone();
            let reconstruction_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.inproc.reconstruction.reconstruct(&mut reconstructed);
            }))
            .is_ok();
            if reconstruction_ok && self.verify_model(&reconstructed) {
                self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
                return self.declare_sat_from_model(candidate);
            }
            if !reconstruction_ok {
                tracing::warn!("walk candidate reconstruction panicked");
            }
        }

        self.cdcl_loop_pure(should_stop)
    }

    /// Extension-specific solve initialization shared by the unified theory loop.
    pub(super) fn init_extension_loop(&mut self, ext: &mut dyn Extension) -> Option<SatResult> {
        // On second+ solve, disable destructive inprocessing (#5031).
        if self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;
        // Allow calling `solve()` multiple times after adding clauses.
        //
        // #lra-inc-engine (S1): in the incremental QF_LRA engine lane
        // (inc_engine_reset_mode, reached here only via the eager theory
        // extension on a depth-0 / no-scope check-sat) take the state-preserving
        // incremental reset so the level-0 trail, watches, VSIDS heap and learned
        // clauses persist across check-sats, instead of the full reset that
        // re-solves the accumulated formula from scratch. Re-establish the benign
        // var-growth cache invalidation (mirrors assumptions.rs);
        // `can_use_incremental_reset`'s arena-mutation guards remain the real
        // soundness gate and force a full ledger-rebuild reset on any destructive
        // op. When inc_engine_reset_mode is off this is byte-identical to the
        // previous unconditional full reset. (The real hybrid_networks files
        // check inside `(push 1)` and take the scoped assumptions.rs path; this
        // branch covers depth-0 check-sats.)
        let use_incremental = if self.cold.inc_engine_reset_mode {
            self.cold.assumption_cache_valid = true;
            self.can_use_incremental_reset()
        } else {
            false
        };
        if use_incremental {
            self.stats.ext_incremental_reset_hits += 1;
            self.reset_search_state_incremental();
        } else {
            if self.cold.inc_engine_reset_mode {
                self.stats.ext_full_reset_hits += 1;
            }
            self.reset_search_state();
        }

        // TLA trace: emit initial state (step 0, no action).
        self.tla_trace_step(CdclTraceState::Propagating, None);

        // Handle empty formula - but still check extension for theory constraints.
        if self.arena.is_empty() {
            if let Some(result) = self.handle_empty_formula_extension_init(ext) {
                return Some(result);
            }
        }

        // Track irredundant clause count for density-aware protection in
        // reduce_db (#8633). Use irredundant_count() not num_clauses() to
        // avoid inflating the density ratio with learned clauses.
        self.num_original_clauses = self.arena.irredundant_count();
        self.cold.original_clause_boundary = self.arena.len();

        // Initialize streaming UNSAT core bitmap (#8250).
        // Issued-original max, not next_original_clause_id - 1: the latter
        // jumps past derived IDs (b93692341 follow-up).
        let num_originals = self.cold.issued_original_clause_id_max;
        if num_originals > 0 {
            self.cold.streaming_core_num_originals = num_originals;
            if let Some(ref mut bitmap) = self.cold.streaming_core {
                bitmap.clear();
                bitmap.resize(num_originals as usize, false);
            } else {
                self.cold.streaming_core = Some(vec![false; num_originals as usize]);
            }
        } else {
            self.cold.streaming_core_num_originals = 0;
            self.cold.streaming_core = None;
        }

        // #lra-inc-engine (S1): in the incremental path the watch lists are
        // preserved from the previous solve and level-0 unit propagations are
        // already on the trail (mirrors the assumptions.rs incremental path);
        // rebuilding watches / reprocessing initial clauses would discard the
        // persisted state. New clauses added since the last solve are attached
        // inline by `reset_search_state_incremental` (ic3_new_clauses_pending).
        if !use_incremental {
            self.initialize_watches();

            if let Some(conflict_ref) = self.process_initial_clauses() {
                // Contradictory unit clauses — collect LRAT resolution chain
                // from the conflict clause so the empty-clause step has proper hints.
                self.record_level0_conflict_chain(conflict_ref);
                return Some(self.declare_unsat());
            }
        }

        ext.init();

        // Propagate level-0 units before entering the unified loop.
        let trail_before = self.trail.len();
        if let Some(conflict_ref) = self.search_propagate() {
            // Record the BCP resolution chain for proof reconstruction (#6368).
            // Without this, the clause trace has no empty-clause entry with
            // resolution hints, causing SAT proof reconstruction (Phase 1)
            // to fail and fall through to trust-lemma fallback.
            self.record_level0_conflict_chain(conflict_ref);
            return Some(self.declare_unsat());
        }
        if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
            self.tla_trace_step(
                CdclTraceState::Propagating,
                Some(CdclTraceAction::Propagate),
            );
        }

        None
    }

    fn handle_empty_formula_extension_init(
        &mut self,
        ext: &mut dyn Extension,
    ) -> Option<SatResult> {
        ext.init();
        let result = ext.propagate(self);

        // Process additional theory lemma clauses BEFORE handling conflicts (#4533).
        // When the XOR extension detects a 0=1 contradiction, it may include
        // intermediate proof clauses that are RUP-derivable from the original
        // XOR-encoding clauses. These must be emitted to the proof stream before
        // the empty clause so external DRAT checkers can verify the derivation.
        for clause in result.clauses {
            self.add_theory_lemma(clause);
        }

        if let Some(conflict) = result.conflict {
            if conflict.is_empty() {
                // Empty conflict = theory proved UNSAT unconditionally.
                return Some(self.declare_unsat());
            }
            self.add_theory_lemma(conflict);
        }
        for (clause, propagated) in result.propagations {
            self.add_theory_propagation_scoped(clause, propagated);
        }
        if self.has_empty_clause() {
            return Some(self.declare_unsat());
        }
        if result.stop {
            return Some(self.declare_unknown_with_reason(SatUnknownReason::TheoryStop));
        }
        if !self.arena.is_empty() {
            return None;
        }
        match ext.check(self) {
            ExtCheckResult::Sat => {
                self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
                Some(self.declare_sat_from_current_assignment())
            }
            ExtCheckResult::Conflict(clause) => {
                if clause.is_empty() {
                    // Empty conflict = theory proved UNSAT unconditionally.
                    return Some(self.declare_unsat());
                }
                self.add_theory_lemma(clause);
                None
            }
            ExtCheckResult::Unknown => {
                Some(self.declare_unknown_with_reason(SatUnknownReason::ExtensionUnknown))
            }
            ExtCheckResult::AddClauses(clauses) => {
                // #6546: add theory lemmas and continue solving.
                for clause in clauses {
                    self.add_theory_lemma(clause);
                }
                None
            }
        }
    }
}
