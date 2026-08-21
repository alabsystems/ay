// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver configuration and statistics accessors.

use super::*;
use crate::proof_capability::{self, ProofMode, ProofTransform};
#[cfg(test)]
use std::mem::size_of;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

impl Solver {
    /// Store an interrupt handle for cooperative cancellation (#3638).
    ///
    /// The flag is polled by `is_interrupted()` during preprocessing and
    /// inprocessing phases where the `should_stop` closure is not available.
    /// The CDCL main loop still uses the closure-based check.
    pub fn set_interrupt(&mut self, handle: Arc<AtomicBool>) {
        self.cold.interrupt = Some(handle);
    }

    /// Replace the cooperative-cancellation handle, including clearing it.
    ///
    /// Persistent SMT pipelines reuse one SAT solver across public queries, so
    /// they must rebind the exact current executor handle rather than retaining
    /// a flag owned by an earlier query.
    pub fn set_interrupt_handle(&mut self, handle: Option<Arc<AtomicBool>>) {
        self.cold.interrupt = handle;
    }

    /// Check whether an external interrupt has been requested.
    ///
    /// Returns true if `set_interrupt()` was called and the flag was set.
    /// Used in preprocessing/inprocessing to honor timeout during long-running
    /// techniques where the `should_stop` closure is not threaded through.
    #[inline]
    pub(super) fn is_interrupted(&self) -> bool {
        if self.cold.process_memory_interrupt {
            return true;
        }
        self.cold
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
    }

    /// True when preprocessing's local budget or the whole-solve deadline has
    /// expired. Existing preprocessing internals poll this helper directly.
    #[inline]
    pub(super) fn preprocess_timed_out(&self) -> bool {
        self.cold
            .preprocess_deadline
            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
            || self.solve_deadline_expired()
    }

    /// Install (or clear) the whole-solve wall-clock deadline
    /// (#array-deadline-forward, see `cold.solve_deadline`). The DPLL(T)
    /// pipelines forward the executor's live per-solve deadline here before
    /// each SAT call, so the phases a `should_stop` closure cannot reach
    /// (incremental inprocessing, level-0 GC, the non-interruptible
    /// assumption entry) still honor the caller's budget. Polled amortized;
    /// an expired deadline can only produce Unknown — never a verdict.
    pub fn set_solve_deadline(&mut self, deadline: Option<ay_core::time::Instant>) {
        self.cold.solve_deadline = deadline;
    }

    /// Returns true if the whole-solve wall-clock deadline has been reached
    /// (#array-deadline-forward). Amortize calls — this reads the clock.
    #[inline]
    pub(super) fn solve_deadline_expired(&self) -> bool {
        self.cold
            .solve_deadline
            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
    }

    /// Enable periodic progress line emission to stderr during solving.
    ///
    /// When enabled, the solver emits a compact one-line status summary to
    /// stderr approximately every 5 seconds. The format uses the DIMACS `c`
    /// comment prefix for compatibility with SAT competition tooling.
    ///
    /// Format: `c [5.0s] conflicts=N decisions=N props=N restarts=N learned=N mode=focused`
    pub fn set_progress_enabled(&mut self, enabled: bool) {
        self.cold.progress_enabled = enabled;
    }

    /// Enable BCP attribution telemetry in optimized builds.
    ///
    /// The propagation loop writes these counters, so release builds keep them
    /// off unless a caller explicitly enables BCP telemetry, such as DIMACS
    /// runs gated by `AY_BCP_TELEMETRY`. Debug builds still collect them
    /// unconditionally for solver diagnostics.
    pub fn set_bcp_telemetry_enabled(&mut self, enabled: bool) {
        self.cold.bcp_telemetry_enabled = enabled;
    }

    /// Return whether release BCP telemetry was explicitly requested.
    pub fn bcp_telemetry_enabled(&self) -> bool {
        self.cold.bcp_telemetry_enabled
    }

    /// Enable the outer-loop BCP trail-lookahead watch-list prefetch.
    ///
    /// This is enabled by default to preserve the current propagation policy.
    /// Turning it off keeps enqueue-time prefetching but removes the extra
    /// next-trail watch-list prefetch from the propagation loop for A/B runs.
    pub fn set_bcp_trail_lookahead_prefetch_enabled(&mut self, enabled: bool) {
        self.cold.bcp_trail_lookahead_prefetch = enabled;
    }

    /// Return whether outer-loop BCP trail-lookahead prefetch is enabled.
    pub fn bcp_trail_lookahead_prefetch_enabled(&self) -> bool {
        self.cold.bcp_trail_lookahead_prefetch
    }

    /// Enable the SEARCH-only in-place watch scan route.
    ///
    /// This is default-on (see `cold.rs`): in builds with the `raw-pointer-bcp`
    /// feature (a default feature) it routes full SEARCH BCP through the
    /// raw-pointer watch-list substrate — verified bit-identical to the safe
    /// deferred-copy path by `solver/tests/propagation_bcp_unsafe.rs`. Builds
    /// without `raw-pointer-bcp` retain the safe route regardless of this flag.
    pub fn set_bcp_search_inplace_watch_scan_enabled(&mut self, enabled: bool) {
        self.cold.bcp_search_inplace_watch_scan = enabled;
    }

    /// Return whether the SEARCH in-place watch scan route was requested.
    pub fn bcp_search_inplace_watch_scan_enabled(&self) -> bool {
        self.cold.bcp_search_inplace_watch_scan
    }

    /// Return whether the requested SEARCH in-place watch scan route can run in this build.
    pub fn bcp_search_inplace_watch_scan_route_enabled(&self) -> bool {
        self.cold.bcp_search_inplace_watch_scan && cfg!(feature = "raw-pointer-bcp")
    }

    /// Enable the experimental long-clause BCP saved-position advance.
    ///
    /// With this enabled, an unassigned replacement watch in a long clause writes
    /// `saved_pos` to the next tail slot (wrapping to 2) instead of the slot that
    /// will receive the just-falsified watched literal after the watch swap.
    pub fn set_bcp_advance_saved_pos_after_unassigned_move_enabled(&mut self, enabled: bool) {
        self.cold.bcp_advance_saved_pos_after_unassigned_move = enabled;
    }

    /// Return whether the experimental BCP saved-position advance is enabled.
    pub fn bcp_advance_saved_pos_after_unassigned_move_enabled(&self) -> bool {
        self.cold.bcp_advance_saved_pos_after_unassigned_move
    }

    /// Enable the experimental learned 19-63 false saved-position reset.
    ///
    /// With this enabled, learned clauses in the 19-63 bucket whose saved-position
    /// literal is already false restart replacement scanning at tail slot 2 and
    /// skip the known-false saved slot.
    pub fn set_bcp_learned_1963_false_saved_pos_reset_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_false_saved_pos_reset = enabled;
    }

    /// Return whether the learned 19-63 false saved-position reset is enabled.
    pub fn bcp_learned_1963_false_saved_pos_reset_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_false_saved_pos_reset
    }

    /// Enable the experimental learned 19-63 true-tail watch relocation.
    ///
    /// With this enabled, learned clauses in the 19-63 bucket move a watch to a
    /// satisfied tail replacement instead of only refreshing the blocker.
    pub fn set_bcp_learned_1963_true_tail_relocation_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_true_tail_relocation = enabled;
    }

    /// Return whether the learned 19-63 true-tail relocation is enabled.
    pub fn bcp_learned_1963_true_tail_relocation_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_true_tail_relocation
    }

    /// Enable the learned 19-63 used>=5 false-start-wrap saved-position reset.
    ///
    /// With this enabled, learned clauses in the 19-63 bucket whose
    /// no-replacement scan starts false, wraps, and has `used >= 5` reset
    /// `saved_pos` to tail slot 2.
    pub fn set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_used5_fsw_saved_pos_reset = enabled;
    }

    /// Return whether the learned 19-63 used>=5 FSW reset is enabled.
    pub fn bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_used5_fsw_saved_pos_reset
    }

    /// Enable the learned 19-63 FSW conflict-only saved-position reset.
    ///
    /// With this enabled, learned clauses in the 19-63 bucket whose
    /// no-replacement scan starts false, wraps, and ends in conflict reset
    /// `saved_pos` to tail slot 2. Unit outcomes do not write.
    pub fn set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_fsw_conflict_saved_pos_reset = enabled;
    }

    /// Return whether the learned 19-63 FSW conflict-only reset is enabled.
    pub fn bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_fsw_conflict_saved_pos_reset
    }

    /// Enable the experimental learned 6-18 true-tail watch relocation.
    ///
    /// With this enabled, learned clauses in the 6-18 buckets move a watch to a
    /// satisfied tail replacement instead of only refreshing the blocker.
    pub fn set_bcp_learned_618_true_tail_relocation_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_618_true_tail_relocation = enabled;
    }

    /// Return whether the learned 6-18 true-tail relocation is enabled.
    pub fn bcp_learned_618_true_tail_relocation_enabled(&self) -> bool {
        self.cold.bcp_learned_618_true_tail_relocation
    }

    /// Enable the experimental learned no-replacement saved-position update.
    ///
    /// With this enabled, learned long clauses whose replacement scan finds no
    /// non-false tail literal reset `saved_pos` to the normalized tail head.
    pub fn set_bcp_learned_no_replacement_saved_pos_update_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_no_replacement_saved_pos_update = enabled;
    }

    /// Return whether the learned no-replacement saved-position update is enabled.
    pub fn bcp_learned_no_replacement_saved_pos_update_enabled(&self) -> bool {
        self.cold.bcp_learned_no_replacement_saved_pos_update
    }

    /// Enable the learned 19-63 false-start-wrap Gent-order skip.
    ///
    /// With this enabled, learned clauses in the 19-63 bucket whose saved-position
    /// literal is already false preserve Gent replacement order while skipping
    /// the saved-start slot already proved false.
    pub fn set_bcp_learned_1963_fsw_gent_skip_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_fsw_gent_skip = enabled;
    }

    /// Return whether the learned 19-63 FSW Gent-order skip is enabled.
    pub fn bcp_learned_1963_fsw_gent_skip_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_fsw_gent_skip
    }

    /// Enable default-off learned no-replacement scan-pressure instrumentation.
    ///
    /// The gate records learned long-clause no-replacement scan counts and scan
    /// steps by length bucket. It does not alter saved positions, watch
    /// movement, propagation, or conflict behavior.
    pub fn set_bcp_learned_no_replacement_scan_pressure_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_no_replacement_scan_pressure = enabled;
    }

    /// Return whether learned no-replacement scan-pressure instrumentation is enabled.
    pub fn bcp_learned_no_replacement_scan_pressure_enabled(&self) -> bool {
        self.cold.bcp_learned_no_replacement_scan_pressure
    }

    /// Enable default-off exact learned 19-63 clause identity instrumentation.
    ///
    /// The hook records clause ID, age, LBD, used-count, scan pressure, repeat
    /// identity, and unit/conflict participation. It does not alter saved
    /// positions, watch movement, propagation, or conflict behavior.
    pub fn set_bcp_learned_1963_identity_profile_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_identity_profile = enabled;
        if enabled {
            self.stats.enable_bcp_learned_1963_identity();
        }
    }

    /// Return whether learned 19-63 exact identity instrumentation is enabled.
    pub fn bcp_learned_1963_identity_profile_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_identity_profile
    }

    /// Enable default-off learned 19-63 pressure-aware reduce_db ranking.
    ///
    /// This scheduling experiment only biases already-deletable normal reduce
    /// candidates and relies on exact 19-63 identity rows as its pressure
    /// source, so enabling it also enables the identity table.
    pub fn set_bcp_learned_1963_pressure_reduction_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_pressure_reduction = enabled;
        if enabled {
            self.set_bcp_learned_1963_identity_profile_enabled(true);
        }
    }

    /// Return whether learned 19-63 pressure-aware reduce_db ranking is enabled.
    pub fn bcp_learned_1963_pressure_reduction_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_pressure_reduction
    }

    /// Enable default-off learned 19-63 pressure-aware reduce_db retention.
    ///
    /// This scheduling experiment only biases already-deletable normal reduce
    /// candidates and relies on exact 19-63 identity rows as its pressure
    /// source, so enabling it also enables the identity table.
    pub fn set_bcp_learned_1963_pressure_retention_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_pressure_retention = enabled;
        if enabled {
            self.set_bcp_learned_1963_identity_profile_enabled(true);
        }
    }

    /// Return whether learned 19-63 pressure-aware reduce_db retention is enabled.
    pub fn bcp_learned_1963_pressure_retention_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_pressure_retention
    }

    /// Enable the learned 19-63 no-replacement unit blocker-refresh disable.
    ///
    /// This default-off experiment isolates the W58 unit blocker refresh on the
    /// clique-regression length bucket without changing other learned lengths or
    /// original clauses.
    pub fn set_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(
        &mut self,
        enabled: bool,
    ) {
        self.cold
            .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh = enabled;
    }

    /// Return whether learned 19-63 no-replacement unit blocker refresh is disabled.
    pub fn bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(&self) -> bool {
        self.cold
            .bcp_disable_learned_1963_no_replacement_unit_blocker_refresh
    }

    /// Enable the experimental learned 6-17 creation-time tail reorder.
    ///
    /// With this enabled, learned clauses in the 6-17 bucket preserve watched
    /// literals 0/1 and reorder only `literals[2..]` by descending decision
    /// level and trail position before the clause enters the arena.
    pub fn set_bcp_learned_617_tail_reorder_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_617_tail_reorder = enabled;
    }

    /// Return whether the learned 6-17 creation-time tail reorder is enabled.
    pub fn bcp_learned_617_tail_reorder_enabled(&self) -> bool {
        self.cold.bcp_learned_617_tail_reorder
    }

    /// Enable the experimental learned length-18 creation-time tail reorder.
    ///
    /// With this enabled, learned clauses in the length-18 bucket preserve watched
    /// literals 0/1 and reorder only `literals[2..]` by descending decision
    /// level and trail position before the clause enters the arena.
    pub fn set_bcp_learned_18_tail_reorder_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_18_tail_reorder = enabled;
    }

    /// Return whether the learned length-18 creation-time tail reorder is enabled.
    pub fn bcp_learned_18_tail_reorder_enabled(&self) -> bool {
        self.cold.bcp_learned_18_tail_reorder
    }

    /// Enable the experimental learned 19-63 creation-time tail reorder.
    ///
    /// With this enabled, learned clauses in the 19-63 bucket preserve watched
    /// literals 0/1 and reorder only `literals[2..]` by descending decision
    /// level and trail position before the clause enters the arena.
    pub fn set_bcp_learned_1963_tail_reorder_enabled(&mut self, enabled: bool) {
        self.cold.bcp_learned_1963_tail_reorder = enabled;
    }

    /// Return whether the learned 19-63 creation-time tail reorder is enabled.
    pub fn bcp_learned_1963_tail_reorder_enabled(&self) -> bool {
        self.cold.bcp_learned_1963_tail_reorder
    }

    /// Set the optional learned 19-63 creation-time tail reorder swap budget.
    ///
    /// When set, the learned 19-63 tail reorder is applied only when the stable
    /// adjacent-swap count is within this budget. `None` disables the budgeted
    /// route without changing the full reorder gate.
    pub fn set_bcp_learned_1963_tail_reorder_swap_budget(&mut self, budget: Option<u64>) {
        self.cold.bcp_learned_1963_tail_reorder_swap_budget = budget;
    }

    /// Return the optional learned 19-63 creation-time tail reorder swap budget.
    pub fn bcp_learned_1963_tail_reorder_swap_budget(&self) -> Option<u64> {
        self.cold.bcp_learned_1963_tail_reorder_swap_budget
    }

    /// Set the formula-size breakpoint for domain-restricted BCP (#8802).
    ///
    /// When an active domain is present above decision level 0, formulas with
    /// fewer than `min_vars` variables use full BCP instead of domain BCP.
    /// `0` forces domain BCP for every domain-restricted query. By default,
    /// IC3 mode uses `IC3_DOMAIN_BCP_MIN_VARS_DEFAULT`; non-IC3 domain solving
    /// preserves the historical always-use-domain-BCP behavior.
    pub fn set_domain_bcp_min_vars(&mut self, min_vars: usize) {
        self.cold.domain_bcp_min_vars = Some(min_vars);
    }

    /// Clear any explicit domain-BCP breakpoint override.
    pub fn clear_domain_bcp_min_vars_override(&mut self) {
        self.cold.domain_bcp_min_vars = None;
    }

    /// Return the effective domain-BCP breakpoint for the current solver mode.
    pub fn domain_bcp_min_vars(&self) -> usize {
        self.effective_domain_bcp_min_vars()
    }

    #[inline]
    pub(super) fn effective_domain_bcp_min_vars(&self) -> usize {
        self.cold.domain_bcp_min_vars.unwrap_or({
            if self.cold.ic3_mode {
                IC3_DOMAIN_BCP_MIN_VARS_DEFAULT
            } else {
                0
            }
        })
    }

    #[inline]
    pub(super) fn should_use_domain_bcp_for(&self, domain: &[bool]) -> bool {
        domain.len() >= self.effective_domain_bcp_min_vars()
    }

    /// Return whether the current build/run should write BCP attribution counters.
    #[inline(always)]
    /// Enable the lean SEARCH BCP route (#bcp-lean).
    pub fn set_bcp_lean_route_enabled(&mut self, enabled: bool) {
        self.cold.bcp_lean_route_enabled = enabled;
    }

    pub(super) fn should_collect_bcp_telemetry(&self) -> bool {
        cfg!(debug_assertions) || self.cold.bcp_telemetry_enabled
    }

    /// Return whether a default-off BCP route must force telemetry-specialized BCP.
    ///
    /// Functional experiments that can run without counters, such as learned
    /// 19-63 Gent-order skip, are intentionally excluded so score-timing runs
    /// can exercise the behavior without writing full BCP telemetry.
    #[inline(always)]
    pub(super) fn bcp_hot_path_telemetry_forced_by_experiment(&self) -> bool {
        self.cold.bcp_learned_no_replacement_saved_pos_update
            || self.cold.bcp_learned_1963_fsw_conflict_saved_pos_reset
            || self.cold.bcp_learned_no_replacement_scan_pressure
            || self.cold.bcp_learned_1963_identity_profile
    }

    /// Enable the official SAT-COMP Main/default/proof conflict-analysis hot path.
    ///
    /// When enabled, optional experiments and stats-only hooks are bypassed in
    /// the conflict-analysis path. This is intentionally narrower than the
    /// inprocessing profile: proof-producing non-official runs keep their
    /// historical instrumentation unless this flag is explicitly set.
    /// Stop maintaining the arena-offset-indexed clause-ID table.
    ///
    /// Only safe when NOTHING will read it: no proof of any format, no clause
    /// or decision trace, no ER definition log, no `bcp_learned_1963` identity
    /// profile. The DIMACS no-proof route is the one caller today. Worth
    /// 760 MB on an 18 M-clause instance, because the table is indexed by arena
    /// WORD and is therefore twice the size of the clause arena.
    pub fn set_clause_ids_disabled(&mut self, disabled: bool) {
        self.cold.clause_ids_disabled = disabled;
    }

    /// Declare this solver a ONE-SHOT SAT solve, enabling structural symmetry
    /// breaking (orbitopal fixing, the aux-free PHP refutation).
    ///
    /// Only call this when the solver will be used for a single non-incremental
    /// solve with no assumptions. Those routes remove models, which is
    /// satisfiability-preserving for the formula but NOT valid under
    /// assumptions: an assumption satisfiable only in a removed model would flip
    /// to UNSAT, and an unsat core could name assumptions that are not
    /// responsible.
    pub fn set_symmetry_oneshot(&mut self, oneshot: bool) {
        self.cold.symmetry_oneshot = oneshot;
    }

    /// Enable the official SAT Competition Main conflict-analysis pruning policy.
    pub fn set_sat_comp_main_conflict_pruning(&mut self, enabled: bool) {
        self.cold.sat_comp_main_conflict_pruning = enabled;
    }

    /// Return whether official Main conflict-analysis pruning is enabled.
    pub fn sat_comp_main_conflict_pruning_enabled(&self) -> bool {
        self.cold.sat_comp_main_conflict_pruning
    }

    /// Enable the stable-only rephase experiment.
    ///
    /// When enabled, scheduled rephases are held while the solver is in focused
    /// mode and fire once the normal restart controller reaches stable mode.
    pub fn set_stable_only_rephase_enabled(&mut self, enabled: bool) {
        self.cold.stable_only_rephase_enabled = enabled;
    }

    /// Return whether the stable-only rephase experiment is enabled.
    #[cfg(test)]
    pub(crate) fn stable_only_rephase_enabled(&self) -> bool {
        self.cold.stable_only_rephase_enabled
    }

    /// Hot-path predicate for optional conflict-analysis experiments/hooks.
    ///
    /// Normally driven by the route profile: only the official SAT-COMP
    /// Main/default/LRAT route prunes the per-conflict experiments (DIP-ERCL,
    /// IBCL, and friends). `--sat-prune-conflict-experiments=1|0` overrides it
    /// so the experiments can be A/B'd on any route.
    ///
    /// This exists because of a measurement, not a preference: profiling AY on
    /// the official 2026 set showed conflict analysis taking 41.6 % of active
    /// time against BCP's 36.7 % — inverted versus a Kissat-class solver — and
    /// those runs used `--competition --no-proof`, a route where none of the
    /// experiments are pruned. Whether they pay for themselves is therefore an
    /// open, measurable question rather than an assumption.
    #[inline(always)]
    pub(super) fn should_prune_conflict_analysis_experiments(&self) -> bool {
        match ay_core::misc_cli_flags().sat_prune_conflict_experiments {
            Some(forced) => forced,
            None => self.cold.sat_comp_main_conflict_pruning,
        }
    }

    /// Register a programmatic progress observer (#8155).
    ///
    /// The observer receives callbacks at conflict, restart, progress, and
    /// inprocessing events. When no observer is registered (the default),
    /// all callback sites are a single `Option::is_some()` check that the
    /// branch predictor eliminates — zero overhead.
    ///
    /// AI consumers (model-checker-consumer, deductive-checks, verification-consumer) use this for stall detection
    /// and timeout decisions instead of parsing stderr progress lines.
    ///
    /// Pass `None` to remove a previously registered observer.
    pub fn set_observer(&mut self, observer: Option<Box<dyn crate::observer::SolveObserver>>) {
        self.cold.observer = observer;
    }

    /// Install parallel-portfolio clause sharing hooks.
    ///
    /// This is crate-private because imported clauses are trusted learned
    /// clauses. The portfolio only enables it for non-proof DIMACS workers that
    /// share one formula and one variable namespace.
    pub(crate) fn set_portfolio_clause_sharing(
        &mut self,
        exporter: Option<Box<dyn FnMut(&[Literal], u32) + Send>>,
        importer: Option<Box<dyn FnMut() -> Vec<Vec<Literal>> + Send>>,
    ) {
        self.cold.portfolio_clause_exporter = exporter;
        self.cold.portfolio_clause_importer = importer;
    }

    /// Returns true if a programmatic observer is registered.
    #[inline]
    pub(crate) fn has_observer(&self) -> bool {
        self.cold.observer.is_some()
    }

    /// Build a `ProgressStats` snapshot from the current solver state.
    #[inline]
    pub(crate) fn progress_stats_snapshot(&self) -> crate::observer::ProgressStats {
        crate::observer::ProgressStats {
            conflicts: self.num_conflicts,
            decisions: self.num_decisions,
            propagations: self.num_propagations,
            restarts: self.cold.restarts,
            stable_mode: self.stable_mode,
            decision_level: self.decision_level,
        }
    }

    /// Notify the observer of a conflict event.
    ///
    /// Inline + `is_some()` guard makes this zero-cost when no observer is set.
    #[inline]
    pub(crate) fn notify_observer_conflict(&mut self) {
        if self.cold.observer.is_some() {
            let stats = self.progress_stats_snapshot();
            if let Some(obs) = self.cold.observer.as_mut() {
                obs.on_conflict(&stats);
            }
        }
    }

    /// Notify the observer of a restart event.
    #[inline]
    pub(crate) fn notify_observer_restart(&mut self) {
        if self.cold.observer.is_some() {
            let stats = self.progress_stats_snapshot();
            if let Some(obs) = self.cold.observer.as_mut() {
                obs.on_restart(&stats);
            }
        }
    }

    /// Notify the observer of a progress event (periodic, wall-clock gated).
    #[inline]
    pub(crate) fn notify_observer_progress(&mut self) {
        if self.cold.observer.is_some() {
            let stats = self.progress_stats_snapshot();
            if let Some(obs) = self.cold.observer.as_mut() {
                obs.on_progress(&stats);
            }
        }
    }

    /// Notify the observer that an inprocessing technique completed.
    #[inline]
    pub(crate) fn notify_observer_inprocessing(
        &mut self,
        technique: crate::observer::InprocessingTechnique,
        simplifications: u64,
    ) {
        if let Some(obs) = self.cold.observer.as_mut() {
            obs.on_inprocessing(technique, simplifications);
        }
    }

    /// Notify the observer that a clause was learned from conflict analysis.
    #[inline]
    pub(crate) fn notify_observer_learn(&mut self, clause_len: u32, lbd: u32) {
        if self.cold.observer.is_some() {
            if let Some(obs) = self.cold.observer.as_mut() {
                obs.on_learn(clause_len, lbd);
            }
        }
    }

    /// Notify the observer of a theory conflict.
    #[inline]
    pub(crate) fn notify_observer_theory_conflict(&mut self, theory: crate::observer::TheoryId) {
        if self.cold.observer.is_some() {
            if let Some(obs) = self.cold.observer.as_mut() {
                obs.on_theory_conflict(theory);
            }
        }
    }

    /// Enter incremental mode before the first solve (#5608).
    ///
    /// Disables destructive inprocessing (BVE, BCE, subsumption, etc.) so
    /// that the clause database is never rebuilt between incremental solves.
    /// This preserves learned clauses across optimization iterations.
    ///
    /// Call this after adding initial clauses but before the first `solve()`.
    /// Without this, the first solve may run BVE which eliminates variables,
    /// forcing a full arena rebuild on the second solve that drops all learned
    /// clauses — causing incremental optimization to re-derive everything.
    pub fn set_incremental_mode(&mut self) {
        self.disable_destructive_inprocessing();
    }

    /// Enable or disable initial preprocessing
    pub fn set_preprocess_enabled(&mut self, enabled: bool) {
        self.cold.preprocess_enabled = enabled;
    }

    /// Scale the *incremental* inprocessing re-fire interval by formula size
    /// (#maxsat-inproc-throttle). With `Some(n)`, the interval between
    /// incremental inprocessing rounds becomes `clamp(500, num_clauses / n,
    /// 20_000)` conflicts instead of the flat 500; `None` restores the legacy
    /// flat interval.
    ///
    /// Motivation: each incremental round scans O(arena) clauses (subsumption +
    /// vivification). On large weighted-MaxSAT formulas (hard clauses plus
    /// totalizers accumulated over hundreds of OLL core iterations) the flat
    /// interval over-fires — profiling put inprocessing at ~50% of runtime vs
    /// ~7% for BCP — starving lower-bound-proving core extraction. Scaling the
    /// interval with clause count keeps inprocessing a bounded fraction of
    /// runtime. The MaxSAT engine sets `Some(100)`; SAT/SMT/IC3/CHC consumers
    /// leave it unset. Frequency-only — the passes are sound whenever they run,
    /// so this can never change a verdict, only throughput.
    pub fn set_incremental_inprobe_divisor(&mut self, divisor: Option<u64>) {
        self.cold.incremental_inprobe_clause_divisor = divisor.filter(|&n| n > 0);
    }

    /// Select between quick and full preprocessing passes.
    ///
    /// This does not toggle preprocessing itself; it only controls whether the
    /// heavier preprocessing passes guarded by `preprocessing_quick_mode` are
    /// allowed to run when preprocessing is enabled.
    pub fn set_full_preprocessing(&mut self, enabled: bool) {
        self.preprocessing_quick_mode = !enabled;
    }

    /// Returns whether initial preprocessing is enabled.
    pub fn is_preprocess_enabled(&self) -> bool {
        self.cold.preprocess_enabled
    }

    /// Returns whether full preprocessing is enabled.
    pub fn is_full_preprocessing_enabled(&self) -> bool {
        !self.preprocessing_quick_mode
    }

    /// Enable or disable root symmetry preprocessing.
    pub fn set_symmetry_enabled(&mut self, enabled: bool) {
        self.cold.symmetry_enabled = enabled
            && (!(self.proof_manager.is_some() || self.cold.lrat_enabled)
                || proof_capability::transform_allowed(
                    ProofMode::from_lrat_enabled(self.cold.lrat_enabled),
                    ProofTransform::Symmetry,
                ));
    }

    /// Returns whether root symmetry preprocessing is enabled.
    pub fn is_symmetry_enabled(&self) -> bool {
        self.cold.symmetry_enabled
    }

    /// Returns whether walk-based phase initialization is enabled.
    pub fn is_walk_enabled(&self) -> bool {
        self.phase_init.walk_enabled
    }

    /// Enable or disable walk-based phase initialization (#1816)
    pub fn set_walk_enabled(&mut self, enabled: bool) {
        self.phase_init.walk_enabled = enabled;
        self.phase_init.startup_walk_enabled = enabled;
    }

    /// Enable or disable startup walk without changing periodic rephase walk.
    pub(crate) fn set_startup_walk_enabled(&mut self, enabled: bool) {
        self.phase_init.startup_walk_enabled = enabled;
        if enabled {
            self.phase_init.walk_enabled = true;
        }
    }

    /// Returns whether startup walk phase initialization is enabled.
    pub fn is_startup_walk_enabled(&self) -> bool {
        self.phase_init.startup_walk_enabled
    }

    /// Returns whether warmup-based phase initialization is enabled.
    pub fn is_warmup_enabled(&self) -> bool {
        self.phase_init.warmup_enabled
    }

    /// Enable or disable warmup-based phase initialization (#1816)
    pub fn set_warmup_enabled(&mut self, enabled: bool) {
        self.phase_init.warmup_enabled = enabled;
        self.phase_init.startup_warmup_enabled = enabled;
    }

    /// Enable or disable startup warmup without changing periodic rephase walk.
    pub(crate) fn set_startup_warmup_enabled(&mut self, enabled: bool) {
        self.phase_init.startup_warmup_enabled = enabled;
        if enabled {
            self.phase_init.warmup_enabled = true;
        }
    }

    /// Returns whether startup warmup phase initialization is enabled.
    pub fn is_startup_warmup_enabled(&self) -> bool {
        self.phase_init.startup_warmup_enabled
    }

    /// Snapshot the current inprocessing feature-enable profile.
    ///
    /// This is consumed by soundness-gate integration tests to assert that
    /// feature isolation toggles only the requested technique.
    pub fn inprocessing_feature_profile(&self) -> crate::InprocessingFeatureProfile {
        crate::InprocessingFeatureProfile {
            preprocess: self.cold.preprocess_enabled,
            walk: self.phase_init.walk_enabled,
            warmup: self.phase_init.warmup_enabled,
            shrink: self.shrink_enabled,
            hbr: self.hbr_enabled,
            vivify: self.inproc_ctrl.vivify.enabled,
            subsume: self.inproc_ctrl.subsume.enabled,
            probe: self.inproc_ctrl.probe.enabled,
            bve: self.inproc_ctrl.bve.enabled,
            bce: self.inproc_ctrl.bce.enabled,
            condition: self.inproc_ctrl.condition.enabled,
            decompose: self.inproc_ctrl.decompose.enabled,
            factor: self.inproc_ctrl.factor.enabled,
            sbva: self.inproc_ctrl.sbva.enabled,
            transred: self.inproc_ctrl.transred.enabled,
            htr: self.inproc_ctrl.htr.enabled,
            gate: self.inproc_ctrl.gate.enabled,
            congruence: self.inproc_ctrl.congruence.enabled,
            sweep: self.inproc_ctrl.sweep.enabled,
            backbone: self.inproc_ctrl.backbone.enabled,
            symmetry: self.cold.symmetry_enabled,
            reorder: self.inproc_ctrl.reorder.enabled,
            cce: self.inproc_ctrl.cce.enabled,
        }
    }

    /// Apply an `InprocessingFeatureProfile` to this solver, setting all
    /// technique toggles to match the profile.
    ///
    /// This is the single code path for writing back a full profile snapshot.
    /// Used by `VariantConfig::apply_to_solver()` and the portfolio's
    /// `apply_adaptive_adjustments()` to avoid field-by-field duplication.
    pub fn apply_feature_profile(&mut self, profile: &crate::InprocessingFeatureProfile) {
        self.set_preprocess_enabled(profile.preprocess);
        self.set_walk_enabled(profile.walk);
        self.set_warmup_enabled(profile.warmup);
        self.set_shrink_enabled(profile.shrink);
        self.set_hbr_enabled(profile.hbr);
        self.set_vivify_enabled(profile.vivify);
        self.set_subsume_enabled(profile.subsume);
        self.set_probe_enabled(profile.probe);
        self.set_bve_enabled(profile.bve);
        self.set_bce_enabled(profile.bce);
        self.set_condition_enabled(profile.condition);
        self.set_decompose_enabled(profile.decompose);
        self.set_factor_enabled(profile.factor);
        self.set_sbva_enabled(profile.sbva);
        self.set_transred_enabled(profile.transred);
        self.set_htr_enabled(profile.htr);
        self.set_gate_enabled(profile.gate);
        self.set_congruence_enabled(profile.congruence);
        self.set_sweep_enabled(profile.sweep);
        self.set_backbone_enabled(profile.backbone);
        self.set_symmetry_enabled(profile.symmetry);
        self.set_reorder_enabled(profile.reorder);
        self.set_cce_enabled(profile.cce);

        self.enforce_inprocessing_proof_overrides();
    }

    /// Set a custom inprocessing feature profile at runtime.
    ///
    /// This allows programmatic consumers (e.g., IC3 downstream IC3 engines) to
    /// dynamically adjust which inprocessing techniques are active between
    /// solving phases. For example, disabling BVE during short incremental
    /// queries but enabling it for long BMC unrollings.
    ///
    /// Equivalent to `apply_feature_profile` but named for discoverability
    /// as a standalone API rather than the internal variant-application path.
    pub fn set_inprocessing_profile(&mut self, profile: &crate::InprocessingFeatureProfile) {
        self.apply_feature_profile(profile);
    }

    /// Set maximum number of learned clauses before aggressive reduction (#1609)
    ///
    /// When the number of learned clauses exceeds this limit, the solver
    /// triggers clause reduction more aggressively to prevent memory exhaustion.
    /// Set to `None` to disable the limit (default behavior).
    pub fn set_max_learned_clauses(&mut self, limit: Option<usize>) {
        self.cold.max_learned_clauses = limit;
    }

    /// Set maximum clause database memory in bytes before aggressive reduction (#1609)
    ///
    /// When the clause database memory exceeds this limit, the solver triggers
    /// aggressive clause reduction and arena compaction to reclaim memory.
    /// Set to `None` to disable the limit (default behavior).
    ///
    /// Example: `set_max_clause_db_bytes(Some(500 * 1024 * 1024))` for 500MB limit.
    pub fn set_max_clause_db_bytes(&mut self, limit: Option<usize>) {
        self.cold.max_clause_db_bytes = limit;
    }

    /// Install a deterministic conflict budget backing the SMT-LIB `:rlimit`
    /// option (#8749).
    ///
    /// `target` is an *absolute* conflict count: the solver returns `Unknown`
    /// with reason [`SatUnknownReason::ResourceBudget`] once `num_conflicts()`
    /// reaches it. Pass `None` to clear the budget. Callers that want a budget
    /// relative to the work already done should pass
    /// `Some(self.num_conflicts() + allowance)`.
    ///
    /// Unlike a wall-clock timeout, this bound is machine-independent: the same
    /// formula and random seed stop at the same conflict count on every host,
    /// so verification results are reproducible.
    ///
    /// [`SatUnknownReason::ResourceBudget`]: crate::SatUnknownReason::ResourceBudget
    pub fn set_conflict_budget(&mut self, target: Option<u64>) {
        self.cold.conflict_budget = target;
    }

    /// Get the current absolute conflict budget, or `None` if unbounded.
    #[must_use]
    pub fn conflict_budget(&self) -> Option<u64> {
        self.cold.conflict_budget
    }

    /// Whether the conflict budget (if any) has been reached.
    #[inline]
    pub(crate) fn conflict_budget_exhausted(&self) -> bool {
        self.cold
            .conflict_budget
            .is_some_and(|target| self.num_conflicts >= target)
    }

    /// Install a deterministic decision budget (#ground-determinism).
    ///
    /// `target` is an *absolute* decision count: the solver returns `Unknown`
    /// with reason [`SatUnknownReason::ResourceBudget`] once `num_decisions()`
    /// reaches it. Pass `None` to clear the budget. Callers that want a budget
    /// relative to the work already done should pass
    /// `Some(self.num_decisions() + allowance)`.
    ///
    /// Companion of [`Self::set_conflict_budget`] for decision-heavy /
    /// conflict-light regimes (theory-extension churn makes hundreds of
    /// decisions per conflict, so a conflict budget alone cannot bound its
    /// work deterministically). Like the conflict budget it is machine-
    /// independent: the same formula and random seed stop at the same
    /// decision count on every host. Checked every 1000th decision, at
    /// conflict sites, and at the amortized loop-top, so the stop point
    /// itself is a deterministic function of the search trajectory.
    ///
    /// [`SatUnknownReason::ResourceBudget`]: crate::SatUnknownReason::ResourceBudget
    pub fn set_decision_budget(&mut self, target: Option<u64>) {
        self.cold.decision_budget = target;
    }

    /// Get the current absolute decision budget, or `None` if unbounded.
    #[must_use]
    pub fn decision_budget(&self) -> Option<u64> {
        self.cold.decision_budget
    }

    /// Whether the decision budget (if any) has been reached.
    #[inline]
    pub(crate) fn decision_budget_exhausted(&self) -> bool {
        self.cold
            .decision_budget
            .is_some_and(|target| self.num_decisions >= target)
    }

    /// Whether ANY deterministic resource budget (conflicts or decisions)
    /// has been reached. Shared exhaustion predicate for the deterministic
    /// checkpoints in the solve loops (#ground-determinism).
    #[inline]
    pub(crate) fn resource_budget_exhausted(&self) -> bool {
        self.conflict_budget_exhausted() || self.decision_budget_exhausted()
    }

    /// Remove stale watchers for deleted/garbage clauses from dirty watch lists.
    ///
    /// Only processes literals in the explicit `dirty_watch_list` (#8101).
    /// Cost: O(dirty_lits * avg_dirty_list_len) -- no scan of the full
    /// `num_vars * 2` bitmap. The `dirty_watches` bitmap de-duplicates entries
    /// pushed by concurrent deletion paths.
    /// Reference: CaDiCaL collect.cpp:216-262 (ported with dirty-list extension, #8101).
    pub(super) fn flush_watches(&mut self) {
        for di in 0..self.dirty_watch_list.len() {
            let lit_idx = self.dirty_watch_list[di] as usize;
            // Bitmap de-duplication: skip already-processed duplicates.
            if lit_idx >= self.dirty_watches.len() || !self.dirty_watches[lit_idx] {
                continue;
            }
            self.dirty_watches[lit_idx] = false;
            self.stats.flush_dirty_lits += 1;

            let lit = Literal::from_index(lit_idx);
            let (watch_len, _bc) = self
                .watches
                .copy_to_deferred(lit, &mut self.deferred_watch_list);
            let mut j: usize = 0;
            for i in 0..watch_len {
                let clause_raw = self.deferred_watch_list.clause_raw(i);
                let clause_idx = (clause_raw & !BINARY_FLAG) as usize;

                if clause_idx >= self.arena.len() {
                    continue;
                }
                if self.arena.is_empty_clause(clause_idx) || self.arena.is_garbage(clause_idx) {
                    continue;
                }

                self.deferred_watch_list.set_entry(
                    j,
                    self.deferred_watch_list.blocker_raw(i),
                    clause_raw,
                );
                j += 1;
            }

            self.stats.flush_watches_removed += (watch_len - j) as u64;

            // Two-pointer compaction: j <= watch_len always.
            debug_assert!(
                j <= watch_len,
                "BUG: flush_watches compaction j ({j}) > watch_len ({watch_len}) for lit {lit_idx}"
            );
            self.deferred_watch_list.truncate(j);
            self.watches
                .restore_from_deferred(lit, &mut self.deferred_watch_list);
        }
        self.dirty_watch_list.clear();
    }

    /// Enable or disable Glucose-style EMA restarts.
    ///
    /// When enabled, restarts are triggered based on the exponential moving average
    /// of learned clause LBD values. When disabled, uses Luby sequence restarts.
    ///
    /// CP solvers typically benefit from Luby restarts (set to `false`) because
    /// propagation-derived clauses often have high LBD, causing Glucose restarts
    /// to fire too aggressively.
    pub fn set_glucose_restarts(&mut self, enabled: bool) {
        self.cold.glucose_restarts = enabled;
    }

    /// Set the base restart interval for Luby-sequence restarts (in conflicts).
    ///
    /// Only effective when Glucose restarts are disabled. The actual restart
    /// interval is `base * luby(n)` where `luby(n)` is the Luby sequence.
    /// Default is 100. CP solvers may benefit from larger values (e.g., 250)
    /// to allow more exploration between restarts.
    pub fn set_restart_base(&mut self, base: u64) {
        self.cold.restart_base = base;
    }

    /// Enable the default-off dense-mutex focused restart gate experiment.
    ///
    /// When enabled, only clique-shaped small dense binary-heavy formulas raise
    /// their focused restart gate from the legacy small-dense floor of 10 toward
    /// `max(40, min(100, active_vars / 4))`.
    pub fn set_dense_mutex_focused_restart_gate_experiment_enabled(&mut self, enabled: bool) {
        self.cold.dense_mutex_focused_restart_gate_experiment = enabled;
    }

    /// Return whether the dense-mutex focused restart gate experiment is enabled.
    pub fn dense_mutex_focused_restart_gate_experiment_enabled(&self) -> bool {
        self.cold.dense_mutex_focused_restart_gate_experiment
    }

    /// Record whether variant routing enabled the dense-clique MAB branch experiment.
    pub fn set_dense_clique_mab_branch_route_enabled(&mut self, enabled: bool) {
        self.stats.dense_clique_mab_branch_route_enabled = u64::from(enabled);
        if !enabled {
            self.stats.dense_clique_mab_branch_route_exercised = 0;
        }
    }

    /// Set the initial stabilization phase length (in conflicts).
    ///
    /// Controls how many conflicts the solver spends in its first stabilization
    /// phase before switching modes. The default is 1000 (CaDiCaL `stabinit`).
    /// If search starts focused, this extends focused exploration before the
    /// first stable phase; if a caller starts in stable mode, it extends that
    /// first stable phase before returning to focused mode.
    pub fn set_stable_phase_init(&mut self, conflicts: u64) {
        self.cold.stable_phase_init = conflicts;
        self.cold.stable_phase_length = conflicts;
    }

    /// Set the vivification scheduling interval (in conflicts).
    ///
    /// Minimum spacing between vivification rounds for learned clauses.
    /// Default is 2000. Lower values vivify more frequently.
    pub fn set_vivify_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.vivify.reset_interval(conflicts);
    }

    /// Set the irredundant vivification scheduling interval (in conflicts).
    ///
    /// Minimum spacing between vivification rounds for original clauses.
    /// Default is 5000.
    pub fn set_vivify_irred_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.vivify_irred.reset_interval(conflicts);
    }

    /// Set the subsumption scheduling interval (in conflicts).
    ///
    /// Minimum spacing between forward subsumption rounds.
    /// Default is 20000.
    pub fn set_subsume_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.subsume.reset_interval(conflicts);
    }

    /// Set the probing scheduling interval (in conflicts).
    ///
    /// Minimum spacing between failed-literal probing rounds.
    /// Default is 1000.
    pub fn set_probe_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.probe.reset_interval(conflicts);
    }

    /// Enable true stable-only mode for DIMACS SAT workloads.
    ///
    /// When enabled, the solver starts and stays in stable mode
    /// (EVSIDS + reluctant doubling) across preprocessing resets.
    pub fn set_stable_only(&mut self, enabled: bool) {
        self.cold.mode_lock = if enabled {
            cold::ModeLock::Stable
        } else {
            cold::ModeLock::None
        };
        self.stable_mode = enabled;
        self.cold.stable_mode_start_conflicts = 0;
        self.sync_active_branch_heuristic();
    }

    /// Force equal-effort stable-mode budgeting (the `equiticks` config),
    /// overriding the `--sat-mode-equiticks` env resolution. Used by the
    /// portfolio's Equiticks strategy arm to give the target-phase machinery
    /// more stable airtime on model-finding instances.
    pub fn set_mode_equiticks(&mut self, enabled: bool) {
        self.cold.mode_equiticks_cached = Some(enabled);
    }

    /// Enable the equiticks stable-phase progress gate at the default window,
    /// overriding the `--sat-eqt-progress` env resolution. Only has effect when
    /// equiticks is also active (the gate requires `stable_tick_hardcap > 0`).
    /// Used by the portfolio's Equiticks arm so a still-converging stable phase
    /// is not starved by the halved equal-effort budget (captures 3ef7fa06 /
    /// 4c3001f8 on the parallel track).
    pub fn set_eqt_progress_default(&mut self) {
        self.cold.eqt_progress_cached = Some(EQT_PROGRESS_WINDOW_DEFAULT);
    }

    /// Return whether stable-only search is currently locked on.
    #[cfg(test)]
    pub(crate) fn stable_only_enabled(&self) -> bool {
        self.cold.mode_lock == cold::ModeLock::Stable
    }

    /// Set BVE effort as per-mille of cumulative search propagations.
    pub fn set_bve_effort_permille(&mut self, permille: u64) {
        self.cold.bve_effort_permille = permille;
    }

    /// Set subsumption effort as per-mille of cumulative search propagations.
    pub fn set_subsume_effort_permille(&mut self, permille: u64) {
        self.cold.subsume_effort_permille = permille;
    }

    /// Return the configured BVE effort in per-mille.
    pub fn bve_effort_permille(&self) -> u64 {
        self.cold.bve_effort_permille
    }

    /// Return the configured subsumption effort in per-mille.
    pub fn subsume_effort_permille(&self) -> u64 {
        self.cold.subsume_effort_permille
    }

    /// Enable geometric restart schedule matching Z3's QF_LRA mode.
    ///
    /// Geometric restarts use `next_restart = initial * factor^n` where `n` is
    /// the restart count. Z3 defaults: initial=100, factor=1.1, giving the
    /// sequence 100, 110, 121, 133, 146, ...
    ///
    /// When enabled, this overrides both Glucose-style and Luby restarts.
    /// Also disables CaDiCaL-style stabilization mode switching since geometric
    /// restarts use a fixed schedule independent of clause quality signals.
    pub fn set_geometric_restarts(&mut self, initial: f64, factor: f64) {
        self.cold.geometric_restarts = true;
        self.cold.geometric_initial = initial;
        self.cold.geometric_factor = factor;
    }

    /// Force a specific branching heuristic, independent of restart mode.
    pub fn set_branch_heuristic(&mut self, heuristic: BranchHeuristic) {
        self.cold.branch_selector_mode = BranchSelectorMode::Fixed(heuristic);
        self.switch_branch_heuristic(heuristic);
        self.start_branch_heuristic_epoch();
    }

    /// Enable or disable UCB1 multi-armed-bandit branching selection.
    ///
    /// When enabled, configures AE-Kissat-MAB 2025 winner settings:
    /// - 2-arm variant (EVSIDS + CHB, no VMTF) matching AE-Kissat-MAB
    /// - `DecisionConflictRatio` reward signal (`log2(decisions)/log2(conflicts)`)
    /// - Momentum-adaptive exploration coefficient
    pub fn set_branch_selector_ucb1(&mut self, enabled: bool) {
        self.cold.branch_selector_mode = if enabled {
            BranchSelectorMode::MabUcb1
        } else {
            BranchSelectorMode::LegacyCoupled
        };
        if enabled {
            // AE-Kissat-MAB 2-arm config: {EVSIDS, CHB} only.
            self.cold
                .branch_mab
                .set_active_arms(&crate::mab::AE_KISSAT_MAB_ARMS);
        }
        self.reset_branch_heuristic_selector();
    }

    /// Set the minimum number of conflicts required before scoring a branch-heuristic epoch.
    pub fn set_branch_selector_epoch_min_conflicts(&mut self, conflicts: u64) {
        self.cold.branch_mab.set_epoch_min_conflicts(conflicts);
        self.start_branch_heuristic_epoch();
    }

    /// Set random variable frequency for decisions (Z3-style).
    ///
    /// With probability `freq`, each decision will select a random unassigned
    /// variable instead of the VSIDS/VMTF-highest one. Z3 default for SMT: 0.01
    /// (1% of decisions). Set to 0.0 to disable (default for pure SAT).
    pub fn set_random_var_freq(&mut self, freq: f64) {
        self.cold.random_var_freq = freq.clamp(0.0, 1.0);
    }

    /// Enable or disable chronological backtracking
    ///
    /// When enabled, the solver may backtrack by only one level instead of jumping
    /// to the asserting level, which can help on certain problem classes.
    pub fn set_chrono_enabled(&mut self, enabled: bool) {
        self.chrono_enabled = enabled;
    }

    /// Enable or disable CaDiCaL-style trail reuse for chronological backtracking
    ///
    /// When enabled, the solver uses trail reuse heuristic to find the best
    /// variable above the jump level and backtrack only to that level, preserving
    /// more of the useful trail state. Only active in stable mode.
    pub fn set_chrono_reuse_trail(&mut self, enabled: bool) {
        self.chrono_reuse_trail = enabled;
    }

    /// Mark extension-derived theory lemmas as trusted transforms (#4533).
    ///
    /// When `true`, theory lemmas added via `add_theory_lemma()` and
    /// `add_theory_propagation()` are classified as
    /// `ProofAddKind::TrustedTransform` instead of `ProofAddKind::Axiom`. This
    /// is correct for extensions like XOR Gauss-Jordan that consume original
    /// clauses and produce logically equivalent theory lemmas. In LRAT mode,
    /// transforms without explicit chains remain suppressed and make a terminal
    /// UNSAT fail closed to Unknown because LRAT cannot encode this trust tag.
    ///
    /// The `solve_with_preprocessing_extension` path sets this automatically
    /// via `prepare_preprocessing_extension`. This method is for callers that
    /// use `solve_with_extension` directly (e.g., `ExtDimacsFormula::solve()`,
    /// the DIMACS CLI XOR path) and know their extension produces trusted lemmas.
    ///
    /// When `false` (default), theory lemmas are treated as external axioms
    /// and LRAT mode is blocked once any theory lemma is added.
    pub fn set_extension_trusted_lemmas(&mut self, trusted: bool) {
        self.cold.extension_trusted_lemmas = trusted;
    }

    /// Set the initial phase for all variables.
    ///
    /// If `phase` is `true`, variables will initially be assigned positive.
    /// If `phase` is `false`, variables will initially be assigned negative.
    pub(crate) fn set_initial_phase(&mut self, phase: bool) {
        self.phase.fill(if phase { 1 } else { -1 });
    }

    /// Set the preferred phase for a specific variable
    ///
    /// This is useful for guiding the search - for example, in LIA solving,
    /// when splitting on an integer variable with fractional value, we can
    /// set the preferred phase to try the closer integer first.
    ///
    /// # Arguments
    /// * `var` - The variable to set phase for
    /// * `phase` - `true` for positive polarity, `false` for negative
    pub fn set_var_phase(&mut self, var: Variable, phase: bool) {
        let idx = var.index();
        if idx < self.num_vars {
            self.phase[idx] = if phase { 1 } else { -1 };
        }
    }

    /// Get the forced phase hint for a variable, if one has been set.
    ///
    /// Returns `None` if no phase hint was set for this variable.
    /// Used by tests to verify that `set_var_phase` was called correctly.
    pub fn var_phase(&self, var: Variable) -> Option<bool> {
        let idx = var.index();
        if idx < self.num_vars {
            match self.phase[idx] {
                1 => Some(true),
                -1 => Some(false),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Get the VSIDS activity score for a variable.
    ///
    /// Returns the current activity score used by the decision heuristic.
    /// Higher scores indicate variables involved in more recent conflicts.
    /// Used by the DPLL(T) theory layer to prioritize branching on
    /// high-activity theory atoms (#8420).
    pub fn activity(&self, var: Variable) -> f64 {
        if var.index() < self.num_vars {
            self.vsids.activity(var)
        } else {
            0.0
        }
    }

    /// Bump the VSIDS activity of a variable.
    ///
    /// This increases the variable's priority in the decision heuristic,
    /// making it more likely to be selected as the next branching variable.
    /// Used by ay-cp to boost objective variable literals after finding
    /// a solution during optimization, biasing the search toward improving
    /// the objective.
    pub fn bump_variable_activity(&mut self, var: Variable) {
        if var.index() < self.num_vars {
            self.vsids.bump(var, &self.vals, true);
            self.vsids.bump(var, &self.vals, false);
        }
    }

    /// Bump the VSIDS activity of multiple theory variables (#8421).
    ///
    /// Batch variant of `bump_variable_activity` for theory-conflict-driven
    /// bumps. Theory atoms appearing in conflicts or propagations should be
    /// prioritized in the SAT decision heuristic so the solver focuses on
    /// contentious theory atoms. This matches Z3's `update_activity()` calls
    /// in the theory conflict handling path.
    pub fn bump_theory_vars(&mut self, vars: &[Variable]) {
        let use_vsids = self.active_branch_heuristic != BranchHeuristic::Vmtf;
        for &var in vars {
            if var.index() < self.num_vars {
                self.vsids.bump(var, &self.vals, use_vsids);
            }
        }
    }

    /// Set the random seed for variable selection tie-breaking
    ///
    /// This affects the order of variables with equal VSIDS scores.
    /// Different seeds can lead to different search paths.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.vsids.set_random_seed(seed);
    }

    /// Return the current random seed for variable selection tie-breaking.
    #[must_use]
    pub fn random_seed(&self) -> u64 {
        self.vsids.random_seed()
    }

    /// Estimate memory usage of the solver (in bytes)
    /// Returns a breakdown of live heap-backed buffers plus the inline solver
    /// shell. Tracks the current hot/cold split layout so `#5090` regressions
    /// show up in tests.
    /// Clause storage is arena allocated, with header and literal buffers.
    /// Clauses have no individual heap allocations.
    /// Reusable scratch and proof buffers are charged by retained capacity, even
    /// when their logical length is zero.
    #[cfg(test)]
    pub(crate) fn memory_stats(&self) -> MemoryStats {
        fn packed_bool_vec_bytes(capacity: usize) -> usize {
            capacity.div_ceil(8)
        }
        let solver_shell = size_of::<Self>();

        let var_data = self.vals.capacity() * size_of::<i8>()
            + self.var_data.capacity() * size_of::<VarData>()
            + self.phase.capacity() * size_of::<i8>()
            + self.target_phase.capacity() * size_of::<i8>()
            + self.best_phase.capacity() * size_of::<i8>();

        let vsids = self.vsids.buffer_bytes();

        let minimize_bytes = self.min.minimize_flags.capacity() * size_of::<u8>()
            + self.min.minimize_to_clear.capacity() * size_of::<usize>()
            + self.min.level_seen.capacity() * size_of::<minimization_state::LevelSeen>()
            + self.min.level_seen_to_clear.capacity() * size_of::<u32>()
            + self.min.lrat_to_clear.capacity() * size_of::<usize>()
            + self.min.lrat_original_learned_buf.capacity() * size_of::<Literal>()
            + self.min.minimize_level_seen.capacity() * size_of::<minimization_state::LevelSeen>()
            + self.min.minimize_levels_to_clear.capacity() * size_of::<u32>();
        let conflict = self.conflict.buffer_bytes()
            + self.reason_clause_marks.capacity() * size_of::<u32>()
            + self.bump_order_sort_buf.capacity() * size_of::<(u64, usize)>()
            + self.glue_stamp.capacity() * size_of::<u32>()
            + self.shrink_stamp.capacity() * size_of::<u32>()
            + minimize_bytes;

        let arena = self.arena.memory_bytes();
        let total_literals = self.arena.active_literals();

        let watches = self.watches.heap_bytes()
            + self.deferred_watch_list.capacity() * size_of::<u32>()
            + self.deferred_replacement_watches.capacity() * size_of::<(Literal, Watcher)>();

        let trail = self.trail.capacity() * size_of::<Literal>()
            + self.trail_lim.capacity() * size_of::<usize>()
            + self.cold.learned_clause_trail.capacity() * size_of::<usize>();

        let support = self.cold.e2i.capacity() * size_of::<u32>()
            + self.cold.i2e.capacity() * size_of::<u32>()
            + self.var_lifecycle.heap_bytes()
            + packed_bool_vec_bytes(self.phase_init.walk_prev_phase.capacity())
            + self.cold.capability_ledger.heap_bytes()
            + self
                .cold
                .solution_witness
                .as_ref()
                .map_or(0, |witness| witness.capacity() * size_of::<Option<bool>>());
        let clause_ids = self.cold.clause_ids.capacity() * size_of::<u64>()
            + self.cold.bcp_learned_clause_birth_conflicts.capacity() * size_of::<u64>()
            + self.unit_proof_id.capacity() * size_of::<u64>()
            + self.unit_proof_sign.capacity() * size_of::<i8>()
            + self.pending_theory_unit_proof_ids.capacity() * size_of::<(ClauseRef, u64)>()
            + self.cold.level0_proof_id.capacity() * size_of::<u64>()
            + self.cold.level0_proof_sign.capacity() * size_of::<i8>()
            + self.cold.lrat_level0_unit_materialize_pinned.capacity() * size_of::<usize>()
            + self.cold.scope_selectors.capacity() * size_of::<Variable>()
            + self.cold.root_satisfied_saved.capacity() * size_of::<Vec<Literal>>()
            + self
                .cold
                .root_satisfied_saved
                .iter()
                .map(|clause| clause.capacity() * size_of::<Literal>())
                .sum::<usize>();

        let inprocessing = packed_bool_vec_bytes(self.subsume_dirty.capacity())
            + packed_bool_vec_bytes(self.dirty_watches.capacity())
            + self.dirty_watch_list.capacity() * size_of::<u32>()
            + self.probe_parent.capacity() * size_of::<Option<Literal>>()
            + self.cold.freeze_counts.capacity() * size_of::<u32>()
            + self.cold.factor_candidate_marks.capacity() * size_of::<u8>()
            + packed_bool_vec_bytes(self.cold.scope_selector_set.capacity())
            + packed_bool_vec_bytes(self.cold.was_scope_selector.capacity())
            + self.hbr_lits.capacity() * size_of::<Literal>()
            + self.tiers.tier_usage[0].capacity() * size_of::<u64>()
            + self.tiers.tier_usage[1].capacity() * size_of::<u64>()
            + self.inproc.preprocess_transactions.heap_bytes();

        let reconstruction = self.inproc.reconstruction.memory_bytes();

        MemoryStats {
            solver_shell,
            num_vars: self.num_vars,
            num_clauses: self.arena.num_clauses(),
            total_literals,
            var_data,
            vsids,
            conflict,
            arena,
            watches,
            trail,
            support,
            clause_ids,
            original_ledger: self.cold.original_ledger.heap_bytes(),
            inprocessing,
            reconstruction,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn persistent_solver_interrupt_handle_is_rebound_and_cleared() {
        let mut solver = Solver::new(0);
        let stale = Arc::new(AtomicBool::new(true));
        solver.set_interrupt_handle(Some(stale));
        assert!(solver.is_interrupted());

        let current = Arc::new(AtomicBool::new(false));
        solver.set_interrupt_handle(Some(Arc::clone(&current)));
        assert!(!solver.is_interrupted());
        current.store(true, Ordering::Relaxed);
        assert!(solver.is_interrupted());

        solver.set_interrupt_handle(None);
        assert!(!solver.is_interrupted());
    }

    #[test]
    fn test_apply_feature_profile_lrat_clamps_destructive_transforms() {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 0);
        let mut solver = Solver::with_proof_output(4, proof);
        let profile = crate::InprocessingFeatureProfile {
            symmetry: true,
            ..crate::InprocessingFeatureProfile::default()
        };

        solver.apply_feature_profile(&profile);

        assert!(!solver.is_bve_enabled(), "BVE must be disabled for LRAT");
        assert!(
            !solver.is_factor_enabled(),
            "factor must be disabled for LRAT"
        );
        assert!(!solver.is_sbva_enabled(), "SBVA must be disabled for LRAT");
        assert!(
            !solver.is_sweep_enabled(),
            "sweep must be disabled for LRAT"
        );
        assert!(
            !solver.is_symmetry_enabled(),
            "symmetry must be disabled for LRAT"
        );
    }

    #[test]
    fn test_apply_feature_profile_drat_keeps_proof_incomplete_transforms_clamped() {
        let proof = ProofOutput::drat_text(Vec::<u8>::new());
        let mut solver = Solver::with_proof_output(4, proof);
        let profile = crate::InprocessingFeatureProfile {
            congruence: true,
            decompose: true,
            sweep: true,
            factor: true,
            symmetry: true,
            ..Default::default()
        };

        solver.apply_feature_profile(&profile);

        assert!(
            !solver.is_sweep_enabled(),
            "sweep must stay disabled in DRAT proof mode"
        );
        assert!(
            solver.is_decompose_enabled(),
            "decompose is DRAT-open since 2026-07-09 (registry Decompose \
             drat=true; externally verified via dpr-trim + cake_lpr)"
        );
        assert!(
            solver.is_congruence_enabled(),
            "congruence is DRAT-open since 2026-07-10 (wf_ff5991a1: registry \
             Congruence drat=true; externally verified via dpr-trim + cake_lpr; \
             kill-switch --sat-no-drat-subst)"
        );
        assert!(
            solver.is_factor_enabled(),
            "factor remains available in DRAT proof mode"
        );
        assert!(
            !solver.is_symmetry_enabled(),
            "symmetry must stay disabled in DRAT proof mode"
        );
    }

    #[test]
    fn test_set_symmetry_enabled_clamps_proof_modes() {
        let mut plain_solver = Solver::new(4);
        plain_solver.set_symmetry_enabled(true);
        assert!(plain_solver.is_symmetry_enabled());

        let mut drat_solver =
            Solver::with_proof_output(4, ProofOutput::drat_text(Vec::<u8>::new()));
        drat_solver.set_symmetry_enabled(true);
        assert!(
            !drat_solver.is_symmetry_enabled(),
            "DRAT proof mode must not reopen symmetry"
        );

        let mut lrat_solver =
            Solver::with_proof_output(4, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
        lrat_solver.set_symmetry_enabled(true);
        assert!(
            !lrat_solver.is_symmetry_enabled(),
            "LRAT proof mode must not reopen symmetry"
        );
    }
}
