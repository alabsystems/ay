// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main solve loop and proof finalization.
//!
//! Split into submodules for maintainability (#4933, #5142):
//! - `analyze`: Shared conflict-analysis skeleton (chrono BT + learn + enqueue)
//! - `theory_callback`: Theory/extension callback abstraction
//! - `theory_entry`: Theory closure entry points
//! - `extension_entry`: Extension-mode entry points and init
//! - `theory_backend`: Unified CDCL backend loop for theory/extension
//! - `diagnostics`: TLA tracing and diagnostic emission
//! - `inprocessing_schedule`: Inprocessing pass scheduling facade
//! - `inprocessing_maintenance`: Garbage drain and gate checks
//! - `inprocessing_equivalence`: Equivalence/probing front-half passes
//! - `inprocessing_elimination`: Elimination back-half passes
//! - `inprocessing_round_end`: Round-end invariant checks and telemetry
//! - `finalize`: Result declaration and proof finalization

mod analyze;
mod diagnostics;
mod ext_conflict;
mod extension_entry;
mod finalize;
mod finalize_sat;
mod finalize_unsat;
mod ic3;
#[cfg(test)]
mod ic3_tests;
mod inprocessing_elimination;
mod inprocessing_incremental;
mod inprocessing_maintenance;
mod inprocessing_schedule;
#[cfg(test)]
mod tests;
mod theory_backend;
mod theory_callback;
mod theory_entry;

use super::*;
impl Solver {
    /// Run one inprocessing pass with scoped diagnostic tracing and timing.
    #[inline]
    pub(super) fn run_timed_diagnostic_inprocessing_pass<T>(
        &mut self,
        pass: DiagnosticPass,
        run: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let start = ay_core::time::Instant::now();
        let yield_before = self.inprocessing_yield_signal(pass);
        self.stats.record_inprocessing_run(pass);
        self.set_diagnostic_pass(pass);
        let result = run(self);
        self.clear_diagnostic_pass();
        let elapsed_ns = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        self.stats.record_inprocessing_time(pass, elapsed_ns);
        if self.inprocessing_yield_signal(pass) > yield_before {
            self.stats.record_inprocessing_yield(pass);
        }
        result
    }

    #[inline]
    pub(super) fn run_probe_inprocessing_pass(&mut self) -> bool {
        let start = ay_core::time::Instant::now();
        let yield_before = self.inprocessing_yield_signal(DiagnosticPass::Probe);
        self.stats.record_inprocessing_run(DiagnosticPass::Probe);
        self.set_diagnostic_pass(DiagnosticPass::Probe);
        let probe_unsat = self.probe();
        self.clear_diagnostic_pass();
        let elapsed_ns = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        self.stats
            .record_inprocessing_time(DiagnosticPass::Probe, elapsed_ns);
        if self.inprocessing_yield_signal(DiagnosticPass::Probe) > yield_before {
            self.stats.record_inprocessing_yield(DiagnosticPass::Probe);
        }
        probe_unsat
    }

    #[inline]
    pub(super) fn run_intree_inprocessing_pass(&mut self) -> bool {
        let yield_before = self.inprocessing_yield_signal(DiagnosticPass::Probe);
        self.stats.record_inprocessing_run(DiagnosticPass::Probe);
        let intree_unsat = self.intree_probe();
        if self.inprocessing_yield_signal(DiagnosticPass::Probe) > yield_before {
            self.stats.record_inprocessing_yield(DiagnosticPass::Probe);
        }
        intree_unsat
    }

    #[inline]
    fn inprocessing_yield_signal(&self, pass: DiagnosticPass) -> u64 {
        match pass {
            DiagnosticPass::Subsume => {
                let stats = self.inproc.subsumer.stats();
                stats
                    .forward_subsumed
                    .saturating_add(stats.strengthened_clauses)
                    .saturating_add(stats.strengthened_literals)
            }
            DiagnosticPass::Probe => {
                let stats = self.inproc.prober.stats();
                stats
                    .failed
                    .saturating_add(stats.hbr_redundant)
                    .saturating_add(stats.hbr_subsumed_deleted)
                    .saturating_add(self.cold.intree_failed)
                    .saturating_add(self.cold.intree_vars_set)
            }
            DiagnosticPass::Backbone => self
                .stats
                .backbone_binary_units
                .saturating_add(self.fixed_count as u64),
            DiagnosticPass::Congruence => {
                let stats = self.inproc.congruence.stats();
                stats
                    .equivalences_found
                    .saturating_add(stats.congruence_subsumed)
                    .saturating_add(stats.literals_rewritten)
                    .saturating_add(stats.clauses_modified)
            }
            DiagnosticPass::Decompose => {
                let stats = self.decompose_stats();
                stats.substituted.saturating_add(stats.units)
            }
            DiagnosticPass::HTR => {
                let stats = self.htr_stats();
                stats
                    .ternary_resolvents
                    .saturating_add(stats.binary_resolvents)
            }
            DiagnosticPass::TransRed => {
                let stats = self.inproc.transred_engine.stats();
                stats
                    .clauses_removed
                    .saturating_add(stats.failed_literals)
                    .saturating_add(self.fixed_count as u64)
            }
            DiagnosticPass::Vivify => {
                let stats = self.inproc.vivifier.stats();
                stats
                    .clauses_strengthened
                    .saturating_add(stats.inline_subsumed)
                    .saturating_add(stats.analysis_subsumed)
                    .saturating_add(stats.literals_removed)
                    .saturating_add(stats.clauses_satisfied)
            }
            DiagnosticPass::Sweep => {
                // Observability only (wf_755ac432): surface real sweep work so
                // `inproc_sweep_yields` stops reading a phantom 0. The prior arm
                // fell through to `_ => 0`, which caused a whole session to
                // misdiagnose a healthy sweep (127 equivalences, 1136 clauses
                // rewritten on 3f67f676) as "yields nothing". Behavior-neutral:
                // the only cross-pass consumer of `inprocessing_pass_yields` is
                // `round_pass_yields` (inprocessing_schedule.rs), read solely
                // inside the `lrat_zero_yield_scale` branch gated on
                // `lrat_enabled && proof_manager.is_some()`. Sweep is
                // proof-clamped off under every proof mode
                // (proof_capability.rs: ProofTransform::Sweep => false), so its
                // yield can never be observed by that branch — the value is
                // identical in all reachable states.
                let stats = self.inproc.sweeper.stats();
                stats
                    .kitten_equivalences
                    .saturating_add(stats.kitten_backbone)
                    .saturating_add(stats.clauses_rewritten)
            }
            _ => 0,
        }
    }

    /// Convert an assumption-path model to a `SatResult`.
    ///
    /// Always-on model-length validation (#5749 Phase 5): if the model length
    /// does not match `user_num_vars`, returns `Unknown` with
    /// `InvalidSatModel` instead of producing a bogus `Sat`.
    /// The model has already been verified by `finalize_sat_model` inside
    /// `solve_with_assumptions_impl`, so a length mismatch here indicates a
    /// corruption bug in the type-conversion layer, not a solver bug.
    #[inline]
    fn sat_from_assume_model(&mut self, model: Vec<bool>, context: &'static str) -> SatResult {
        if model.len() != self.user_num_vars {
            tracing::error!(
                context,
                model_len = model.len(),
                user_num_vars = self.user_num_vars,
                "sat_from_assume_model: model length mismatch"
            );
            return self.declare_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        // #7912: verify the finalized external model against all original clauses.
        // NOTE: debug_assert_sat_result_model removed — reads stale self.vals
        // after walk/ProbSAT. See finalize_sat.rs declare_sat_from_model comment.
        // Domain-restricted SAT (#8473): skip external verification when active
        // domain is set. The model only satisfies domain-restricted clauses.
        #[cfg(debug_assertions)]
        if self.active_domain.is_none() {
            debug_assert!(
                self.verify_external_model(&model),
                "BUG: Invalid SAT model in sat_from_assume_model ({context})"
            );
        }
        SatResult::Sat(model)
    }

    /// Convert an assumption-path model to an `AssumeResult`.
    ///
    /// Always-on model-length validation (#5749 Phase 5): if the model length
    /// does not match `user_num_vars`, returns `Unknown` instead of `Sat`.
    #[inline]
    pub(super) fn assume_sat_from_assume_model(
        &mut self,
        model: Vec<bool>,
        context: &'static str,
    ) -> AssumeResult {
        if model.len() != self.user_num_vars {
            tracing::error!(
                context,
                model_len = model.len(),
                user_num_vars = self.user_num_vars,
                "assume_sat_from_assume_model: model length mismatch"
            );
            return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        // #7912: verify the finalized external model against all original clauses.
        // NOTE: debug_assert_sat_result_model removed — reads stale self.vals
        // after walk/ProbSAT. See finalize_sat.rs declare_sat_from_model comment.
        // Domain-restricted SAT (#8473): skip external verification when active
        // domain is set. The model only satisfies domain-restricted clauses.
        #[cfg(debug_assertions)]
        if self.active_domain.is_none() {
            debug_assert!(
                self.verify_external_model(&model),
                "BUG: Invalid SAT model in assume_sat_from_assume_model ({context})"
            );
        }
        AssumeResult::Sat(model)
    }

    /// Solve the formula
    pub fn solve(&mut self) -> VerifiedSatResult {
        let result = self.solve_raw();
        self.maybe_write_fmla_learned_lrat_dry_run_proof_artifact_from_env();
        VerifiedSatResult::from_validated(result)
    }

    /// Internal solve returning raw `SatResult`.
    fn solve_raw(&mut self) -> SatResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY across solve() calls —
        // once the solver has produced an invalid SAT model in this session,
        // learned clauses derived afterwards are suspect, so any later UNSAT
        // must be downgraded to Unknown. Do NOT reset here.

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions(|| false);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        let assumptions = self.compose_scope_assumptions(&[]);

        let result = match self.solve_with_assumptions_impl(
            &assumptions,
            None::<&fn() -> bool>,
            None,
            None,
            None,
        ) {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve() scope-selector path")
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    /// Solve the formula with an interrupt callback
    ///
    /// The callback is checked periodically (every ~100 conflicts). If it returns
    /// `true`, solving is interrupted and `SatResult::Unknown` is returned.
    ///
    /// This is useful for parallel portfolio solving where multiple solvers run
    /// concurrently and can be stopped when one finds a solution.
    pub fn solve_interruptible<F>(&mut self, should_stop: F) -> VerifiedSatResult
    where
        F: Fn() -> bool,
    {
        let result = self.solve_interruptible_raw(should_stop);
        self.maybe_write_fmla_learned_lrat_dry_run_proof_artifact_from_env();
        VerifiedSatResult::from_validated(result)
    }

    /// Internal interruptible solve returning raw `SatResult`.
    fn solve_interruptible_raw<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY — see solve_raw() comment.

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions(should_stop);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        let assumptions = self.compose_scope_assumptions(&[]);

        // Use the interruptible variant so should_stop is respected even
        // when scope_selectors produce assumptions (#3237).
        let result = match self.solve_with_assumptions_impl(
            &assumptions,
            Some(&should_stop),
            None,
            None,
            None,
        ) {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve_interruptible() scope-selector path")
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    /// Solve with phase hints for scoped (push/pop) solving (#8423).
    ///
    /// When scope selectors are active (nonzero scope depth), the normal
    /// `solve_with_extension` path rejects extensions. This method passes
    /// the extension's `suggest_decision` and `suggest_phase` methods through
    /// to the assumption-based CDCL loop, enabling theory-guided branching
    /// in incremental solving with push/pop.
    ///
    /// When scope selectors are empty, falls back to normal solving.
    pub fn solve_with_phase_hints(&mut self, phase_hints: &dyn Extension) -> VerifiedSatResult {
        let result = self.solve_with_phase_hints_raw(phase_hints);
        self.maybe_write_fmla_learned_lrat_dry_run_proof_artifact_from_env();
        VerifiedSatResult::from_validated(result)
    }

    /// Internal phase-hint solve returning raw `SatResult`.
    fn solve_with_phase_hints_raw(&mut self, phase_hints: &dyn Extension) -> SatResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY — see solve_raw() comment.

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            // No scoping — use the full extension path.
            let result = self.solve_no_assumptions(|| false);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        let assumptions = self.compose_scope_assumptions(&[]);

        let result = match self.solve_with_assumptions_impl(
            &assumptions,
            None::<&fn() -> bool>,
            None,
            Some(phase_hints),
            None,
        ) {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve_with_phase_hints() scope-selector path")
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    /// Initialize solver state for a new solve call.
    ///
    /// Resets search state, sets up watches, processes initial unit clauses,
    /// and runs initial propagation. Returns `Some(result)` if the formula
    /// is trivially solved during initialization (empty formula, unit
    /// propagation conflict), `None` if the CDCL loop should proceed.
    fn init_solve(&mut self) -> Option<SatResult> {
        // Record wall-clock start time for progress and observer reporting (#8155).
        if self.cold.progress_enabled || self.has_observer() {
            self.cold.solve_start_time = Some(ay_core::time::Instant::now());
            self.cold.last_progress_time = None;
        }

        // On second+ solve, disable destructive inprocessing (#5031).
        if self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;
        self.reset_search_state();
        // CaDiCaL: init_solve must start at decision level 0
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: init_solve entered at decision level {}",
            self.decision_level,
        );

        tracing::info!(
            num_vars = self.num_vars,
            num_clauses = self.arena.num_clauses(),
            proof_mode = self.proof_manager.is_some(),
            diagnostic_mode = self.cold.diagnostic_trace.is_some(),
            "solve: start"
        );

        // Dump encoding before any preprocessing (#8323).
        self.maybe_dump_encoding();

        self.tla_trace_step(CdclTraceState::Propagating, None);

        if self.arena.is_empty() {
            self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
            return Some(self.declare_sat_from_current_assignment());
        }

        // Track irredundant clause count for density-aware protection in
        // reduce_db (#8633). Use irredundant_count() not num_clauses() to
        // avoid inflating the density ratio with learned clauses.
        self.num_original_clauses = self.arena.irredundant_count();
        self.cold.original_clause_boundary = self.arena.len();
        self.install_and_apply_sat_whole_loop_guard_at_solver_start();

        // Initialize streaming UNSAT core bitmap (#8250).
        // Sized to cover all original clause IDs (1-based: ID 1..=N).
        // Each conflict analysis marks original antecedent clause IDs,
        // so the core is available immediately at UNSAT.
        let num_originals = self.cold.next_original_clause_id.saturating_sub(1);
        if num_originals > 0 {
            self.cold.streaming_core_num_originals = num_originals;
            self.cold.streaming_core = Some(vec![false; num_originals as usize]);
        } else {
            self.cold.streaming_core_num_originals = 0;
            self.cold.streaming_core = None;
        }

        // Classify formula for jump reasons gate (#8034).
        // Kissat classify.c: bigbigfraction=990 → enable when >= 99.0% binary.
        // Only enabled when LRAT is disabled (LRAT requires clause reasons for
        // forward resolution chain hints — jump reasons lose the clause ID).
        if !self.cold.lrat_enabled && self.num_original_clauses > 0 {
            let binary_count = self
                .arena
                .indices()
                .filter(|&off| self.arena.len_of(off) == 2)
                .count();
            let ratio = binary_count as f64 / self.num_original_clauses as f64;
            self.cold.jump_reasons_enabled = ratio >= 0.99;
        }

        self.initialize_watches();

        if let Some(conflict_ref) = self.process_initial_clauses() {
            // Contradictory unit clauses — collect LRAT resolution chain
            // from the conflict clause so the empty-clause step has proper hints.
            self.record_level0_conflict_chain(conflict_ref);
            return Some(self.declare_unsat());
        }

        let trail_before = self.trail.len();
        let init_conflict = self.search_propagate();
        if let Some(conflict_ref) = init_conflict {
            // Record the BCP resolution chain for proof reconstruction (#4176).
            // Standard analyze_conflict uses 1UIP which assumes decision_level > 0.
            // At level 0, use a dedicated chain recorder that just collects the
            // clause IDs involved in the BCP conflict.
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

    pub(super) fn solve_no_assumptions<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY — see solve_raw() comment.

        if let Some(result) = self.init_solve() {
            return result;
        }

        // The Fmla LRAT preflight route needs original-clause LRAT source IDs
        // before preprocessing can delete them from the checker-visible hint
        // set. The existing inprocessing-scheduler hook remains as a fallback;
        // the route's consumed bit keeps this exactly-once.
        let mut startup_passes_run = Vec::new();
        self.run_fmla_decompose_lrat_preflight_route(&mut startup_passes_run);

        // Early lucky phase at preprocessing entry (kissat lucky.c): try the
        // trivial-assignment probes (all-true/all-false constants, then
        // forward/backward polarity sweeps with full BCP) BEFORE any expensive
        // preprocessing pass. Kissat solves main-track 00fd8ac9 (23.4M vars,
        // 63M clauses) this way with ZERO search — the forward-false sweep
        // completes in parse-dominated time. Only fires on formulas too large
        // for the legacy post-preprocess lucky gate below; each probe is
        // bounded by a size-proportional wall budget and every lucky SAT is
        // re-verified by the model gate. Kill switch: AY_AB_LUCKY=0.
        if let Some(result) = self.try_lucky_phases_at_preprocess_entry() {
            return result;
        }
        if self.is_interrupted() {
            return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
        }

        // Run initial preprocessing (BVE, probing, subsumption)
        // This can eliminate variables and simplify clauses before CDCL
        if self.cold.preprocess_enabled {
            let t0 = ay_core::time::Instant::now();
            let unsat = self.preprocess();
            self.stats.preprocess_time_ns =
                t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
            if unsat {
                return self.declare_unsat();
            }
        }

        // Reinitialize watches after preprocessing (clauses may have been modified)
        // Must clear watches first to avoid duplicates from pre-preprocessing state.
        //
        // Optimization: when BVE ran and rebuilt watches as its last step, and no
        // subsequent pass modified clause literals in-place (e.g., quick-mode on
        // large instances), skip the redundant O(clauses) watch rebuild. On
        // shuffling-2 (4.7M clauses), this saves ~6 seconds of double watch init.
        if self.cold.preprocess_enabled {
            // #8496: Ensure all clauses containing eliminated/substituted
            // variables are cleaned up, regardless of how preprocess() exited
            // (normal completion, timeout, or interrupt). Preprocessing may
            // return early via timeout checks after passes that eliminate
            // variables (decompose, sweep, BVE), leaving stale clauses in
            // the arena. This must run before initialize_watches() to prevent
            // watching dead clauses that reference eliminated variables.
            let finalize_deleted = self.finalize_preprocess_clause_cleanup();
            // #8496: When finalize deleted any clauses, force a full watch
            // rebuild. arena.delete() on pending-garbage clauses zeroes
            // lit_len and sets GARBAGE_BIT, but does NOT remove their stale
            // watch entries. The binary-clause BCP path does not check
            // garbage bits (it relies on eager watch unlinking at deletion
            // time). A full watches.clear() + initialize_watches() is the
            // only safe way to purge all stale entries.
            if finalize_deleted {
                self.cold.preprocess_watches_valid = false;
            }
            if !self.cold.preprocess_watches_valid {
                self.watches.clear();
                self.initialize_watches();
            }
            // Reset qhead so all level-0 assignments re-propagate through
            // current watches (#1818). Needed even when watches are valid
            // because backbone/BVE may have enqueued new units.
            self.qhead = 0;

            // Re-propagate after watch reinitialization (#1464)
            // BVE may have added resolvents that are unit/conflict under current assignment.
            // Without this propagation, the solver may miss conflicts or unit implications.
            {
                let trail_before = self.trail.len();
                // Post-preprocess: no probing/vivify — search variant.
                if let Some(conflict_ref) = self.search_propagate() {
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat();
                }
                if self.cold.tla_trace.is_some() && self.trail.len() > trail_before {
                    self.tla_trace_step(
                        CdclTraceState::Propagating,
                        Some(CdclTraceAction::Propagate),
                    );
                }
            }

            // Disable for subsequent calls — prevents double preprocessing if a
            // later call goes through solve_with_assumptions_impl().
            self.cold.preprocess_enabled = false;

            // Use the post-preprocessing irredundant count for scheduling.
            // arena.num_clauses() counts deleted slots left behind by BVE and
            // subsumption, which overstates the live problem size.
            self.num_original_clauses = self.arena.active_clause_count();

            // Density-aware restart tuning (#8466): on small dense formulas
            // (clique_n2_k10: 180 vars, 3160 clauses, density 17.5), the
            // Glucose EMA restart trigger fires pathologically because LBD
            // quality is structurally poor (83% LBD >= 11). This causes
            // 93K restarts vs Kissat's 14K. The fix:
            //
            // 1. Disable stable-mode EMA entirely for small dense formulas.
            //    CaDiCaL's stable mode uses ONLY reluctant doubling. AY's
            //    stable-mode EMA was an intentional addition (#7998) but is
            //    counterproductive when all conflicts have high LBD.
            //
            // 2. Raise the focused-mode minimum restart interval from 2 to
            //    10 conflicts. With uniformly bad LBD, the EMA always fires,
            //    so the interval gate is the only thing preventing restarts
            //    every 3 conflicts. Raising to 10 matches Kissat's effective
            //    focused-mode restart frequency on this benchmark.
            //
            // Threshold: < 1000 active vars AND clause/var density > 10.
            // This catches graph coloring, pigeon hole, and similar dense
            // combinatorial formulas while leaving medium/large industrial
            // instances untouched.
            {
                let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars());
                let active_cls = self.arena.active_clause_count();
                let density = if active_vars > 0 {
                    active_cls as f64 / active_vars as f64
                } else {
                    0.0
                };
                let mut dense_mutex_computed_gate = 0;
                if self.cold.dense_mutex_focused_restart_gate_experiment {
                    let active_binary = self
                        .arena
                        .indices()
                        .filter(|&idx| self.arena.is_active(idx) && self.arena.len_of(idx) == 2)
                        .count();
                    let runtime_candidate = Self::dense_mutex_focused_restart_candidate(
                        active_vars,
                        active_cls,
                        active_binary,
                    );
                    let admitted_formula_gate = if self.user_num_vars > 0 {
                        Self::dense_mutex_focused_restart_gate(self.user_num_vars)
                    } else {
                        0
                    };
                    if runtime_candidate {
                        dense_mutex_computed_gate =
                            Self::dense_mutex_focused_restart_gate(active_vars)
                                .max(admitted_formula_gate);
                    } else if admitted_formula_gate != 0 {
                        // The route was admitted from the original formula
                        // features. Preprocessing can satisfy or rewrite away
                        // the live dense-binary shape before this snapshot, so
                        // preserve the admitted startup gate while reporting
                        // the post-preprocess runtime predicate separately.
                        dense_mutex_computed_gate = admitted_formula_gate;
                    }
                    self.stats.dense_mutex_focused_restart_runtime_checked += 1;
                    self.stats.dense_mutex_focused_restart_active_vars = active_vars as u64;
                    self.stats.dense_mutex_focused_restart_active_clauses = active_cls as u64;
                    self.stats.dense_mutex_focused_restart_active_binary_clauses =
                        active_binary as u64;
                    self.stats.dense_mutex_focused_restart_runtime_candidate =
                        u64::from(runtime_candidate);
                    self.stats.dense_mutex_focused_restart_previous_gate =
                        self.cold.focused_restart_gate;
                    self.stats.dense_mutex_focused_restart_computed_gate =
                        dense_mutex_computed_gate;
                }
                if active_vars < 1000 && density > 10.0 {
                    // Small dense formulas (clique_n2_k10, pigeon hole):
                    // disable stable-mode EMA to prevent restart storms
                    // (#8135, #8466). Pure reluctant doubling is correct
                    // for these combinatorial instances.
                    self.cold.stable_ema_gate = u64::MAX;
                    // Default behavior keeps the legacy 10-conflict floor.
                    // The #9164 dense-mutex experiment raises this only for
                    // opt-in, binary-heavy clique-shaped formulas.
                    self.cold.focused_restart_gate = self.cold.focused_restart_gate.max(10);
                }
                if self.cold.dense_mutex_focused_restart_gate_experiment
                    && dense_mutex_computed_gate != 0
                {
                    if dense_mutex_computed_gate > self.cold.focused_restart_gate {
                        self.stats.dense_mutex_focused_restart_gate_updates += 1;
                    }
                    self.cold.focused_restart_gate = self
                        .cold
                        .focused_restart_gate
                        .max(dense_mutex_computed_gate);
                }
            }

            // #8466: Adaptive chrono-BT disable for small formulas
            // WITHOUT extension variables.
            //
            // Chronological backtracking uses CHRONO_LEVEL_LIMIT (100) to decide
            // when to skip deep backjumps. On small dense formulas (e.g.,
            // clique_n2_k10 with 180 vars), decision levels approach num_vars,
            // and nearly every conflict has skip > 100. This means chrono-BT
            // fires on almost every conflict, preventing deep backjumps and
            // forcing the solver into effectively brute-force DFS.
            //
            // Only disable when factorization did NOT run (no extension vars).
            // When factorization introduces extension variables, the search space
            // grows to ~437 vars (for clique_n2_k10), and chrono-BT's limit of
            // 100 is well-calibrated to that depth — disabling it hurts.
            // Without factorization, on the raw 180-var formula, chrono-BT fires
            // on every conflict because skip_levels always exceeds 100.
            if self.cold.first_extension_var_index == usize::MAX {
                let active_vars = self.num_vars.saturating_sub(self.trail.len());
                if active_vars < 2 * CHRONO_LEVEL_LIMIT as usize && self.chrono_enabled {
                    tracing::info!(
                            active_vars,
                            num_vars = self.num_vars,
                            chrono_level_limit = CHRONO_LEVEL_LIMIT,
                            "disabling chrono-BT: active vars < 2 * CHRONO_LEVEL_LIMIT (no extension vars)"
                        );
                    self.chrono_enabled = false;
                    self.ghost_guard_needed = false;
                }
            }
        }

        // Auto-set learned clause cap for large formulas (#8655).
        //
        // On deep BMC formulas (depth 100+, millions of clauses), learned
        // clauses accumulate rapidly without bound. The normal reduce_db
        // fires at sqrt(conflicts) intervals scaled by log10(clauses),
        // which for million-clause formulas means 10K+ conflicts between
        // reductions. During that interval, each conflict generates a
        // learned clause, potentially doubling the clause DB size.
        //
        // Auto-setting max_learned_clauses as a safety net triggers
        // reduce_db when the learned clause count exceeds a multiple of
        // the original formula size, regardless of the conflict-based
        // scheduling. This prevents BCP from slowing down due to watch
        // list bloat from excessive learned clauses.
        //
        // Only set if the caller hasn't already set an explicit limit.
        if self.cold.max_learned_clauses.is_none()
            && self.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD
        {
            // Two-tier cap (#8655/#8448): very large formulas (>1M clauses) get
            // a tighter cap (2x) because their original clause DB is already
            // huge and learned clauses degrade BCP throughput proportionally
            // more. Formulas in the 100K-1M range use the standard 3x cap.
            let mult = if self.num_original_clauses > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD {
                VERY_LARGE_FORMULA_LEARNED_CAP_MULT
            } else {
                LEARNED_CLAUSE_CAP_MULT
            };
            let cap = self.num_original_clauses * mult;
            self.cold.max_learned_clauses = Some(cap);
        }

        // Large-formula stabilization tuning (#8655).
        //
        // Deep BMC formulas (depth 100+, usually >1M clauses) are highly
        // structured with strong variable locality by unrolling depth.
        // Stable mode (EVSIDS + target phases + reluctant doubling) is
        // far more effective than focused mode (VMTF + Glucose EMA restarts)
        // on these instances because:
        //
        // 1. EVSIDS preserves decision ordering across restarts, letting
        //    the solver progressively explore deeper BMC depths.
        // 2. Target phases preserve satisfying polarities, avoiding
        //    re-discovering the same partial assignment.
        // 3. Reluctant doubling gives geometrically growing restart
        //    intervals, allowing the solver to go deep before restarting.
        //
        // Focused mode's aggressive Glucose EMA restarts destroy search
        // progress on deep BMC: the solver restarts every few hundred
        // conflicts, never reaching the deep unrolling depths where the
        // satisfying assignment lives.
        //
        // Two-tier approach (#8655):
        // - Large structured (>1M clauses): start directly in stable mode.
        //   This avoids wasting the first phase in focused mode entirely.
        //   VSIDS decay is slowed (0.97 for 1M-2M, 0.99 for >2M) to
        //   preserve structural variable scoring. Focused restart gate is
        //   scaled by log10(clauses) so mode-alternation focused phases
        //   don't restart too aggressively.
        // - Medium (>100K clauses): scale the initial phase length by
        //   log10(clauses) so the solver builds better EMA statistics
        //   before the first mode switch, and the tick delta bootstrap
        //   produces a larger base increment for future phases.
        //
        // Only applied when mode_lock is None (not overridden by caller).
        if self.cold.mode_lock == cold::ModeLock::None && LARGE_FORMULA_STABLE_PHASE_SCALE {
            if self.num_original_clauses > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD {
                // Large structured formula (>1M clauses, #8655/#8448): start in
                // stable mode directly. This matches Kissat's stabilizeonly=1
                // behavior and the IC3 pattern (which also locks to stable mode).
                //
                // Stable mode (EVSIDS + target phases + reluctant doubling) is
                // far more effective than focused mode on BMC-style structured
                // formulas because EVSIDS preserves decision ordering across
                // restarts and target phases preserve satisfying polarities.
                //
                // With lock=false (#8448), the normal stabilization schedule
                // can still switch to focused mode later, preserving
                // adaptability for non-BMC structured formulas.
                if !self.stable_mode {
                    tracing::info!(
                        clauses = self.num_original_clauses,
                        threshold = VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD,
                        "starting in stable mode for large structured formula (#8655)"
                    );
                    self.stable_mode = true;
                    self.cold.stable_mode_start_conflicts = self.num_conflicts;
                    // Reset reluctant doubling for a clean stable start.
                    self.cold.reluctant_u = 1;
                    self.cold.reluctant_v = 1;
                    self.cold.reluctant_countdown = RELUCTANT_INIT;
                    self.cold.reluctant_ticked_at = self.num_conflicts;
                    self.sync_active_branch_heuristic();
                }
                // Lock stable mode for very large formulas (#8655).
                //
                // Deep BMC formulas never benefit from focused-mode phases.
                // Focused mode's VMTF queue and aggressive Glucose restarts
                // destroy search progress on structured BMC encodings.
                // Lock the mode so should_restart() never switches back.
                // Matches Kissat's stable=2 (stabilize-only) behavior.
                if VERY_LARGE_FORMULA_STABLE_LOCK && self.cold.mode_lock == cold::ModeLock::None {
                    tracing::info!(
                        clauses = self.num_original_clauses,
                        "locking stable mode for very large formula (#8655)"
                    );
                    self.cold.mode_lock = cold::ModeLock::Stable;
                }

                // Slower VSIDS decay for large structured formulas (#8655).
                //
                // Two tiers of decay adjustment:
                // - >2M clauses (deep BMC): 0.99 — very slow forgetting for
                //   rigid structural locality in deeply unrolled circuits.
                // - 1M-2M clauses (moderate BMC/structured): 0.97 — slower
                //   than default (0.95) but faster than deep BMC, balancing
                //   structural scoring stability with adaptability.
                let decay = if self.num_original_clauses > 2_000_000 {
                    VERY_LARGE_FORMULA_VSIDS_DECAY
                } else {
                    LARGE_FORMULA_VSIDS_DECAY
                };
                self.vsids.set_decay(decay);
                tracing::info!(
                    decay,
                    clauses = self.num_original_clauses,
                    "set slower VSIDS decay for large structured formula (#8655)"
                );

                // Suppress inprocessing during search (#8655).
                //
                // BMC formulas above the stable-bias threshold gain nothing from
                // mid-search inprocessing: the clause structure is
                // fixed by circuit unrolling, and O(clauses) passes
                // (vivification, BVE, probing) waste wall-clock time.
                // Preprocessing already ran before search started.
                // Kissat solves Sokoban HWMCC benchmarks in <5s with
                // zero inprocessing overhead.
                if VERY_LARGE_FORMULA_SUPPRESS_INPROCESSING {
                    tracing::info!(
                        clauses = self.num_original_clauses,
                        "suppressing inprocessing for very large formula (#8655)"
                    );
                    self.disable_all_inprocessing();
                }

                // Scale focused_restart_gate for large formulas (#8655).
                //
                // When mode alternation switches back to focused mode,
                // the default gate of 2 conflicts allows restarts every
                // 3 conflicts. On large structured formulas, this is
                // far too aggressive. Scale by log10(clauses) to give
                // focused mode more conflicts between restarts.
                //
                // 1M clauses:   gate = 2 * 6 = 12 conflicts
                // 2M clauses:   gate = 2 * 6.3 = 12 conflicts
                let gate_scale = (self.num_original_clauses as f64).log10();
                let scaled_gate = (RESTART_INTERVAL as f64 * gate_scale) as u64;
                if scaled_gate > self.cold.focused_restart_gate {
                    self.cold.focused_restart_gate = scaled_gate;
                }

                // Disable rephasing for very large structured formulas (#8655).
                //
                // Rephasing resets variable polarities (phases) using strategies
                // like random, inverted, or best-phase restore. On deep BMC
                // formulas, the structured phase information — where variable
                // polarities correspond to circuit values at each unrolling
                // depth — is critical for search progress. Rephasing destroys
                // this structure, forcing the solver to re-discover satisfying
                // polarities from scratch.
                //
                // Kissat only rephases in stable mode (rephase.c:32-38) and
                // its rephase interval grows rapidly via NLOG3N scheduling. On
                // very large formulas, AY's scaled rephase interval is still
                // too frequent. Pure
                // target-phase saving with no rephase disturbance is optimal
                // for BMC: the solver progressively discovers satisfying
                // polarities and preserves them via the target phase array.
                if self.cold.rephase_enabled {
                    tracing::info!(
                        clauses = self.num_original_clauses,
                        "disabling rephasing for large structured formula (#8655)"
                    );
                    self.cold.rephase_enabled = false;
                }

                // Disable stable-mode EMA restarts for very large formulas (#8655).
                //
                // On deep BMC formulas, pure reluctant doubling (Knuth's Luby
                // sequence) is the optimal restart strategy. The Luby sequence
                // provides geometrically growing restart intervals (1024, 1024,
                // 2048, 1024, 1024, 2048, 4096, ...) that let the solver explore
                // progressively deeper search subtrees.
                //
                // The stable-mode EMA check can interrupt reluctant doubling
                // intervals when the fast LBD EMA exceeds 1.25x the slow EMA.
                // On structured BMC formulas, LBD quality fluctuates as the
                // solver crosses unrolling depth boundaries, causing spurious
                // EMA-triggered restarts that destroy deep search progress.
                //
                // Disable by setting stable_ema_gate to u64::MAX (same as the
                // small-dense formula disable path). This matches CaDiCaL's
                // stable-mode behavior which uses pure reluctant doubling.
                if self.cold.stable_ema_gate != u64::MAX {
                    tracing::info!(
                        clauses = self.num_original_clauses,
                        "disabling stable-mode EMA restarts for large structured formula (#8655)"
                    );
                    self.cold.stable_ema_gate = u64::MAX;
                }
            } else if self.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
                // Large formula (100K-1M clauses): scale initial phase
                // length so the solver builds better statistics before
                // the first mode switch.
                let scale = (self.num_original_clauses as f64).log10();
                let scaled_phase = (STABLE_PHASE_INIT as f64 * scale) as u64;
                if scaled_phase > self.cold.stable_phase_length {
                    tracing::info!(
                        clauses = self.num_original_clauses,
                        original_phase = self.cold.stable_phase_length,
                        scaled_phase,
                        "scaling initial stable phase length for large formula (#8655)"
                    );
                    self.cold.stable_phase_length = scaled_phase;
                }
            }
        }

        // Large-formula rephase interval scaling (#8655).
        //
        // On large structured formulas, the default rephase interval
        // of 1000 conflicts fires far too early. At that point the solver has
        // barely explored one unrolling depth and rephasing destroys the
        // structured phase information that BMC search depends on (variable
        // polarities correspond to circuit values at each unrolling depth).
        //
        // Kissat only rephases in stable mode (rephase.c:32-38:
        // `if (!solver->stable) return false`). AY rephases in both modes,
        // which is more aggressive. For large structured formulas, we
        // compensate by scaling the initial rephase interval by log10(clauses),
        // matching the stable phase length scaling above.
        //
        // 100K clauses: next_rephase = 1000 * 5 = 5000 conflicts
        // 500K clauses: next_rephase = 1000 * 5.7 = 5700 conflicts
        // 1M clauses:   next_rephase = 1000 * 6 = 6000 conflicts
        //
        // This also increases the rephase count base used in the NLOG3N
        // scheduling, so subsequent rephases are also spaced further apart.
        if self.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
            let scale = (self.num_original_clauses as f64).log10();
            let scaled_rephase = (REPHASE_INITIAL as f64 * scale) as u64;
            if scaled_rephase > self.cold.next_rephase {
                tracing::info!(
                    clauses = self.num_original_clauses,
                    original_rephase = self.cold.next_rephase,
                    scaled_rephase,
                    "scaling initial rephase interval for large formula (#8655)"
                );
                self.cold.next_rephase = self.num_conflicts.saturating_add(scaled_rephase);
            }
        }

        // Component decomposition (#8168): if preprocessing detected multiple
        // disconnected components, solve each independently via sub-solvers.
        // Gate on decompose.enabled (#8448): sub-solvers with decompose
        // disabled must not re-decompose. Without this gate, a sub-solver
        // (set_decompose_enabled(false)) still triggered try_decompose_solve
        // because analyze_components ran unconditionally in preprocessing
        // and set decomposable_found > 0.
        if self.inproc_ctrl.decompose.enabled && self.cold.component_stats.decomposable_found > 0 {
            if let Some(result) = self.try_decompose_solve() {
                return result;
            }
        }

        // SAT-COMP current-mode native helpers are installed after
        // preprocessing so compilation sees the final variable capacity. Scalar
        // CDCL remains authoritative: unavailable helpers simply fall back.
        #[cfg(feature = "jit")]
        self.install_sat_native_helpers_for_current_mode_at_solver_start();

        // CaDiCaL internal.cpp:487-489: init_search_limits.
        // Set the initial inprobe conflict limit proportional to formula size.
        // delta = log10(irredundant + 10)^2; lim.inprobe = conflicts + inprobeint * delta.
        // For shuffling-2 (4.9M clauses): delta=44.7, limit=4470 conflicts.
        // Without this, next_inprobe_conflict=0 causes inprocessing to fire at
        // conflict 1 on large post-BVE formulas, wasting time on passes that
        // CaDiCaL defers until the search has made progress (#6926).
        //
        // Dense formula scaling (#9215): on large dense formulas (>2M clauses,
        // density > 20), AY's per-conflict cost is much higher than CaDiCaL's
        // due to BCP overhead on the huge clause database. Reaching 4470
        // conflicts takes ~40s on shuffling-2 vs <1s on CaDiCaL. Since the
        // density guard skips most inprocessing passes anyway, reduce the
        // initial limit by 4x so sweep fires sooner.
        {
            let irredundant = self.num_original_clauses as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let active_cls = self.arena.active_clause_count();
            let active_vars_est = self.num_vars.saturating_sub(self.trail.len());
            let formula_density = if active_vars_est > 0 {
                active_cls as f64 / active_vars_est as f64
            } else {
                0.0
            };
            let scale = if active_cls > 2_000_000 && formula_density > 20.0 {
                0.25 // 4x reduction for dense formulas
            } else {
                1.0
            };
            let limit = (INPROBE_INTERVAL as f64 * delta * scale) as u64;
            self.cold.next_inprobe_conflict = self.total_conflicts().saturating_add(limit);
        }

        // Try lucky phases (CaDiCaL-style pre-solving)
        // This can quickly solve formulas with simple satisfying assignments.
        //
        // Size guard (#8448): lucky phases iterate ALL variables with BCP after
        // each decision. On large formulas (ecarev-110: 127K vars, 741K clauses),
        // 8 lucky strategies x 127K variables x O(clauses) BCP = 15+ seconds.
        // CaDiCaL's BCP is 3-8x faster (constants.rs performance gap analysis),
        // so what CaDiCaL does in 2s takes AY 10-20s. Skip lucky phases when
        // the formula exceeds 50K variables or 500K clauses — these formulas
        // are never "lucky" in practice and the time is better spent on CDCL.
        {
            let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars());
            let active_cls = self.arena.active_clause_count();
            if active_vars < preprocess::LUCKY_SMALL_MAX_ACTIVE_VARS
                && active_cls < preprocess::LUCKY_SMALL_MAX_ACTIVE_CLAUSES
            {
                let t0 = ay_core::time::Instant::now();
                let lucky_result = self.try_lucky_phases();
                // Accumulate: the early (pre-preprocess) lucky attempt may have
                // already recorded time before preprocessing shrank the formula
                // below the small gate.
                self.stats.lucky_time_ns = self
                    .stats
                    .lucky_time_ns
                    .saturating_add(t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64);
                if let Some(sat) = lucky_result {
                    if sat {
                        // Lucky phase found satisfying assignment
                        self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
                        return self.declare_sat_from_current_assignment();
                    }
                    // UNSAT proven at level 0 during lucky phase
                    return self.declare_unsat();
                }
            }
        }
        if self.is_interrupted() {
            return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
        }

        // Run warmup to initialize target phases before walk
        // Warmup uses propagation-based phase setting which is O(1) per propagation
        self.try_warmup();

        // Try walk-based phase initialization for larger formulas
        // Walk uses ProbSAT to find good initial phases by minimizing unsatisfied clauses
        let walk_start = ay_core::time::Instant::now();
        let walk_found = self.try_walk();
        self.stats.walk_time_ns = walk_start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        if walk_found {
            // Walk found an assignment satisfying (some subset of) clauses.
            // Before returning SAT, verify the candidate model against *all* clauses
            // (including any learned clauses added during preprocessing) and
            // against reconstruction obligations from equisatisfiable transforms.
            //
            // `walk` is a heuristic; without this check, it can return a model that
            // does not satisfy the full clause database, which is an unsound SAT result.
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

        // Jeroslow-Wang initial phases: for any variable without a saved phase
        // (from walk/warmup), set phase to the polarity with higher JW score.
        // JW(l) = sum_{c containing l} 2^{-|c|}. Higher score means the literal
        // appears in more/shorter clauses, so assigning it true satisfies more
        // constraints. CaDiCaL computes this in phases.cpp for initial_phase=2.
        // Cost: O(total_literals), negligible even on 4M-clause formulas (~10ms).
        self.init_jw_phases();

        let t0 = ay_core::time::Instant::now();
        let result = self.cdcl_loop_pure(should_stop);
        self.stats.search_time_ns = t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        result
    }
}

// Finalize section (declare_*, finalize_*, proof_writer, handle_ext_conflict)
// moved to finalize.rs (#4933).
