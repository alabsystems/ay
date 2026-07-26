// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified CDCL backend loop for theory callback and extension modes.

use super::super::*;
use super::theory_callback::{NullCallback, TheoryCallback, TheoryModelCheck};

impl Solver {
    pub(crate) fn disable_extension_inprocessing(&mut self) {
        self.inproc_ctrl.condition.enabled = false;
        self.inproc_ctrl.bve.enabled = false;
        self.inproc_ctrl.bce.enabled = false;
        self.inproc_ctrl.sweep.enabled = false;
        self.inproc_ctrl.congruence.enabled = false;
        self.inproc_ctrl.factor.enabled = false;
        self.inproc_ctrl.decompose.enabled = false;
        // #7979: Vivification is SAFE for theory/extension mode. It strengthens
        // clauses by removing redundant literals via BCP — no variable elimination,
        // no binary implication generation, no reconstruction needed. Disabling
        // vivification degraded learned clause quality, breaking CDCL search
        // trajectories that E-matching depends on for AUFLIA convergence.
        // Subsumption and HTR were already enabled; vivify completes the set
        // of theory-safe inprocessing techniques.
        //
        // UNSAFE techniques remain disabled:
        //   BVE: eliminates variables, reconstruction interacts with theory lemmas
        //   BCE: removes clauses, may drop theory-relevant blocking clauses
        //   Sweep: variable equivalence substitution without theory consultation
        //   Congruence/Decompose: SCC-based rewriting without theory awareness
        //   Factor: introduces extension variables
        //   SBVA: introduces extension variables via new_var_internal() (#8078)
        //   Condition: root-satisfied clause GC, may drop theory-visible clauses
        //   Probe: HBR-derived implications are unsound without theory (#7935)
        //   Backbone: uses probing internally, inherits probe unsoundness
        //
        // #7935: Probing with HBR generates binary implication clauses that
        // are sound for pure SAT but unsound in DPLL(T) — the SAT-level
        // probe does not consult the theory, so implications derived from
        // failed literals may not hold under theory semantics. Backbone
        // detection uses probing internally and inherits the same unsoundness.
        self.inproc_ctrl.probe.enabled = false;
        self.inproc_ctrl.backbone.enabled = false;
        // #8078: SBVA introduces extension variables via new_var_internal().
        // Like factor, these interact badly with theory/extension mode.
        self.inproc_ctrl.sbva.enabled = false;
    }

    /// Unified CDCL loop for theory callback and extension modes (Wave 2).
    ///
    /// The optional `should_stop` closure is polled every 100 conflicts and
    /// every 1000 decisions, matching `solve_no_assumptions`. When it returns
    /// `true`, the solver returns `Unknown` with reason `Interrupted`.
    pub(super) fn solve_no_assumptions_with_theory_backend<C, F>(
        &mut self,
        callback: &mut C,
        should_stop: F,
    ) -> SatResult
    where
        C: TheoryCallback,
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY across solve() calls.

        // Record wall-clock start time for progress/observer reporting (#8155).
        if self.cold.progress_enabled || self.has_observer() {
            self.cold.solve_start_time = Some(ay_core::time::Instant::now());
            self.cold.last_progress_time = None;
        }

        if let Some(result) = callback.init_loop(self) {
            return result;
        }

        // Run initial preprocessing in theory/extension mode.
        // Only safe techniques run: subsumption, probing, HTR (add implications
        // only). Clause-deleting and variable-eliminating techniques are disabled
        // because theory callbacks may add lemmas referencing any variable/clause
        // during the CDCL loop that follows.
        if self.cold.preprocess_enabled && !self.cold.has_been_incremental {
            // #7935: Disable ALL preprocessing in theory/extension mode.
            // SAT-level preprocessing (probing, backbone, HTR, subsumption)
            // operates without theory solver consultation. It can derive
            // implications that are sound for pure SAT but unsound in DPLL(T),
            // forcing theory atoms TRUE at level 0 and creating spurious
            // theory conflicts. Previously only clause-deleting techniques
            // were disabled; now all techniques are blocked.
            self.cold.preprocess_enabled = false;
        }

        // Disable destructive inprocessing techniques for theory/extension mode.
        //
        // BVE, BCE, sweep, congruence, decompose, factor, condition, probe, and
        // backbone are unsound in DPLL(T): they modify or eliminate variables
        // and clauses without consulting the theory solver. BVE in particular
        // creates reconstruction entries that can cause finalize_sat_model to
        // fail original-formula verification, producing InvalidSatModel -> Unknown.
        //
        // Previously only the preprocessing_extension path (used by standalone
        // SAT with preprocessing) called disable_extension_inprocessing(). The
        // extension/theory paths that enter through solve_with_extension() or
        // solve_with_theory() did NOT, leaving BVE/probe/sweep/etc. enabled
        // during the CDCL loop. After enough conflicts, inprocessing_gates_pass()
        // would trigger run_restart_inprocessing() with these destructive
        // techniques active, causing QF_LRA (and other theory) benchmarks to
        // return Unknown instead of Sat/Unsat.
        //
        // Safe techniques (vivify, subsume, HTR, reorder) remain enabled --
        // see disable_extension_inprocessing() for the full rationale.
        self.disable_extension_inprocessing();

        // CaDiCaL init_search_limits (internal.cpp:487-489) for DPLL(T) path.
        // Same formula-size-proportional inprobe limit as the pure SAT path.
        {
            let irredundant = self.arena.active_clause_count() as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.total_conflicts().saturating_add(limit);
        }

        self.cdcl_loop(callback, should_stop)
    }

    #[inline]
    pub(in crate::solver) fn maybe_run_restart<C: TheoryCallback>(
        &mut self,
        callback: &mut C,
    ) -> bool {
        // Cold restart check (Zhang et al. 2024, arXiv:2404.16387):
        // fires at much longer intervals (300K+ conflicts) than warm
        // restarts and is independent of the warm restart schedule.
        // Check here so all conflict paths benefit.
        if self.should_cold_restart() {
            self.do_cold_restart();
            callback.backtrack_after_materializing_lazy_reasons(self, 0);
            self.cold.lazy_materialization_failed = false;
        }

        if self.num_conflicts < callback.restart_warmup_conflicts() {
            return false;
        }
        if !self.should_restart() {
            return false;
        }
        if callback.should_block_restart(self.trail.len() as u32, self.num_vars as u32) {
            return false;
        }

        self.stats.record_pending_restart_attribution();
        callback.materialize_lazy_reasons_before_restart(self);
        let vars_to_bump = callback.on_restart();
        self.do_restart();

        // Tier controller: check for completed background compilations
        // at restart boundaries. Currently T0 and T1 only; T2-T4 placeholders
        // will trigger here when their background compilations complete.
        // BCP JIT tier controller and retired BCP compiler polling removed (#8517).

        // #7982: Re-boost theory atom VSIDS activity at restart time.
        // Theory atoms get one initial bump at registration but are quickly
        // overwhelmed by conflict-driven activity. Re-boosting at restart
        // keeps theory atoms competitive in the VSIDS heap, ensuring the
        // DPLL solver continues deciding theory atoms and feeding bounds
        // to the theory solver.
        //
        // #8008: Theory atoms get 10 bumps per restart (equivalent to 10
        // conflict participations). This must overpower the conflict-driven
        // activity that accumulates on Tseitin encoding variables between
        // restarts. With only 3 bumps, theory atoms sink below encoding
        // variables after ~20 conflicts, causing "bound starvation" where
        // DPLL stops deciding theory atoms. 10 bumps keeps theory atoms
        // in the top ~20% of the VSIDS heap across restart intervals,
        // matching Z3's add_theory_aware_branching_info priority boost.
        let use_vsids = self.active_branch_heuristic != BranchHeuristic::Vmtf;
        for var in vars_to_bump {
            if var.index() < self.num_vars {
                for _ in 0..10 {
                    self.vsids.bump(var, &self.vals, use_vsids);
                }
            }
        }
        true
    }

    #[inline]
    pub(in crate::solver) fn maybe_run_restart_pure(&mut self) -> bool {
        // Cold restart check (Zhang et al. 2024, arXiv:2404.16387):
        // fires at much longer intervals (300K+ conflicts) than warm
        // restarts and is independent of the warm restart schedule.
        // Check here so all conflict paths benefit.
        if self.should_cold_restart() {
            self.do_cold_restart();
        }

        if !self.should_restart_pure() {
            return false;
        }

        self.stats.record_pending_restart_attribution();
        self.do_restart_pure();
        true
    }

    #[inline]
    pub(in crate::solver) fn cdcl_loop_pure<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        if self.cold.tla_trace.is_some() {
            let mut callback = NullCallback;
            self.cdcl_loop_impl::<false, _, _>(&mut callback, should_stop)
        } else {
            self.cdcl_loop_main_no_tla(should_stop)
        }
    }

    /// Unified CDCL inner loop shared by pure SAT, theory, and extension modes.
    ///
    /// All solve-mode specific preamble (init, preprocessing, walk, and search
    /// limit setup) is done by the caller before entering this loop.
    pub(in crate::solver) fn cdcl_loop<C, F>(
        &mut self,
        callback: &mut C,
        should_stop: F,
    ) -> SatResult
    where
        C: TheoryCallback,
        F: Fn() -> bool,
    {
        self.cdcl_loop_impl::<true, _, _>(callback, should_stop)
    }

    #[inline]
    fn declare_cdcl_complete_assignment_sat(&mut self) -> SatResult {
        self.debug_assert_cdcl_complete_assignment_satisfies_arena();
        if self.cold.tla_trace.is_some() {
            self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
        }
        self.declare_sat_from_current_assignment()
    }

    #[inline]
    fn declare_cdcl_complete_assignment_sat_no_tla(&mut self) -> SatResult {
        self.debug_assert_cdcl_complete_assignment_satisfies_arena();
        self.declare_sat_from_current_assignment()
    }

    #[inline]
    fn debug_assert_cdcl_complete_assignment_satisfies_arena(&self) {
        // #8078: Pre-SAT arena clause verification.
        // When JIT BCP is active, verify every non-garbage arena clause is
        // satisfied. JIT codegen bugs can miss propagations/conflicts, leading
        // to a spurious SAT on UNSAT formulas. When an unsatisfied clause is
        // found, invalidate JIT and restart search with standard 2WL BCP, which
        // is proven correct. BCP JIT missed-conflict detection removed (#8517).
        #[cfg(debug_assertions)]
        {
            let model = self.get_model();
            for idx in self.arena.indices() {
                if self.arena.is_garbage(idx) {
                    continue;
                }
                let lits = self.arena.literals(idx);
                let satisfied = lits.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < model.len() && model[vi] == lit.is_positive()
                });
                debug_assert!(
                    satisfied,
                    "BUG [#8078]: BCP missed conflict! clause_idx={idx}, \
                     dimacs={:?}, learned={}, qhead={}, trail_len={}, dl={}",
                    lits.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                    self.arena.is_learned(idx),
                    self.qhead,
                    self.trail.len(),
                    self.decision_level,
                );
            }
        }
    }

    /// Main/default CDCL loop for pure SAT with no TLA tracing.
    ///
    /// This is intentionally a direct spelling of the `USE_CALLBACK = false`
    /// path from `cdcl_loop_impl`: no theory callback object, no theory model
    /// checks, and no per-iteration TLA branches. The TLA-enabled pure route
    /// continues to use `cdcl_loop_impl::<false>` above.
    fn cdcl_loop_main_no_tla<F>(&mut self, should_stop: F) -> SatResult
    where
        F: Fn() -> bool,
    {
        // Branch-independent time-based interrupt (see solve_with_assumptions_impl):
        // a restart-thrash regime can starve the per-conflict/per-decision
        // `should_stop` checks below, so check it at the loop top, amortized every
        // 1024 iterations, to keep wall-clock query deadlines fail-closed.
        let mut loop_iters: u64 = 0;
        loop {
            if self.is_interrupted() {
                return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
            }
            loop_iters = loop_iters.wrapping_add(1);
            if loop_iters & 1023 == 0 {
                if should_stop() {
                    return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                }
                // Conflict-independent memory poll (see cdcl_loop_impl): the
                // reduction-time poll requires conflicts, so a low-conflict
                // regime would otherwise never see the process memory gate.
                self.poll_process_memory_limit_now();
            }

            self.import_portfolio_shared_clauses_at_root();

            if self.has_empty_clause {
                return self.declare_unsat();
            }

            if let Some(conflict_ref) = self.search_propagate_standard() {
                if self.decision_level == 0 {
                    if self.cold.trace_ext_conflict {
                        self.trace_bcp_conflict_level0(conflict_ref);
                    }
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat();
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();
                self.notify_observer_conflict();

                if self.cold.trace_ext_conflict {
                    self.trace_bcp_conflict_detail(conflict_ref);
                }

                if self.resource_budget_exhausted() {
                    return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                }
                if self.num_conflicts.is_multiple_of(100) {
                    if should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                    self.maybe_emit_progress();
                }

                self.analyze_and_backtrack(conflict_ref, "main search loop", |_, _| {});
                self.maybe_run_restart_pure();
                continue;
            }

            let restarted = self.maybe_run_restart_pure();
            if restarted {
            } else if self.should_rephase() {
                if self.decision_level != 0 {
                    self.backtrack(0);
                }
                self.rephase();
            } else if self.should_run_lookahead() {
                debug_assert_eq!(self.decision_level, 0);
                self.run_lookahead_round();
                if self.has_empty_clause {
                    return self.declare_unsat();
                }
            } else if self.inprocessing_gates_pass() {
                if self.decision_level != 0 {
                    self.backtrack(0);
                }
                let found_unsat = self.run_restart_inprocessing();
                if found_unsat {
                    return self.declare_unsat();
                }
                continue;
            } else if let Some(la_lit) = self.take_lookahead_decision() {
                self.decide(la_lit);
                if self.num_decisions.is_multiple_of(1000) {
                    // Deterministic decision-budget checkpoint FIRST
                    // (#ground-determinism), then the nondeterministic
                    // external stops — so a budget-exhausted stop is
                    // attributed to the budget on every host.
                    if self.decision_budget_exhausted() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    if self.is_interrupted() || should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }
            } else if let Some(var) = self.pick_next_decision_variable_main() {
                let lit = self.pick_phase(var);
                self.decide(lit);
                if self.num_decisions.is_multiple_of(1000) {
                    if self.decision_budget_exhausted() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    if self.is_interrupted() || should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }
            } else {
                return self.declare_cdcl_complete_assignment_sat_no_tla();
            }
        }
    }

    fn cdcl_loop_impl<const USE_CALLBACK: bool, C, F>(
        &mut self,
        callback: &mut C,
        should_stop: F,
    ) -> SatResult
    where
        C: TheoryCallback,
        F: Fn() -> bool,
    {
        // Branch-independent time-based interrupt (see solve_with_assumptions_impl):
        // amortized loop-top `should_stop` so a restart-thrash regime cannot starve
        // the wall-clock query deadline.
        let mut loop_iters: u64 = 0;
        loop {
            if self.is_interrupted() {
                return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
            }
            loop_iters = loop_iters.wrapping_add(1);
            if loop_iters & 1023 == 0 {
                if should_stop() {
                    return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                }
                // A zero-conflict theory-propagation spin (non-converging LIA
                // bound refinements) makes no conflicts and no decisions, so
                // the per-conflict/per-decision checkpoints below never run and
                // the conflict-cadence memory poll in reduction never fires.
                // Enforce both budgets here on the same amortized cadence:
                // the deterministic `:rlimit` conflict budget (#8749 — checked
                // in the pure loop at its conflict site but previously never
                // in this extension loop), its decision-budget companion
                // (#ground-determinism), and the process memory gate, so the
                // very next `is_interrupted()` sees compressor-backed growth.
                if self.resource_budget_exhausted() {
                    return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                }
                self.poll_process_memory_limit_now();
            }

            // Check if an inprocessing/theory lemma detected global UNSAT.
            if self.has_empty_clause {
                return self.declare_unsat();
            }

            // Propagate — search-specialized BCP (no probe/vivify overhead).
            // Capture trail length when USE_CALLBACK (for the Phase C
            // interleaved-theory hook, #4919) or when TLA tracing is active
            // (for trace emission). Phase C uses this to detect cascading BCP
            // work — Z3's propagate_core pattern calls theory unit_propagate
            // each time BCP drains qhead (reference/z3/src/sat/sat_solver.cpp:961).
            let trail_len_before_prop = if USE_CALLBACK || self.cold.tla_trace.is_some() {
                self.trail.len()
            } else {
                0
            };
            let propagate_result = if USE_CALLBACK {
                self.search_propagate()
            } else {
                self.search_propagate_standard()
            };
            if let Some(conflict_ref) = propagate_result {
                if self.cold.tla_trace.is_some() {
                    if self.trail.len() > trail_len_before_prop {
                        self.tla_trace_step(
                            CdclTraceState::Propagating,
                            Some(CdclTraceAction::Propagate),
                        );
                    }
                    self.tla_trace_step(
                        CdclTraceState::Conflicting,
                        Some(CdclTraceAction::DetectConflict),
                    );
                }

                if self.decision_level == 0 {
                    if self.cold.trace_ext_conflict {
                        self.trace_bcp_conflict_level0(conflict_ref);
                    }
                    if USE_CALLBACK {
                        // #8467: materialize level-0 lazy theory reasons BEFORE
                        // collecting the level-0 resolution chain, so the chain
                        // sees real reason clauses (with proof ids) instead of
                        // lazy table indexes (which carry no clause and would
                        // leave holes in the empty-clause derivation).
                        callback.materialize_lazy_reasons(self);
                    }
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat();
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();
                self.notify_observer_conflict();
                // #8452: BCP-level conflict — not a direct theory conflict.
                if USE_CALLBACK {
                    self.update_theory_conflict_ratio(false);
                }

                // Tier controller: check if conflict count reached a
                // promotion threshold (T1->T2 at 1K conflicts, etc.).
                // BCP JIT tier controller conflict tracking removed (#8517).

                if self.cold.trace_ext_conflict {
                    self.trace_bcp_conflict_detail(conflict_ref);
                }

                // Deterministic resource-budget checkpoint at the conflict
                // site (#ground-determinism): mirrors the pure loop's exact
                // per-conflict honoring so small `:rlimit` budgets stop at
                // the same conflict count in both loops.
                if self.resource_budget_exhausted() {
                    return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                }
                // Interrupt check on conflict path (#6296): matches
                // solve_no_assumptions' every-100-conflicts check.
                if self.num_conflicts.is_multiple_of(100) {
                    if should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                    // Periodic progress reporting (wall-clock gated, ~5s interval).
                    self.maybe_emit_progress();
                    // BCP JIT PGO recompile and tier-promotion recompile removed (#8517).
                }

                if USE_CALLBACK {
                    // #8467: Pre-materialize lazy theory reasons at the current
                    // decision level so 1UIP resolution never encounters them.
                    callback.materialize_lazy_reasons(self);
                    let context = callback.conflict_context();
                    self.analyze_and_backtrack(conflict_ref, context, |solver, level| {
                        callback.backtrack_after_materializing_lazy_reasons(solver, level);
                    });
                } else {
                    self.analyze_and_backtrack(conflict_ref, "main search loop", |_, _| {});
                }
                if USE_CALLBACK {
                    self.maybe_run_restart(callback);
                } else {
                    self.maybe_run_restart_pure();
                }
                continue;
            }

            // No conflict from BCP — scheduling path.
            if self.cold.tla_trace.is_some() && self.trail.len() > trail_len_before_prop {
                self.tla_trace_step(
                    CdclTraceState::Propagating,
                    Some(CdclTraceAction::Propagate),
                );
            }

            if USE_CALLBACK {
                // Run backend-specific propagation checks before making a SAT decision.
                let mut theory_result = callback.propagate(self);
                if self.cold.trace_ext_conflict {
                    self.trace_theory_result_tag(&theory_result);
                }

                // Phase C (BCP-interleaved theory propagation, #4919):
                // If the first theory call returned Continue but BCP just
                // propagated atoms, give the theory one more force-call to
                // catch cascading internal work (e.g. pending implied bounds
                // in LRA) that does not show up as new theory atoms on the
                // SAT trail. If this surfaces new propagations, the upgraded
                // result routes into the same fixpoint loop the Propagate arm
                // uses below — matching Z3's propagate_core pattern where
                // unit_propagate is called each time BCP drains qhead, not just
                // after BCP exits. See reference/z3/src/sat/sat_solver.cpp:961-976.
                if matches!(theory_result, TheoryPropResult::Continue)
                    && self.trail.len() > trail_len_before_prop
                {
                    let forced = callback.propagate_force(self);
                    if self.cold.trace_ext_conflict {
                        self.trace_theory_result_tag(&forced);
                    }
                    self.stats.bcp_theory_interleaved_force_calls += 1;
                    if !matches!(forced, TheoryPropResult::Continue) {
                        self.stats.bcp_theory_interleaved_force_hits += 1;
                        theory_result = forced;
                    }
                }

                // #8256: Check should_stop after theory propagation calls.
                // For theory-heavy formulas (QF_LRA), each propagate() call runs
                // expensive simplex operations. The SAT solver may make very few
                // conflicts/decisions per second, causing the 100-conflict and
                // 1000-decision polling checkpoints to never fire within the
                // wall-clock budget. This check ensures the budget is respected
                // even when theory calls dominate runtime.
                //
                // #8465: Gate the check on whether the theory callback actually
                // did work. When theory_result is not Continue, a potentially
                // expensive theory operation happened and we must check the budget.
                // When it IS Continue, the periodic checks on conflict (every 100)
                // and decision (every 1000) paths are sufficient for timeout
                // responsiveness.
                // #storm-poll-cadence companion: ALSO poll on Continue results
                // at an amortized 1/32 cadence. A propagate-time pivot storm is
                // a run of expensive-but-derivation-free theory rounds — the
                // budget-exhausted propagate simplex maps Unknown->Sat ("no
                // conflict found"), so every storm round returns Continue and
                // the #8465 gate skipped the only per-round poll, starving the
                // wall-clock deadline exactly when rounds are slowest. One
                // should_stop() per 32 Continue rounds is noise; a hit only
                // produces an earlier legal Unknown (fail-closed liveness).
                self.cold.theory_continue_polls = self.cold.theory_continue_polls.wrapping_add(1);
                let continue_poll = matches!(theory_result, TheoryPropResult::Continue)
                    && self.cold.theory_continue_polls.is_multiple_of(32);
                if (!matches!(theory_result, TheoryPropResult::Continue) || continue_poll)
                    && should_stop()
                {
                    return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                }
                match theory_result {
                    TheoryPropResult::Continue => {
                        // #8003: Bulk theory phase seeding. After BCP and theory
                        // propagation reach quiescence, seed the SAT phase[] array
                        // with theory-model-consistent polarities for all unassigned
                        // theory atoms. This creates the Z3-style feedback loop
                        // where the LP/simplex model guides SAT search by biasing
                        // pick_phase() toward theory-consistent assignments.
                        //
                        // This is critical for induction/BMC benchmarks where Z3
                        // solves in 0.1-0.9s but AY times out. Z3 checks its theory
                        // model at every decision (get_phase), and the bulk seeding
                        // here approximates that by writing all phase hints at once.
                        callback.seed_theory_phases(self);
                    }
                    TheoryPropResult::Propagate => {
                        // #8003 Gap 3: BCP-Theory fixed-point loop.
                        // Z3 loops BCP + theory propagation to quiescence before
                        // making a decision. Previously AY did a single BCP pass,
                        // single theory propagation, then `continue`d to the top
                        // of the CDCL loop (hitting all scheduling checks). Now we
                        // run an inner loop: re-run BCP + theory propagation until
                        // both return no-change, then fall through to scheduling.
                        // Bounded to MAX_FIXPOINT_ITERS to prevent infinite loops.
                        const MAX_FIXPOINT_ITERS: u32 = 8;
                        self.stats.bcp_theory_fixpoint_entries += 1;
                        let mut fixpoint_iter = 0u32;
                        loop {
                            // Check for pending theory conflict before BCP (#6262).
                            if let Some(conflict_ref) = self.take_live_pending_theory_conflict() {
                                self.conflicts_since_restart += 1;
                                self.num_conflicts += 1;
                                self.on_conflict_random_decision();
                                self.notify_observer_conflict();
                                // #8452: Pending theory conflict = theory-originated.
                                self.cold.ext_conflict_count += 1;
                                self.update_theory_conflict_ratio(true);
                                if self.decision_level == 0 {
                                    // #8467: materialize before collecting the
                                    // level-0 chain (lazy table indexes are not
                                    // arena offsets).
                                    callback.materialize_lazy_reasons(self);
                                    self.record_level0_conflict_chain(conflict_ref);
                                    return self.declare_unsat();
                                }
                                // #8467: Pre-materialize lazy theory reasons.
                                callback.materialize_lazy_reasons(self);
                                let context = callback.conflict_context();
                                self.analyze_and_backtrack(
                                    conflict_ref,
                                    context,
                                    |solver, level| {
                                        callback.backtrack_after_materializing_lazy_reasons(
                                            solver, level,
                                        );
                                    },
                                );
                                self.maybe_run_restart(callback);
                                break;
                            }

                            fixpoint_iter += 1;
                            if fixpoint_iter > MAX_FIXPOINT_ITERS {
                                self.stats.bcp_theory_fixpoint_saturated += 1;
                                break;
                            }

                            // Theory lemma may have set has_empty_clause (e.g.,
                            // contradicting unit clauses). The outer loop checks
                            // this at the top, so break and let it handle UNSAT.
                            if self.has_empty_clause {
                                break;
                            }

                            // Re-run BCP on any new unit propagations from theory lemmas.
                            let trail_before = self.trail.len();
                            let bcp_result = self.search_propagate();
                            if let Some(conflict_ref) = bcp_result {
                                // BCP found a conflict — handle normally.
                                if self.decision_level == 0 {
                                    // #8467: materialize before collecting the
                                    // level-0 chain (lazy table indexes are not
                                    // arena offsets).
                                    callback.materialize_lazy_reasons(self);
                                    self.record_level0_conflict_chain(conflict_ref);
                                    return self.declare_unsat();
                                }
                                self.conflicts_since_restart += 1;
                                self.num_conflicts += 1;
                                self.on_conflict_random_decision();
                                self.notify_observer_conflict();
                                // #8452: BCP conflict inside fixpoint loop — not theory.
                                self.update_theory_conflict_ratio(false);
                                if self.num_conflicts.is_multiple_of(100) {
                                    if should_stop() {
                                        return self.declare_unknown_with_reason(
                                            SatUnknownReason::Interrupted,
                                        );
                                    }
                                    self.maybe_emit_progress();
                                }
                                // #8467: Pre-materialize lazy theory reasons.
                                callback.materialize_lazy_reasons(self);
                                let context = callback.conflict_context();
                                self.analyze_and_backtrack(
                                    conflict_ref,
                                    context,
                                    |solver, level| {
                                        callback.backtrack_after_materializing_lazy_reasons(
                                            solver, level,
                                        );
                                    },
                                );
                                self.maybe_run_restart(callback);
                                break;
                            }
                            let bcp_propagated = self.trail.len() > trail_before;

                            // Re-run theory propagation. Use propagate_force() to bypass
                            // the can_propagate gate (#8452). Inside the fixpoint, the
                            // theory may have pending implied bounds cascading work from
                            // the previous round that doesn't manifest as new theory
                            // atoms on the SAT trail. Without this, the fixpoint exits
                            // prematurely when BCP propagates boolean-only variables.
                            let inner_theory = callback.propagate_force(self);
                            // #8256: Check should_stop inside the fixpoint loop.
                            // Each theory propagation call can run expensive simplex.
                            // Without this check, the fixpoint loop can consume the
                            // entire wall-clock budget without ever polling should_stop.
                            if should_stop() {
                                return self
                                    .declare_unknown_with_reason(SatUnknownReason::Interrupted);
                            }
                            match inner_theory {
                                TheoryPropResult::Continue => {
                                    if !bcp_propagated {
                                        // Fixed point: neither BCP nor theory produced
                                        // anything new. Fall through to scheduling.
                                        break;
                                    }
                                    // BCP propagated but theory didn't — loop once more
                                    // in case theory needs another look.
                                }
                                TheoryPropResult::Propagate => {
                                    // Theory produced new propagations; loop to re-run BCP.
                                }
                                TheoryPropResult::Conflict(clause) => {
                                    if let Some(result) =
                                        callback.handle_conflict_clause(self, clause)
                                    {
                                        return result;
                                    }
                                    self.maybe_run_restart(callback);
                                    break;
                                }
                                TheoryPropResult::Stop => {
                                    return self
                                        .declare_unknown_with_reason(SatUnknownReason::TheoryStop);
                                }
                            }
                        }
                        // Record fixpoint depth stats (#8003).
                        self.stats.bcp_theory_fixpoint_iterations += u64::from(fixpoint_iter);
                        if fixpoint_iter > self.stats.bcp_theory_fixpoint_max_depth {
                            self.stats.bcp_theory_fixpoint_max_depth = fixpoint_iter;
                        }
                        // #8003: Seed theory phases after fixpoint quiescence.
                        callback.seed_theory_phases(self);
                        continue;
                    }
                    TheoryPropResult::Conflict(clause) => {
                        if let Some(result) = callback.handle_conflict_clause(self, clause) {
                            return result;
                        }
                        self.maybe_run_restart(callback);
                        continue;
                    }
                    TheoryPropResult::Stop => {
                        return self.declare_unknown_with_reason(SatUnknownReason::TheoryStop);
                    }
                }

                // Catch pending theory conflicts from non-propagation paths (#6262).
                // This handles the edge case where callback.propagate() returns
                // Continue but a previous iteration left a pending conflict.
                if let Some(conflict_ref) = self.take_live_pending_theory_conflict() {
                    self.conflicts_since_restart += 1;
                    self.num_conflicts += 1;
                    self.on_conflict_random_decision();
                    self.notify_observer_conflict();
                    // #8452: Pending theory conflict = theory-originated.
                    self.cold.ext_conflict_count += 1;
                    self.update_theory_conflict_ratio(true);
                    if self.decision_level == 0 {
                        // #8467: materialize before collecting the level-0
                        // chain (lazy table indexes are not arena offsets).
                        callback.materialize_lazy_reasons(self);
                        self.record_level0_conflict_chain(conflict_ref);
                        return self.declare_unsat();
                    }
                    // #8467: Pre-materialize lazy theory reasons at the current
                    // decision level so 1UIP resolution never encounters them.
                    callback.materialize_lazy_reasons(self);
                    let context = callback.conflict_context();
                    self.analyze_and_backtrack(conflict_ref, context, |solver, level| {
                        callback.backtrack_after_materializing_lazy_reasons(solver, level);
                    });
                    self.maybe_run_restart(callback);
                    continue;
                }

                // `take_live_pending_theory_conflict` can consume a queued
                // unit by installing it at level 0, in which case it returns
                // `None` rather than a conflict. BCP already ran earlier in
                // this iteration, so do not fall through to scheduling with
                // the newly enqueued root fact still pending. The empty-clause
                // check likewise belongs at the top of the next iteration:
                // callbacks are permitted to add a lemma and still return
                // `Continue`.
                if self.has_empty_clause || self.qhead < self.trail.len() {
                    continue;
                }
            }

            // CaDiCaL internal.cpp:290-332: else-if priority chain.
            // Exactly one scheduling action per CDCL iteration.
            // Restart has highest priority, then rephase, then lookahead,
            // then inprocessing, then decide.
            let restarted = if USE_CALLBACK {
                self.maybe_run_restart(callback)
            } else {
                self.maybe_run_restart_pure()
            };
            if restarted {
            } else if self.should_rephase() {
                if self.decision_level != 0 {
                    self.backtrack(0);
                    if USE_CALLBACK {
                        callback.backtrack_after_materializing_lazy_reasons(self, 0);
                        self.cold.lazy_materialization_failed = false;
                    }
                }
                self.rephase();
            } else if self.should_run_lookahead() {
                // #8087: Lookahead-guided decisions for hard combinatorial instances.
                // When stable mode search is stuck (high LBD ratio), run a full
                // lookahead probe to find the most informative splitting variable.
                // The result is stored and used for the next decision.
                debug_assert_eq!(self.decision_level, 0);
                self.run_lookahead_round();
                // After lookahead, level-0 propagation may have derived UNSAT
                // via failed literals.
                if self.has_empty_clause {
                    return self.declare_unsat();
                }
            } else if self.inprocessing_gates_pass() {
                if self.decision_level != 0 {
                    self.backtrack(0);
                    if USE_CALLBACK {
                        callback.backtrack_after_materializing_lazy_reasons(self, 0);
                        self.cold.lazy_materialization_failed = false;
                    }
                }
                let found_unsat = self.run_restart_inprocessing();
                if found_unsat {
                    return self.declare_unsat();
                }
                continue;
            } else if let Some(suggested) = if USE_CALLBACK && !self.relevancy_should_engage() {
                // Relevancy brancher (Increment 1): the theory-aware brancher
                // (`suggest_decision`) decides almost every atom in the eager lane,
                // and its picks are always in some unsatisfied clause (so a per-atom
                // relevancy *filter* never prunes). The lever that collapsed the
                // branch-bound Hash reds in the design prototype is the LAZY-arm
                // regime: VSIDS-only, restricted to the relevancy frontier. So while
                // the search is WANDERING (`relevancy_should_engage`), we SUPPRESS
                // theory-aware branching entirely and fall through to the
                // relevancy-restricted `pick_next_decision_variable` below — mirroring
                // the existing `wander_hand_to_vsids` latch. Eager theory PROPAGATION
                // (propagate/check) is untouched, so this stays decisions-only and
                // sound. A no-op (byte-identical) when relevancy is off.
                callback
                    .suggest_decision(self)
                    .filter(|lit| self.value(lit.variable()).is_none())
            } else {
                None
            } {
                // Extension suggested a decision (CP search heuristic)
                self.decide(suggested);
                if self.num_decisions.is_multiple_of(1000) {
                    // Deterministic decision-budget checkpoint FIRST
                    // (#ground-determinism), then the external stops.
                    if self.decision_budget_exhausted() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    // Wander-abort (hybrid arm routing): armed eager attempts
                    // return Unknown once the search wanders so the executor
                    // can re-route to the lazy arm with relevancy.
                    if self.check_wander_abort() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    if self.is_interrupted() || should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }
                if self.cold.tla_trace.is_some() {
                    self.tla_trace_step(CdclTraceState::Propagating, Some(CdclTraceAction::Decide));
                }
            } else if let Some(la_lit) = self.take_lookahead_decision() {
                // #8087: Use the lookahead-guided decision if available.
                // This overrides VSIDS for one decision after a lookahead round.
                self.decide(la_lit);
                if self.num_decisions.is_multiple_of(1000) {
                    if self.decision_budget_exhausted() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    if self.is_interrupted() || should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }
                if self.cold.tla_trace.is_some() {
                    self.tla_trace_step(CdclTraceState::Propagating, Some(CdclTraceAction::Decide));
                }
            } else if let Some(var) = if USE_CALLBACK {
                self.pick_next_decision_variable()
            } else {
                self.pick_next_decision_variable_main()
            } {
                // Ask the extension for a phase suggestion (Z3's get_phase).
                // Theory can suggest polarity consistent with its model.
                let lit = if USE_CALLBACK {
                    if let Some(phase) = callback.suggest_phase(var) {
                        if phase {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        }
                    } else {
                        self.pick_phase(var)
                    }
                } else {
                    self.pick_phase(var)
                };
                self.decide(lit);
                // Interrupt check on decision path (#3237, #6296): ensures
                // check_sat_with_timeout is respected even without conflicts.
                if self.num_decisions.is_multiple_of(1000) {
                    if self.decision_budget_exhausted() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    // Wander-abort (hybrid arm routing): see the DecideExt branch.
                    if self.check_wander_abort() {
                        return self.declare_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                    if self.is_interrupted() || should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }
                // JIT incremental compilation (#8203): periodically compile
                // more deferred pairs during search. Runs every 128 decisions
                // to amortize compilation overhead across the solve. This
                // completes lazy compilation started by jit_adaptive_compile().
                // BCP JIT incremental compilation removed (#8517).
                if self.cold.tla_trace.is_some() {
                    self.tla_trace_step(CdclTraceState::Propagating, Some(CdclTraceAction::Decide));
                }
            } else {
                if !USE_CALLBACK {
                    return self.declare_cdcl_complete_assignment_sat();
                }

                // Drain any pending theory conflict before model check (#6262).
                // A prior callback.propagate() may have set this via
                // add_theory_lemma's all-false detection without it being
                // consumed (e.g., propagate returned Continue).
                if let Some(conflict_ref) = self.take_live_pending_theory_conflict() {
                    self.conflicts_since_restart += 1;
                    self.num_conflicts += 1;
                    self.on_conflict_random_decision();
                    self.notify_observer_conflict();
                    // #8452: Pending theory conflict = theory-originated.
                    self.cold.ext_conflict_count += 1;
                    self.update_theory_conflict_ratio(true);
                    if self.decision_level == 0 {
                        // #8467: materialize before collecting the level-0
                        // chain (lazy table indexes are not arena offsets).
                        callback.materialize_lazy_reasons(self);
                        self.record_level0_conflict_chain(conflict_ref);
                        return self.declare_unsat();
                    }
                    // #8467: Pre-materialize lazy theory reasons.
                    callback.materialize_lazy_reasons(self);
                    let context = callback.conflict_context();
                    self.analyze_and_backtrack(conflict_ref, context, |solver, level| {
                        callback.backtrack_after_materializing_lazy_reasons(solver, level);
                    });
                    self.maybe_run_restart(callback);
                    continue;
                }
                // Draining may have installed an unassigned queued unit at
                // root. Re-enter BCP before asking the theory backend to check
                // a model; otherwise the model can be accepted while the root
                // unit's watch consequences are still pending.
                if self.has_empty_clause || self.qhead < self.trail.len() {
                    continue;
                }
                match callback.check_model(self) {
                    TheoryModelCheck::Sat => {
                        return self.declare_cdcl_complete_assignment_sat();
                    }
                    TheoryModelCheck::Conflict(clause) => {
                        if self.decision_level == 0 {
                            return self.declare_unsat();
                        }
                        if let Some(result) = callback.handle_conflict_clause(self, clause) {
                            return result;
                        }
                    }
                    TheoryModelCheck::Unknown(reason) => {
                        return self.declare_unknown_with_reason(reason);
                    }
                    TheoryModelCheck::AddClauses(clauses) => {
                        // #8480: Backtrack to level 0 before adding theory
                        // lemma clauses from check(). When check() is called
                        // at a complete assignment, the trail contains
                        // decisions and propagations at various levels. Adding
                        // circuit clauses (e.g., a full BV multiplication
                        // circuit with ~9500 clauses and ~2800 new variables)
                        // into this state breaks CDCL invariants:
                        //
                        // 1. With ChrBT: equivalence clauses between old
                        //    result bits (level 0) and new circuit bits
                        //    propagate at level 0 via assignment_level().
                        //    Circuit-internal propagation also cascades at
                        //    level 0. When these conflict, the solver declares
                        //    UNSAT at level 0 even though the formula is SAT.
                        //
                        // 2. Without ChrBT: conflict analysis panics with
                        //    "trail exhausted" because the conflict clause has
                        //    no literals at the current decision level.
                        //
                        // The fix: backtrack to level 0 before adding the
                        // clauses, then let BCP and the CDCL loop re-search
                        // from scratch with the additional constraints. This
                        // matches Z3's pattern where check() returns
                        // CR_CONTINUE and the SAT solver re-enters its
                        // search loop from level 0.
                        if self.decision_level > 0 {
                            self.backtrack(0);
                            callback.backtrack_after_materializing_lazy_reasons(self, 0);
                            self.cold.lazy_materialization_failed = false;
                        }
                        for clause in clauses {
                            // #inc-scoped-lemmas: scope-aware (see ext_conflict.rs).
                            self.add_theory_lemma_scoped(clause);
                        }
                        if self.has_empty_clause {
                            return self.declare_unsat();
                        }
                        // Continue the CDCL loop — BCP will process the new
                        // clauses at level 0 and begin fresh search.
                    }
                }
            }
        }
    }

    // ---- Cold diagnostic helpers ----
    // These are outlined from the hot CDCL loop to reduce its instruction
    // footprint and improve L1 icache utilization. They are only called
    // when trace_ext_conflict is enabled (a debug flag), so they should
    // never be inlined into the main loop.

    /// Trace a BCP conflict at decision level 0 (debug only).
    #[cold]
    #[inline(never)]
    fn trace_bcp_conflict_level0(&self, conflict_ref: ClauseRef) {
        let lits = self.arena.literals(conflict_ref.0 as usize);
        eprintln!(
            "[CDCL] BCP level-0 conflict! clause_ref={:?} lits={:?}",
            conflict_ref,
            lits.iter()
                .map(|l| (l.variable().index(), l.is_positive()))
                .collect::<Vec<_>>()
        );
    }

    /// Trace a BCP conflict with per-literal details (debug only).
    #[cold]
    #[inline(never)]
    fn trace_bcp_conflict_detail(&self, conflict_ref: ClauseRef) {
        let lits = self.arena.literals(conflict_ref.0 as usize);
        eprintln!(
            "[CDCL] BCP conflict at dl={} clause_ref={:?} lits={:?}",
            self.decision_level,
            conflict_ref,
            lits.iter()
                .map(|l| (l.variable().index(), l.is_positive()))
                .collect::<Vec<_>>()
        );
        for lit in lits {
            let var = lit.variable();
            let val = self.var_value_from_vals(var.index());
            let level = self.var_data[var.index()].level;
            eprintln!(
                "[CDCL]   var={} pos={} val={:?} level={}",
                var.index(),
                lit.is_positive(),
                val,
                level
            );
        }
    }

    /// Trace the theory propagation result tag (debug only).
    #[cold]
    #[inline(never)]
    fn trace_theory_result_tag(&self, result: &TheoryPropResult) {
        let tag = match result {
            TheoryPropResult::Continue => "",
            TheoryPropResult::Propagate => "Propagate",
            TheoryPropResult::Conflict(_) => "Conflict",
            TheoryPropResult::Stop => "Stop",
        };
        if !tag.is_empty() {
            eprintln!(
                "[CDCL] theory returned {} at dl={} trail_len={}",
                tag,
                self.decision_level,
                self.trail.len()
            );
        }
    }
}
