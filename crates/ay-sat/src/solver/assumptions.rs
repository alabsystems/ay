// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assumption-based solving with unsat core extraction.

use super::*;

impl Solver {
    /// Solve the formula with assumptions
    ///
    /// This performs assumption-based solving, where the given literals are
    /// treated as temporary unit clauses for this solve call only. The solver
    /// state (learned clauses, etc.) is preserved between calls.
    ///
    /// Returns:
    /// - `AssumeResult::Sat(model)` if satisfiable with the assumptions
    /// - `AssumeResult::Unsat(core)` if unsatisfiable, where `core` is a subset
    ///   of the assumptions that caused the conflict
    /// - `AssumeResult::Unknown` if the solver could not determine satisfiability
    ///
    /// The unsat core extraction follows the MiniSat approach: assumptions are
    /// assigned at decision levels 1, 2, ..., n. When a conflict occurs that
    /// requires backtracking past all assumptions (to level 0), the assumptions
    /// involved in the conflict analysis form the unsat core.
    pub fn solve_with_assumptions(&mut self, assumptions: &[Literal]) -> VerifiedAssumeResult {
        VerifiedAssumeResult::from_validated(self.solve_with_assumptions_raw(assumptions))
    }

    /// Internal assumption solve returning raw `AssumeResult`.
    fn solve_with_assumptions_raw(&mut self, assumptions: &[Literal]) -> AssumeResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        let combined = self.compose_scope_assumptions(assumptions);
        self.emit_diagnostic_assumption_batch(&combined, !self.cold.scope_selectors.is_empty());

        // CaDiCaL constrain.cpp:53 - empty constraint -> immediate UNSAT (#8207)
        if self.cold.unsat_constraint {
            let result = self.declare_unsat_assume(vec![]);
            self.emit_diagnostic_assumption_result(&result);
            self.trace_result(SolveOutcome::Unsat);
            self.finish_tla_trace();
            self.reset_constraint();
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat_assume(vec![]);
            self.emit_diagnostic_assumption_result(&result);
            self.trace_result(SolveOutcome::Unsat);
            self.finish_tla_trace();
            self.reset_constraint();
            return result;
        }

        let result = if combined.is_empty() && self.cold.constraint.is_empty() {
            match self.solve_no_assumptions(|| false) {
                SatResult::Sat(model) => self.assume_sat_from_assume_model(
                    model,
                    "solve_with_assumptions() empty-assumption fast path",
                ),
                SatResult::Unsat(_) => AssumeResult::Unsat(vec![], None),
                SatResult::Unknown => AssumeResult::Unknown,
            }
        } else {
            self.solve_with_assumptions_impl(&combined, None::<&fn() -> bool>, None, None, None)
        };

        let final_result = self.finalize_assumption_api_result(result);
        self.emit_diagnostic_assumption_result(&final_result);
        match final_result {
            AssumeResult::Sat(_) => self.trace_result(SolveOutcome::Sat),
            AssumeResult::Unsat(..) => self.trace_result(SolveOutcome::Unsat),
            AssumeResult::Unknown => self.trace_result(SolveOutcome::Unknown),
        }
        self.finish_tla_trace();
        self.reset_constraint();
        final_result
    }

    /// Solve with assumptions and an interrupt callback.
    ///
    /// The callback is checked periodically (every ~100 conflicts). If it returns
    /// `true`, solving is interrupted and `AssumeResult::Unknown` is returned.
    ///
    /// This is useful for timeout enforcement and parallel solving.
    pub fn solve_with_assumptions_interruptible<F>(
        &mut self,
        assumptions: &[Literal],
        should_stop: F,
    ) -> VerifiedAssumeResult
    where
        F: Fn() -> bool,
    {
        VerifiedAssumeResult::from_validated(
            self.solve_with_assumptions_interruptible_raw(assumptions, should_stop),
        )
    }

    /// Internal interruptible assumption solve returning raw `AssumeResult`.
    fn solve_with_assumptions_interruptible_raw<F>(
        &mut self,
        assumptions: &[Literal],
        should_stop: F,
    ) -> AssumeResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        let combined = self.compose_scope_assumptions(assumptions);
        self.emit_diagnostic_assumption_batch(&combined, !self.cold.scope_selectors.is_empty());

        // CaDiCaL constrain.cpp:53 - empty constraint -> immediate UNSAT (#8207)
        if self.cold.unsat_constraint {
            let result = self.declare_unsat_assume(vec![]);
            self.emit_diagnostic_assumption_result(&result);
            self.trace_result(SolveOutcome::Unsat);
            self.finish_tla_trace();
            self.reset_constraint();
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat_assume(vec![]);
            self.emit_diagnostic_assumption_result(&result);
            self.trace_result(SolveOutcome::Unsat);
            self.finish_tla_trace();
            self.reset_constraint();
            return result;
        }

        let result = if combined.is_empty() && self.cold.constraint.is_empty() {
            match self.solve_no_assumptions(&should_stop) {
                SatResult::Sat(model) => self.assume_sat_from_assume_model(
                    model,
                    "solve_with_assumptions_interruptible() empty-assumption fast path",
                ),
                SatResult::Unsat(_) => AssumeResult::Unsat(vec![], None),
                SatResult::Unknown => AssumeResult::Unknown,
            }
        } else {
            self.solve_with_assumptions_impl(&combined, Some(&should_stop), None, None, None)
        };

        let final_result = self.finalize_assumption_api_result(result);
        self.emit_diagnostic_assumption_result(&final_result);
        match final_result {
            AssumeResult::Sat(_) => self.trace_result(SolveOutcome::Sat),
            AssumeResult::Unsat(..) => self.trace_result(SolveOutcome::Unsat),
            AssumeResult::Unknown => self.trace_result(SolveOutcome::Unknown),
        }
        self.finish_tla_trace();
        self.reset_constraint();
        final_result
    }

    /// Unified assumption-based CDCL loop.
    ///
    /// When `should_stop` is `Some`, the callback is checked every 100 conflicts
    /// and every 1000 decisions to support interruptible solving. When `None`,
    /// the solver runs to completion.
    ///
    /// When `phase_hints` is `Some`, the extension's `suggest_decision` and
    /// `suggest_phase` methods are consulted during the decision phase, enabling
    /// theory-guided branching in scoped (push/pop) solving. This closes the gap
    /// where nonzero-scope-depth solving lost theory-aware decision guidance
    /// (#8423).
    ///
    /// When `eager_ext` is `Some`, the extension's `propagate()`, `check()`,
    /// `backtrack()`, `suggest_decision()`, and `suggest_phase()` are called
    /// during the assumption-based CDCL loop, enabling eager theory propagation
    /// in scoped (push/pop) solving (#8423). When set, this supersedes
    /// `theory_check` and `phase_hints`.
    pub(super) fn solve_with_assumptions_impl<F>(
        &mut self,
        assumptions: &[Literal],
        should_stop: Option<&F>,
        mut theory_check: Option<&mut dyn FnMut(&mut Self) -> TheoryPropResult>,
        phase_hints: Option<&dyn Extension>,
        mut eager_ext: Option<&mut dyn Extension>,
    ) -> AssumeResult
    where
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        // On second+ solve, disable destructive inprocessing (#5031).
        if self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;

        // IC3 assumption propagation cache (#8443, GipSAT pattern).
        //
        // When the cache is valid (no new clauses, push/pop, or new vars since
        // last solve), use the incremental reset which preserves level-0 trail
        // state, watches, and VSIDS heap. This avoids the expensive full reset
        // (vals.fill(0), watch rebuild, VSIDS heap rebuild) that dominates
        // overhead in IC3/PDR workloads with thousands of short queries.
        //
        // Reference: rIC3/src/gipsat/mod.rs new_round() — backtracks to level 0
        // but preserves level-0 propagations between rounds.
        // #lra-inc-engine (S1): the incremental QF_LRA engine lane grows SAT vars
        // every check-sat via the Tseitin delta; `ensure_num_vars`/`new_var`/`push`
        // invalidate `assumption_cache_valid`, which would force a full reset every
        // check-sat and defeat cross-check-sat state persistence (the whole point
        // of S1). Re-establish the cache flag for that lane ONLY — identified by
        // the dedicated `inc_engine_reset_mode` flag, set exclusively on this
        // lane's persistent solver (CHC/IC3 sets ic3_mode WITHOUT it and uses the
        // separate solve_incremental_ic3 loop), so this is byte-neutral for every
        // other caller. The flag is NOT the soundness guard:
        // `can_use_incremental_reset`'s arena-mutation checks (reconstruction /
        // inprocessing_modified / l0_gc_modified) remain and still force a full
        // ledger-rebuild reset on any destructive op. The var arrays are already
        // resized by `ensure_num_vars` before this point, so re-establishing the
        // flag after benign append-only growth is safe; scoped BVE is disabled
        // on this lane (set_bve_enabled(false) after set_ic3_mode), so no
        // scope-BVE arena projection can occur; and the delta clauses were
        // DEFERRED at add time (inc_engine_reset_mode gates the deferral in
        // add_clause_unscoped_inner), so the incremental reset's
        // attach_new_clauses_incremental builds their watches (no BCP-missed
        // conflict #8078).
        let inc_engine_lane = self.cold.inc_engine_reset_mode;
        if inc_engine_lane {
            self.cold.assumption_cache_valid = true;
        }
        let use_incremental = self.can_use_incremental_reset();
        if use_incremental {
            self.stats.assumption_cache_hits += 1;
            if inc_engine_lane {
                self.stats.ext_incremental_reset_hits += 1;
            }
            self.reset_search_state_incremental();
        } else {
            self.stats.assumption_cache_misses += 1;
            if inc_engine_lane {
                self.stats.ext_full_reset_hits += 1;
            }
            self.reset_search_state();
        }
        // #unguarded-tvalid-lemmas STAGE 0: record the assumption-prefix
        // depth (scope selectors + user assumptions) for this solve so
        // conflict analysis can classify assumption-level conflicts. Set
        // AFTER the reset above (the reset zeroes it); no-assumption solve
        // entries leave it at the reset value 0.
        self.cold.active_assumption_count = assumptions.len().min(u32::MAX as usize) as u32;
        // MiniSat assumption-based solving invariant: search must start at
        // level 0. Assumptions are assigned at levels 1..=n.
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: assumption solve starts at decision_level {} (expected 0)",
            self.decision_level,
        );
        // Handle empty formula
        if self.arena.is_empty() {
            // Even when there are no clauses, assumptions still constrain the model.
            // Satisfiable unless assumptions contain an immediate contradiction.
            let mut model = self.get_model();
            let mut first_lit_for_var: Vec<Option<Literal>> = vec![None; self.num_vars];
            // Variables whose vals[] slots we poke below (without a trail entry).
            // The pokes let finalize_sat_model read assumption values from vals[],
            // but they leave vals[] inconsistent with the (empty) level-0 trail.
            // We undo them once the model is finalized so a Sat-returning solve
            // guarantees vals[]/trail consistency (backtrack.rs post-invariant).
            let mut poked_vars: Vec<usize> = Vec::new();

            for &lit in assumptions {
                let var_idx = lit.variable().index();
                if var_idx >= self.num_vars {
                    continue;
                }
                let desired = lit.is_positive();

                if let Some(prev) = first_lit_for_var[var_idx] {
                    if prev.is_positive() != desired {
                        return AssumeResult::Unsat(vec![prev, lit], None);
                    }
                } else {
                    first_lit_for_var[var_idx] = Some(lit);
                    model[var_idx] = desired;
                    // #5571: Write to vals[] so finalize_sat_model (which rebuilds
                    // the external model from vals via e2i) sees assumption values.
                    // Without this, the empty-formula fast path sets model[] but
                    // finalize_sat_model ignores the passed-in model and reads vals[],
                    // producing a model where assumptions evaluate to false.
                    ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
                    ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
                    poked_vars.push(var_idx);
                }
            }

            // Handle constraint clause in empty-formula fast path (#8207).
            // The constraint must be checked against assumptions: if any constraint
            // literal is satisfied by assumptions, OK. If an unassigned literal
            // exists, set it in the model. If all are falsified, return UNSAT.
            if !self.cold.constraint.is_empty() {
                let mut constraint_sat = false;
                let mut unassigned_lit: Option<Literal> = None;
                for &lit in &self.cold.constraint {
                    let var_idx = lit.variable().index();
                    if var_idx >= self.num_vars {
                        continue;
                    }
                    if let Some(prev) = first_lit_for_var[var_idx] {
                        // Variable is set by assumption
                        if prev.is_positive() == lit.is_positive() {
                            constraint_sat = true;
                            break;
                        }
                        // else: falsified by assumption, continue
                    } else if unassigned_lit.is_none() {
                        // Variable is free — can be set to satisfy constraint
                        unassigned_lit = Some(lit);
                    }
                }
                if !constraint_sat {
                    if let Some(lit) = unassigned_lit {
                        // Set free variable to satisfy the constraint
                        let var_idx = lit.variable().index();
                        model[var_idx] = lit.is_positive();
                        ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
                        ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
                        poked_vars.push(var_idx);
                    } else {
                        // All constraint literals falsified by assumptions
                        self.cold.unsat_constraint = true;
                        return AssumeResult::Unsat(vec![], None);
                    }
                }
            }

            let result = self.declare_assume_sat_from_model(model);
            // Restore vals[]/trail consistency. The pokes above assigned
            // variables in vals[] at decision level 0 with NO trail entry;
            // finalize_sat_model has now consumed them, so clear them back to
            // 0. Otherwise a subsequent level-0 backtrack (e.g. the restoring
            // backtrack in probe_implications_false) samples the invariant
            // `assigned_count(vals) == trail.len()` and finds vals[] holding an
            // off-trail assignment (empty arena ⇒ empty level-0 trail).
            for var_idx in poked_vars {
                // Positive-literal slot is 2*var, negative is 2*var+1.
                ay_prefetch::val_set(&mut self.vals, var_idx * 2, 0);
                ay_prefetch::val_set(&mut self.vals, var_idx * 2 + 1, 0);
            }
            return result;
        }

        // Track number of original (irredundant) clauses for density-aware
        // protection in reduce_db. Uses irredundant_count() instead of
        // num_clauses() which includes learned clauses and inflates the
        // density ratio, causing over-aggressive protection relaxation
        // on high clause-count formulas (#8633).
        self.num_original_clauses = self.arena.irredundant_count();
        self.cold.original_clause_boundary = self.arena.len();
        self.install_and_apply_sat_whole_loop_guard_at_solver_start();

        // Initialize streaming UNSAT core bitmap (#8250).
        let num_originals = self.cold.next_original_clause_id.saturating_sub(1);
        if num_originals > 0 {
            self.cold.streaming_core_num_originals = num_originals;
            // Reuse existing allocation if capacity suffices, otherwise allocate.
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

        // Initialize watches and process initial unit clauses.
        // In the incremental path (#8443), both are skipped: watches are
        // preserved from the previous solve, and level-0 unit propagations
        // are already on the trail.
        if !use_incremental {
            self.initialize_watches();

            // CaDiCaL assume.cpp:83-85: state must be clean before initial processing
            debug_assert!(
                self.trail.is_empty(),
                "BUG: trail not empty ({} entries) after reset_search_state",
                self.trail.len(),
            );

            // Process initial unit clauses
            if let Some(conflict_ref) = self.process_initial_clauses() {
                self.record_level0_conflict_chain(conflict_ref);
                return self.declare_unsat_assume(vec![]);
            }
        } else {
            // Incremental path: level-0 trail is preserved. Verify invariant.
            debug_assert_eq!(
                self.decision_level, 0,
                "BUG: incremental reset left decision_level non-zero"
            );
            // Record how many level-0 entries were reused for stats.
            self.stats.assumption_cache_levels_reused += self.trail.len() as u64;
        }

        // Run incremental inprocessing between assumption-based solves (#8208).
        // When has_been_incremental is true (push/pop or second+ solve), run a
        // lightweight subset of inprocessing techniques (subsumption, vivification,
        // transred) to prevent clause database bloat. IC3 frame solvers accumulate
        // hundreds of learned clauses per solve call; without periodic simplification,
        // the clause database grows unboundedly and propagation weakens.
        //
        // Gate: only fire when the inprocessing conflict limit has been reached.
        // This prevents running inprocessing on every solve call (which would be
        // overhead for short solves) while ensuring simplification happens for
        // long-running incremental sessions.
        if self.cold.has_been_incremental
            && self.inprocessing_gates_pass()
            && self.run_incremental_inprocessing()
        {
            return self.declare_unsat_assume(vec![]);
        }

        // Run initial preprocessing (subsumption, probing, decompose, congruence, HTR).
        // DPLL(T) always uses assumptions, so without this, SMT/CHC solving never gets
        // preprocessing. BVE is already disabled for DPLL(T) (default_enabled=false).
        // Only run on first solve; subsequent calls (with new theory lemmas) skip.
        if self.cold.preprocess_enabled && !self.cold.has_been_incremental {
            // Freeze assumption variables so preprocessing won't eliminate them.
            // In DPLL(T), theory variables are already frozen (saturating_add is safe).
            // For direct solve_with_assumptions() callers, this prevents decompose,
            // congruence, sweep, etc. from substituting/removing assumption vars.
            for &lit in assumptions {
                let var = lit.variable();
                if var.index() < self.num_vars {
                    self.freeze(var);
                }
            }

            let preprocess_unsat = self.preprocess();

            // Melt assumption variables — the freeze was only needed during
            // preprocessing to prevent elimination. Melting restores the solver's
            // full inprocessing power for subsequent solve_with_assumptions() calls
            // where these variables may no longer be assumptions.
            // For DPLL(T), theory variables remain frozen (their own freeze_count
            // was incremented separately); our melt only reverses our increment.
            for &lit in assumptions {
                let var = lit.variable();
                if var.index() < self.num_vars {
                    self.melt(var);
                }
            }

            if preprocess_unsat {
                return self.declare_unsat_assume(vec![]);
            }

            // Reinitialize watches after preprocessing (clauses may have been modified)
            self.watches.clear();
            self.initialize_watches();
            self.qhead = 0;

            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return self.declare_unsat_assume(vec![]);
            }

            // Match solve_no_assumptions: scheduling should use the live
            // irredundant clause count after preprocessing shrink, not the
            // monotonic arena slot count captured before BVE/subsumption.
            self.num_original_clauses = self.arena.active_clause_count();

            // JIT-compile static clauses for assumption-based solving.
            // Mirrors solve_no_assumptions in solve/mod.rs.
            // Uses adaptive compilation (#8203) for size-dependent strategy.

            // Disable preprocessing for subsequent solve calls — DPLL(T) re-solves
            // with new theory lemmas; preprocessing should only run once.
            self.cold.preprocess_enabled = false;
        }

        // Track which variables are assumptions and which assumptions are "failed"
        let mut is_assumption = vec![false; self.num_vars];
        let mut assumption_lit = vec![None; self.num_vars];
        let mut failed_assumptions: Vec<Literal> = Vec::new();
        let mut is_failed: Vec<bool> = vec![false; self.num_vars];

        for &lit in assumptions {
            let var_idx = lit.variable().index();
            if var_idx < self.num_vars {
                is_assumption[var_idx] = true;
                assumption_lit[var_idx] = Some(lit);
            }
        }

        // Current assumption index we're trying to set
        let mut assumption_idx = 0;

        // IC3 assumption cache (#8443): save current assumptions and mark
        // cache valid for the next solve call. This is set here (before
        // the CDCL loop) so that even if the solve returns UNSAT or
        // Unknown, the next call knows what the previous assumptions were.
        // Any structural changes (add_clause, push, pop, new_var) between
        // solves will invalidate the cache via the already-installed hooks.
        self.cold.prev_assumptions.clear();
        self.cold.prev_assumptions.extend_from_slice(assumptions);
        self.cold.assumption_cache_valid = true;
        self.cold.assumption_cache_trail_len = self.trail.len();

        // #8423: Initialize eager extension for scoped solving.
        // When an eager extension is provided, call init() before the search
        // starts and disable destructive inprocessing (same as the unsoped
        // extension path in solve_no_assumptions_with_theory_backend).
        if let Some(ref mut ext) = eager_ext {
            ext.init();
            self.disable_extension_inprocessing();
        }

        // Main CDCL loop with assumptions
        //
        // Iteration counter for an unconditional, branch-independent interrupt
        // check at the TOP of the loop. The per-conflict (every 100 conflicts)
        // and per-decision (every 1000 decisions) `should_stop` checks below can
        // BOTH be starved by a restart-thrash regime — propagate reaches a
        // fixpoint with no conflict, `should_restart()` fires, `do_partial_restart`
        // backtracks, and the loop repeats without ever incrementing
        // `num_conflicts` or `num_decisions` (observed on bit-blasted 32-bit
        // modulo instances, where the 5s query timeout was ignored for minutes).
        // Checking `should_stop` here, amortized every 1024 iterations, makes the
        // time-based deadline fail-closed regardless of which branch dominates.
        let mut loop_iters: u64 = 0;
        loop {
            // Parity with solve_no_assumptions in solve/mod.rs:322 —
            // honor external interrupt handle and process memory limit (#6552).
            if self.is_interrupted() {
                return self.declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
            }
            // Branch-independent time-based interrupt: no CDCL branch (conflict,
            // decision, or restart) can starve this, so a query handed a wall-clock
            // `should_stop` always terminates near its deadline. `& 1023` amortizes
            // the `Instant::now()` in the closure over 1024 iterations. (inc-10:
            // also covers the continue paths — restart no-ops, theory-lemma
            // ping-pong — that increment neither num_conflicts nor num_decisions.)
            loop_iters = loop_iters.wrapping_add(1);
            if loop_iters & 1023 == 0 {
                if let Some(stop) = should_stop {
                    if stop() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }
                // #array-deadline-forward: the whole-solve deadline covers
                // callers of the NON-interruptible `solve_with_assumptions`
                // entry (should_stop = None) — e.g. the DPLL(T) assume
                // split-loop pipeline, whose per-iteration budgets bound the
                // search but not wall time. Same amortization as above.
                if self.solve_deadline_expired() {
                    return self.declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                }
            }

            // Inprocessing/theory lemmas can discover UNSAT at decision level 0
            // by deriving an empty clause. Normal BCP does not see this (empty
            // clauses are tracked via `has_empty_clause`), so check it here.
            // Parity with solve_no_assumptions and
            // solve_no_assumptions_with_theory_backend in solve/mod.rs.
            if self.has_empty_clause {
                return self.declare_unsat_assume(failed_assumptions);
            }

            // #8423 completeness (found via #lra-persist-sat): an extension
            // conflict clause that is already FULLY falsified at level > 0
            // cannot be discovered by BCP — both watched literals are already
            // assigned, so no trail event ever triggers watch propagation for
            // it. `add_theory_lemma` parks such a clause in
            // `pending_theory_conflict` "for the main solve loop" (#6262), but
            // only the unscoped theory-backend loop consumed it; this scoped
            // assumption loop never did, so `ext.propagate()`/`ext.check()`
            // rediscovered the identical theory conflict forever (livelock on
            // pushed pure-theory-UNSAT prefixes). Consume it here exactly like
            // the theory-backend fixpoint does, with the same #8480 staleness
            // validation. The centralized drain also skips every stale queue
            // head before returning a later live conflict, so a stale clause
            // cannot hide a live one long enough for a new decision.
            let assume_pending_conflict = self.take_live_pending_theory_conflict();

            // Propagate — search-specialized BCP (no probe/vivify overhead).
            if let Some(conflict_ref) = assume_pending_conflict.or_else(|| self.search_propagate())
            {
                // Conflict found
                if self.decision_level == 0 {
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat_assume(failed_assumptions);
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();

                // Deterministic `:rlimit` conflict budget + decision-budget
                // companion (checked every conflict so small budgets are
                // honored exactly, #ground-determinism).
                if self.resource_budget_exhausted() {
                    return self
                        .declare_assume_unknown_with_reason(SatUnknownReason::ResourceBudget);
                }
                // Check for interrupt every 100 conflicts
                if let Some(stop) = should_stop {
                    if self.num_conflicts.is_multiple_of(100) && stop() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                }

                // Wave 3 (#4791): use shared conflict-analysis skeleton instead
                // of inline duplicate. The before_backtrack hook updates
                // assumption_idx; the on_learned hook extracts the failed
                // assumption core while var levels are still valid
                // (pre-backtrack).
                let num_assumptions = assumptions.len() as u32;
                // #8423: Track backtrack level for eager extension callback.
                let mut ext_bt_level: Option<u32> = None;
                let has_eager_ext = eager_ext.is_some();
                self.analyze_and_backtrack_with_core_hook(
                    conflict_ref,
                    "assumption loop",
                    |_solver, bt_level| {
                        if bt_level < num_assumptions {
                            assumption_idx = bt_level as usize;
                        }
                        if has_eager_ext {
                            ext_bt_level = Some(bt_level);
                        }
                    },
                    |solver, learned_clause, actual_bt_level| {
                        // #186: a 1UIP learned clause can omit assumptions that
                        // participated in the conflict but were resolved away.
                        // When this conflict rewinds into the assumption prefix,
                        // walk the original conflict clause's implication graph
                        // to collect every contributing assumption.
                        if actual_bt_level < num_assumptions {
                            let conflict_core = solver.resolve_conflict_for_unsat_core(
                                conflict_ref,
                                &is_assumption,
                                &assumption_lit,
                            );
                            for assump_lit in conflict_core {
                                let var_idx = assump_lit.variable().index();
                                if var_idx < is_failed.len() && !is_failed[var_idx] {
                                    is_failed[var_idx] = true;
                                    failed_assumptions.push(assump_lit);
                                }
                            }
                        }

                        // Keep the previous learned-clause harvest as a cheap
                        // fallback for paths where the conflict clause is not
                        // available enough to expose all reasons.
                        for &lit in learned_clause {
                            let var_idx = lit.variable().index();
                            let var_level = solver.var_data[var_idx].level;
                            if var_level > 0
                                && var_level <= num_assumptions
                                && is_assumption[var_idx]
                            {
                                if let Some(assump_lit) = assumption_lit[var_idx] {
                                    if !is_failed[var_idx] {
                                        is_failed[var_idx] = true;
                                        failed_assumptions.push(assump_lit);
                                    }
                                }
                            }
                        }
                    },
                );
                // #8423: Notify eager extension of backtrack after conflict
                // analysis completes. Called outside the closure to avoid
                // borrow conflicts with eager_ext.
                if let (Some(ref mut ext), Some(bt_level)) = (&mut eager_ext, ext_bt_level) {
                    self.materialize_lazy_reasons_through_level_for_backtrack(&mut **ext, bt_level);
                    self.cold.lazy_materialization_failed = false;
                    ext.backtrack(bt_level);
                }
            } else {
                // No conflict

                // First, try to set any remaining assumptions
                if assumption_idx < assumptions.len() {
                    // CaDiCaL decide.cpp:575: decision level must match assumption index
                    debug_assert!(
                        (self.decision_level as usize) <= assumption_idx,
                        "BUG: decision_level {} > assumption_idx {assumption_idx} \
                         — assumptions should advance monotonically",
                        self.decision_level,
                    );
                    let assump_lit = assumptions[assumption_idx];
                    let var = assump_lit.variable();
                    let var_idx = var.index();
                    // CaDiCaL assume.cpp:30: assumption literal must be valid (non-zero index)
                    debug_assert!(
                        var_idx < self.num_vars,
                        "BUG: assumption literal {assump_lit:?} refers to var {var_idx} >= num_vars {}",
                        self.num_vars,
                    );

                    // Check if this assumption is already assigned
                    if let Some(val) = self.var_value_from_vals(var_idx) {
                        let expected = assump_lit.is_positive();
                        if val != expected {
                            // Assumption conflicts with propagated value.
                            // Use CaDiCaL-style backward resolution (#8206) to find
                            // the minimal set of assumptions that cause this conflict.
                            // The trail is fully intact here, so we can BFS through
                            // the implication graph to trace which assumptions
                            // actually participate in the proof.
                            //
                            // Seed: the conflicting variable's negation (it was
                            // propagated to the opposite of the assumption).
                            let seed = vec![assump_lit.negated()];
                            let mut core =
                                self.minimize_unsat_core(&seed, &is_assumption, &assumption_lit);

                            // SOUNDNESS (#unsat-core): `minimize_unsat_core` keys its
                            // `assumption_lit` lookup by VARIABLE, so it cannot
                            // distinguish two opposite-polarity assumptions on the
                            // same variable. When a variable is assumed both ways
                            // (e.g. `a` and `(not a)`), the BFS reports whichever
                            // single literal was registered last in `assumption_lit`
                            // — possibly the wrong polarity, and never both — yielding
                            // a returned core that is itself SATISFIABLE.
                            //
                            // The conflicting assumption `assump_lit` is, by
                            // construction, required for this conflict. Drop any
                            // same-variable literal the BFS guessed for it and add
                            // `assump_lit` back with the correct polarity.
                            core.retain(|l| l.variable() != assump_lit.variable());
                            core.push(assump_lit);

                            // If the value that triggered the conflict was set
                            // directly by the opposite-polarity assumption, that
                            // assumption is also a genuine member of the
                            // (unsatisfiable) core — include it so the returned
                            // subset is itself UNSAT.
                            //
                            // We scan `assumptions` rather than `assumption_lit`:
                            // the latter records only one literal per variable, so
                            // for a variable assumed both ways it holds whichever
                            // polarity was registered last and cannot reveal that
                            // the opposite polarity is also assumed.
                            let opposite = assump_lit.negated();
                            if matches!(self.var_reason_kind(var_idx), ReasonKind::Decision)
                                && assumptions.contains(&opposite)
                            {
                                core.push(opposite);
                            }

                            return self.declare_unsat_assume(core);
                        }
                        // Already assigned to correct value, move to next assumption
                        assumption_idx += 1;
                        continue;
                    }

                    // Make the assumption as a decision.
                    // The assumption level must match: decision_level (before
                    // decide increments it) should equal assumption_idx since
                    // each assumption gets its own level starting from 1.
                    debug_assert!(
                        self.decision_level as usize <= assumption_idx,
                        "BUG: assumption decide at decision_level {} but assumption_idx is {assumption_idx}",
                        self.decision_level,
                    );
                    assumption_idx += 1;
                    self.decide(assump_lit);
                    continue;
                }

                // Handle constraint clause (CaDiCaL decide.cpp:237-320, #8207).
                if !self.cold.constraint.is_empty() {
                    match self.handle_constraint(&failed_assumptions) {
                        constrain::ConstraintAction::Proceed => {}
                        constrain::ConstraintAction::Continue => {
                            continue;
                        }
                        constrain::ConstraintAction::Unsat(core) => {
                            return self.declare_unsat_assume(core);
                        }
                    }
                }

                // All assumptions set — invoke eager extension or theory callback
                // before deciding (#3343, #8423).
                if let Some(ref mut ext) = eager_ext {
                    // #8423: Eager extension propagation in scoped solving.
                    // This mirrors the BCP-theory fixpoint in cdcl_loop
                    // (theory_backend.rs) but simplified for the assumption loop:
                    // we call propagate() once per iteration rather than looping
                    // to a fixpoint, since the outer CDCL loop already re-enters.
                    if ext.can_propagate(self) {
                        let result = ext.propagate(self);

                        // Process VSIDS bumps for theory-conflict-driven variables.
                        if !result.bump_vars.is_empty() {
                            self.bump_theory_vars(&result.bump_vars);
                        }

                        if let Some(conflict) = result.conflict {
                            if conflict.is_empty() {
                                return self.declare_unsat_assume(failed_assumptions);
                            }
                            self.add_theory_lemma(conflict);
                            continue;
                        }

                        let has_work = !result.clauses.is_empty()
                            || !result.propagations.is_empty()
                            || !result.lazy_propagations.is_empty();

                        // Process theory propagations and lemmas.
                        for (clause, propagated) in result.propagations {
                            self.add_theory_propagation(clause, propagated);
                        }
                        for (propagated, reason_data) in result.lazy_propagations {
                            self.add_lazy_theory_propagation(propagated, reason_data);
                        }
                        for clause in result.clauses {
                            self.add_theory_lemma(clause);
                        }

                        if self.has_empty_clause {
                            return self.declare_unsat_assume(failed_assumptions);
                        }
                        if result.stop {
                            return self
                                .declare_assume_unknown_with_reason(SatUnknownReason::TheoryStop);
                        }
                        if has_work {
                            // Re-propagate to reach BCP-theory fixpoint.
                            continue;
                        }
                    }

                    // Seed theory phases after propagation quiescence. Write
                    // both the saved-phase and target-phase arrays in a single
                    // pass (one suggest_phase query per atom) instead of two
                    // full scans — same values, fewer atom-index lookups.
                    ext.seed_phase_hints_dual(&mut self.phase, &mut self.target_phase, &self.vals);
                } else if let Some(ref mut tc) = theory_check {
                    match tc(self) {
                        TheoryPropResult::Continue => {}
                        TheoryPropResult::Propagate => {
                            continue;
                        }
                        TheoryPropResult::Conflict(clause) => {
                            // Must use add_theory_lemma (not add_clause) to
                            // set up watches for mid-solve BCP participation.
                            if clause.is_empty() {
                                return self.declare_unsat_assume(failed_assumptions);
                            }
                            self.add_theory_lemma(clause);
                            continue;
                        }
                        TheoryPropResult::Stop => {
                            return self
                                .declare_assume_unknown_with_reason(SatUnknownReason::TheoryStop);
                        }
                    }
                }

                // A theory callback may add clauses directly and still return
                // `Continue`. In particular, a false or true-above-root unit
                // is queued for mandatory root installation, while an
                // unassigned unit is both queued and immediately enqueued.
                // Re-enter the top-of-loop pending-work/BCP path before any
                // restart, decision, or SAT completion. This also makes an
                // empty lemma fail closed instead of validating a model
                // against formula state the search never consumed.
                if self.has_empty_clause
                    || !self.pending_theory_conflicts.is_empty()
                    || self.qhead < self.trail.len()
                {
                    continue;
                }

                // All assumptions set, continue with regular solving
                if self.should_restart() {
                    self.stats.record_pending_restart_attribution();
                    // For assumption-based solving, only restart back to assumption level
                    // Don't run inprocessing during assumption solving to preserve state
                    self.do_partial_restart(assumptions.len() as u32);
                    // Check if we should rephase (change phase selection strategy)
                    if self.should_rephase() {
                        self.rephase();
                    }
                    // #8423: Notify eager extension of restart-to-assumption-level.
                    if let Some(ref mut ext) = eager_ext {
                        self.materialize_lazy_reasons_through_level_for_backtrack(
                            &mut **ext,
                            assumptions.len() as u32,
                        );
                        self.cold.lazy_materialization_failed = false;
                        ext.backtrack(assumptions.len() as u32);
                    }
                } else if let Some(hint_lit) = if self.relevancy_should_engage() {
                    // Relevancy brancher (Increment 1): while the search is WANDERING
                    // suppress theory-aware branching and let the relevancy-restricted
                    // `pick_next_decision_variable` drive (see theory_backend.rs for
                    // the full rationale — the eager theory brancher's picks are always
                    // relevant, so a per-atom filter is inert; the lever is the
                    // VSIDS-only, frontier-restricted regime). Decisions-only; eager
                    // propagation untouched. A no-op (byte-identical) when off.
                    None
                } else {
                    // #8423: Theory-guided branching in scoped solving.
                    // Eager extension or PhaseHintExtension suggests theory atoms
                    // before VSIDS, matching the behavior of the extension-based
                    // solve path at scope_depth == 0.
                    eager_ext
                        .as_deref()
                        .and_then(|ext| ext.suggest_decision(self))
                        .or_else(|| phase_hints.and_then(|ph| ph.suggest_decision(self)))
                } {
                    self.decide(hint_lit);
                    // Wander-abort (hybrid arm routing): theory-hint decisions
                    // dominate the eager DPLL(T) lane, so this branch needs its
                    // own trip check — the pick_next_decision_variable branch
                    // below is starved when hints fire every decision. Inert
                    // (single disarmed-flag test per 1000 decisions) unless the
                    // executor armed the trip-wire for a hybrid eager attempt.
                    if self.num_decisions.is_multiple_of(1000) && self.check_wander_abort() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::ResourceBudget);
                    }
                } else if let Some(var) = self.pick_next_decision_variable() {
                    let lit = if let Some(phase) = eager_ext
                        .as_deref()
                        .and_then(|ext| ext.suggest_phase(var))
                        .or_else(|| phase_hints.and_then(|ph| ph.suggest_phase(var)))
                    {
                        if phase {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        }
                    } else {
                        self.pick_phase(var)
                    };
                    self.decide(lit);

                    // Keep interrupt semantics consistent with solve_no_assumptions:
                    // SAT-leaning runs can make many decisions with no conflicts.
                    // Parity with solve/mod.rs:363 — check is_interrupted() in
                    // decision branch for memory limit and external handle (#6552).
                    if self.is_interrupted() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                    // Deterministic decision-budget checkpoint FIRST
                    // (#ground-determinism), then the external stop.
                    if self.num_decisions.is_multiple_of(1000) {
                        if self.decision_budget_exhausted() {
                            return self.declare_assume_unknown_with_reason(
                                SatUnknownReason::ResourceBudget,
                            );
                        }
                        // Wander-abort (hybrid arm routing): armed eager attempts
                        // return Unknown once the search wanders so the executor
                        // can re-route to the lazy arm with relevancy.
                        if self.check_wander_abort() {
                            return self.declare_assume_unknown_with_reason(
                                SatUnknownReason::ResourceBudget,
                            );
                        }
                        if let Some(stop) = should_stop {
                            if stop() {
                                return self.declare_assume_unknown_with_reason(
                                    SatUnknownReason::Interrupted,
                                );
                            }
                        }
                    }
                } else {
                    // All variables assigned — check eager extension before
                    // declaring SAT (#8423).
                    if let Some(ref mut ext) = eager_ext {
                        match ext.check(self) {
                            ExtCheckResult::Sat => {}
                            ExtCheckResult::Conflict(clause) => {
                                if clause.is_empty() {
                                    return self.declare_unsat_assume(failed_assumptions);
                                }
                                self.add_theory_lemma(clause);
                                continue;
                            }
                            ExtCheckResult::Unknown => {
                                return self.declare_assume_unknown_with_reason(
                                    SatUnknownReason::ExtensionUnknown,
                                );
                            }
                            ExtCheckResult::AddClauses(clauses) => {
                                for clause in clauses {
                                    self.add_theory_lemma(clause);
                                }
                                if self.has_empty_clause {
                                    return self.declare_unsat_assume(failed_assumptions);
                                }
                                continue;
                            }
                        }
                    }
                    return self.declare_assume_sat_from_current_assignment();
                }
            }
        }
    }

    /// Resolve the current conflict backward through the implication graph to
    /// collect all assumptions that contributed to it (#186).
    ///
    /// This is the assumption-core counterpart of CDCL conflict analysis: start
    /// from the concrete conflict clause, then follow each assigned variable's
    /// reason until reaching assumption decisions. Unlike scanning the 1UIP
    /// learned clause, this retains assumptions that were resolved away while
    /// deriving that learned clause.
    pub(super) fn resolve_conflict_for_unsat_core(
        &self,
        conflict_ref: ClauseRef,
        is_assumption: &[bool],
        assumption_lit: &[Option<Literal>],
    ) -> Vec<Literal> {
        if !self.arena.is_active(conflict_ref.0 as usize) {
            return vec![];
        }
        let seed_lits = self.arena.literals(conflict_ref.0 as usize);
        self.minimize_unsat_core(seed_lits, is_assumption, assumption_lit)
    }

    /// CaDiCaL-style backward resolution to minimize the UNSAT core (#8206).
    ///
    /// Starting from seed literals (typically from the conflict that triggered
    /// UNSAT), BFS backward through the implication graph to find which
    /// assumptions actually participate in the proof of unsatisfiability.
    ///
    /// At each variable in the BFS:
    /// - Level 0 variables are skipped (implied by root-level propagation)
    /// - Variables with reason clauses are expanded (their antecedent literals
    ///   are added to the BFS queue)
    /// - Decision variables that are assumptions are added to the minimal core
    ///
    /// This produces smaller cores than the shallow one-level-deep extraction,
    /// which is critical for IC3/PDR cube generalization where core size
    /// compounds exponentially across frame depths.
    ///
    /// Reference: CaDiCaL assume.cpp:270-307 (`failing()` BFS loop)
    pub(super) fn minimize_unsat_core(
        &self,
        seed_lits: &[Literal],
        is_assumption: &[bool],
        assumption_lit: &[Option<Literal>],
    ) -> Vec<Literal> {
        if seed_lits.is_empty() {
            return vec![];
        }

        let nv = self.num_vars;
        let mut seen = vec![false; nv];
        // BFS queue: variable indices to process
        let mut queue: Vec<usize> = Vec::new();
        let mut core: Vec<Literal> = Vec::new();
        let mut in_core = vec![false; nv];

        // Seed the BFS with the seed literals' variables.
        for &lit in seed_lits {
            let var_idx = lit.variable().index();
            if var_idx < nv && !seen[var_idx] {
                seen[var_idx] = true;
                queue.push(var_idx);
            }
        }

        // BFS through the implication graph
        let mut head = 0;
        while head < queue.len() {
            let var_idx = queue[head];
            head += 1;

            let level = self.var_data[var_idx].level;

            // Level 0 variables are unconditionally implied — skip them.
            if level == 0 {
                continue;
            }

            match self.var_reason_kind(var_idx) {
                ReasonKind::Decision => {
                    // Decision variable: if it's an assumption, add to core.
                    if var_idx < is_assumption.len() && is_assumption[var_idx] {
                        // SOUNDNESS (#unsat-core-polarity, A7): `assumption_lit`
                        // stores ONE literal per VARIABLE, so when the caller
                        // assumes a variable at both polarities in the same
                        // query (`(check-sat-assuming (a b (not a)))`) it holds
                        // whichever was registered LAST. Reporting that literal
                        // here can name the polarity that took no part in this
                        // conflict, producing a "core" that is itself
                        // SATISFIABLE with the assertions — a certificate
                        // consumer (MUS extraction, assumption-based CEGAR, BMC)
                        // would then treat a satisfiable set as unsatisfiable.
                        //
                        // An assumption reaches this arm only by having been
                        // DECIDED (`self.decide(assump_lit)` in the assumption
                        // prefix), so the trail value IS the polarity that
                        // participated. Derive the literal from the assignment;
                        // fall back to the registered literal only if the
                        // variable is somehow unassigned (it cannot be while it
                        // is a decision, but the map keeps the walk total).
                        let participating = self.var_value_from_vals(var_idx).map_or(
                            assumption_lit[var_idx],
                            |value| {
                                let var = Variable::new(var_idx as u32);
                                Some(if value {
                                    Literal::positive(var)
                                } else {
                                    Literal::negative(var)
                                })
                            },
                        );
                        if let Some(a_lit) = participating {
                            if !in_core[var_idx] {
                                in_core[var_idx] = true;
                                core.push(a_lit);
                            }
                        }
                    }
                }
                ReasonKind::Clause(cref) => {
                    // Clause reason: expand all literals in the reason clause.
                    for &reason_lit in self.arena.literals(cref.0 as usize) {
                        let rv = reason_lit.variable().index();
                        if rv < nv && !seen[rv] {
                            seen[rv] = true;
                            queue.push(rv);
                        }
                    }
                }
                ReasonKind::BinaryLiteral(other_lit) => {
                    // Binary clause reason: expand the other literal's variable.
                    let rv = other_lit.variable().index();
                    if rv < nv && !seen[rv] {
                        seen[rv] = true;
                        queue.push(rv);
                    }
                }
                ReasonKind::LazyTheory(_) => {
                    // Lazy theory reasons should have been pre-materialized
                    // before conflict analysis. If we reach here during
                    // assumption core extraction, treat as decision (no expansion).
                    // Assumption-based solving does not use lazy propagations
                    // in practice (#8467).
                }
            }
        }

        core
    }

    /// Partial restart - only restart back to a given level (for assumption-based solving)
    pub(super) fn do_partial_restart(&mut self, min_level: u32) {
        if self.decision_level <= min_level {
            // No search decisions above the assumption prefix to undo, but the
            // pending-restart signal MUST still be consumed (inc-10 root cause):
            // `should_restart()` early-returns false only when
            // `conflicts_since_restart == 0`. Without this reset, the
            // assumption CDCL loop livelocks — every iteration takes the
            // restart branch (a no-op), produces neither conflicts nor
            // decisions, and therefore never reaches either `should_stop`
            // checkpoint. Measured: a 5s-capped IMC bmc_check on
            // nest-len.c_000 (k=4 iter=3) spun here for ~270s.
            // `do_restart_impl` (restart.rs) resets this unconditionally for
            // exactly the same reason.
            self.conflicts_since_restart = 0;
            return;
        }
        // Partial restart must not undo assumption assignments
        debug_assert!(
            min_level > 0,
            "BUG: partial restart to level 0 would undo assumptions",
        );
        // Decision level must be above min_level (checked above, but assert for clarity)
        debug_assert!(
            self.decision_level > min_level,
            "BUG: partial restart from level {} to min_level {min_level} — already at or below",
            self.decision_level,
        );

        // Backtrack to just above the minimum level
        self.backtrack(min_level);
        // Post-condition: decision level must be exactly min_level after backtrack
        debug_assert_eq!(
            self.decision_level, min_level,
            "BUG: after partial restart backtrack, decision_level {} != min_level {min_level}",
            self.decision_level,
        );
        self.conflicts_since_restart = 0;
        self.cold.restarts += 1;

        // Domain-epoch hardness accounting, shared with the full-restart
        // paths in restart.rs: partial restarts are restart events too and
        // must feed the same bucket-queue hardness signal (#8476).
        self.bucket_queue_on_restart();

        // Update Luby sequence
        self.cold.luby_idx += 1;
        let _ = self.complete_branch_heuristic_epoch_if_needed();
    }

    #[inline]
    pub(super) fn compose_scope_assumptions(&self, assumptions: &[Literal]) -> Vec<Literal> {
        let mut combined = Vec::with_capacity(self.cold.scope_selectors.len() + assumptions.len());
        combined.extend(
            self.cold
                .scope_selectors
                .iter()
                .copied()
                .map(Literal::negative),
        );
        combined.extend_from_slice(assumptions);
        combined
    }
}

#[cfg(test)]
#[path = "assumptions_tests.rs"]
mod tests;
