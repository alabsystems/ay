// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! IC3-optimized solve path for incremental assumption-based queries.
//!
//! IC3/PDR makes thousands of short SAT queries per second, each with
//! different assumptions but the same base clause set. The standard
//! `solve_with_assumptions` path carries overhead from features that IC3
//! doesn't need: inprocessing scheduling, theory callbacks, proof logging,
//! TLA tracing, progress reporting, lucky phases, walk-based initialization,
//! Glucose EMA restart heuristics, observer notifications, etc.
//!
//! The search driver here is the standard assumption-based incremental CDCL
//! loop: unit propagation to fixpoint, first-UIP conflict learning with
//! non-chronological backjumping, activity-driven decisions with saved
//! phases, and failing-assumption core extraction (Eén & Sörensson, "An
//! Extensible SAT-solver", SAT 2003; Moskewicz et al., "Chaff: Engineering
//! an Efficient SAT Solver", DAC 2001). In IC3 mode, restarts follow the
//! Luby universal schedule (Luby, Sinclair & Zuckerman, "Optimal Speedup of
//! Las Vegas Algorithms", Information Processing Letters 47(4), 1993),
//! scaled by `IC3_RESTART_BASE` conflicts per unit — the fixed-base Luby
//! policy popularized by MiniSat — while non-IC3 callers keep the solver's
//! Glucose-style LBD-EMA restart policy.

use super::super::*;

/// `y` raised to the Luby-sequence exponent for the 0-based restart counter
/// `x` (counter value `x` is position `i = x + 1` of the published sequence).
///
/// The Luby sequence u(1), u(2), ... = 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, ... is
/// the universal restart schedule of Luby, Sinclair & Zuckerman, "Optimal
/// Speedup of Las Vegas Algorithms", Information Processing Letters 47(4),
/// 1993, defined by
///
/// - u(i) = 2^(k-1)             when i = 2^k - 1 for some k >= 1,
/// - u(i) = u(i - 2^(k-1) + 1)  for the unique k with 2^(k-1) <= i < 2^k - 1.
///
/// `luby(y, x)` returns y^e where u(x + 1) = 2^e, so with `y = 2.0` it is
/// the sequence value itself. Total and panic-free for every `u32` counter
/// (the position is widened to `u64`, so even `x == u32::MAX` cannot
/// overflow). See also the integer variant `Solver::get_luby` in
/// `solver/restart.rs`, which states the same published recurrence.
pub(super) fn luby(y: f64, x: u32) -> f64 {
    // 1-based position into the published sequence.
    let mut i = u64::from(x) + 1;
    // Apply the second recurrence case until the position has the form
    // 2^k - 1; then the first case yields the exponent directly. When i is
    // not of that form, the unique k of the second case has 2^(k-1) equal
    // to the highest power of two <= i, so clearing that block (subtracting
    // 2^(k-1) - 1) applies the case exactly. Every step shortens the
    // position's bit length, so at most 33 steps run for any u32 counter.
    loop {
        let next = i + 1;
        if next.is_power_of_two() {
            // i = 2^k - 1 with k = trailing_zeros(i + 1); u(i) = 2^(k-1).
            let exponent = next.trailing_zeros() - 1;
            return y.powi(exponent as i32);
        }
        let high_bit = 1u64 << i.ilog2();
        i -= high_bit - 1;
    }
}

/// Conflicts per Luby unit for IC3-mode restarts: restart number r (0-based)
/// gets a budget of `luby(2.0, r) * IC3_RESTART_BASE` conflicts. Scaling the
/// Luby schedule by a fixed conflict base is the textbook Luby-restart
/// policy (Eén & Sörensson, "An Extensible SAT-solver", SAT 2003).
const IC3_RESTART_BASE: f64 = 100.0;

impl Solver {
    /// IC3-optimized incremental solve with assumptions.
    ///
    /// This is the fast path for IC3/PDR workloads. It skips:
    /// - Inprocessing scheduling and execution except scoped BVE
    /// - Theory/extension callbacks
    /// - Proof logging and LRAT chain collection
    /// - TLA tracing and diagnostic emission
    /// - Progress reporting and observer notifications
    /// - Lucky phases, walk-based initialization, Jeroslow-Wang phases
    /// - Glucose EMA restart computation
    /// - Streaming UNSAT core bitmap setup
    /// - Cold restart checks
    /// - DIP-ERCL extension variable detection
    /// - Rephasing and lookahead
    ///
    /// Caller requirements:
    /// - Call `set_ic3_mode()` once during frame-solver setup, before the
    ///   first IC3 query. It may be called before or after adding permanent
    ///   clauses; no warm-up solve is required.
    /// - Refresh `set_domain()` before domain-restricted cubes. Calling this
    ///   method with no active domain remains valid, but uses full BCP.
    /// - Do not re-enable preprocessing, proof logging, chronological
    ///   backtracking, or inprocessing after `set_ic3_mode()`.
    ///
    /// When IC3 mode is active, conflict handling routes through
    /// `analyze_and_backtrack_ic3()` and domain BCP dispatch uses
    /// `propagate_bcp_ic3()` when a domain is active above level 0.
    ///
    /// The method returns `VerifiedAssumeResult` for API consistency.
    pub fn solve_incremental_ic3(&mut self, assumptions: &[Literal]) -> VerifiedAssumeResult {
        let result = self.solve_incremental_ic3_raw(assumptions);

        // Enforce learned clause cap after each solve (#8672).
        // The cap check is amortized (runs every IC3_LEARNED_CAP_CHECK_INTERVAL
        // solves) and protects against unbounded clause growth across 10K+
        // queries. This complements ic3_between_solve_gc (which fires during
        // reset_search_state) with a tighter, hard-cap policy.
        if self.cold.ic3_mode {
            if self.decision_level > 0 {
                self.backtrack_ic3(0);
            }
            self.ic3_enforce_learned_cap();

            // Memory-proportional reduce (#8673): complements the count-based
            // cap with an arena memory check. Many medium-length clauses can
            // stay under the count cap while consuming significant arena memory.
            // This fires when arena words exceed IC3_MEMORY_PRESSURE_ARENA_FACTOR
            // times the baseline captured at IC3 mode entry.
            self.ic3_memory_pressure_reduce();
        }

        VerifiedAssumeResult::from_validated(result)
    }

    /// Raw IC3 incremental solve returning `AssumeResult`.
    fn solve_incremental_ic3_raw(&mut self, assumptions: &[Literal]) -> AssumeResult {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        // #8754: finalize_sat_fail_count is STICKY across solve() calls.

        // IC3 fast path (#8569 Gap 1): avoid per-query Vec allocation when no
        // scopes are active and no constraint activation variable is set. This
        // is the common case for IC3/PDR where push/pop is not used and
        // add_constrained_clause is not used. compose_scope_assumptions would
        // allocate a Vec and copy assumptions every call for no benefit.
        let needs_composition =
            !self.cold.scope_selectors.is_empty() || self.cold.ic3_constrain_act.is_some();

        let combined_storage: Vec<Literal>;
        let assumptions: &[Literal] = if needs_composition {
            // Compose scope assumptions (for push/pop compatibility).
            let mut combined = self.compose_scope_assumptions(assumptions);

            // IC3 constraint activation (#8662 Gap 3): if a constraint activation
            // variable is set, prepend it to assumptions so constrained clauses
            // (added via add_constrained_clause) are active during this query.
            // The activation literal is placed FIRST so it's decided at the lowest
            // level, ensuring constrained clauses are active throughout the search.
            if let Some(act_var) = self.cold.ic3_constrain_act {
                let act_lit = Literal::positive(act_var);
                // Only add if not already present (caller may have included it).
                if !combined.contains(&act_lit) {
                    combined.insert(0, act_lit);
                }
            }

            combined_storage = combined;
            &combined_storage
        } else {
            assumptions
        };

        // Early exits.
        if self.has_empty_clause {
            return self.declare_unsat_assume(vec![]);
        }
        if self.cold.unsat_constraint {
            return self.declare_unsat_assume(vec![]);
        }

        // Disable destructive inprocessing on second+ solve.
        // IC3 fast path: set_ic3_mode() already called disable_all_inprocessing(),
        // which is a superset. Skip the redundant call.
        if !self.cold.ic3_mode && self.cold.has_solved_once {
            self.disable_destructive_inprocessing();
        }
        self.cold.has_solved_once = true;

        // IC3 incremental reset: preserve level-0 trail, watches, VSIDS heap.
        // This is the key optimization — avoids O(num_vars) reset per solve.
        // In IC3 mode, can_use_incremental_reset is O(1) (fast path skips
        // the O(clauses) arena scan). See #8569 Gap 1.
        if self.can_use_incremental_reset() {
            self.stats.assumption_cache_hits += 1;
            self.reset_search_state_incremental();
        } else {
            self.stats.assumption_cache_misses += 1;
            self.reset_search_state();

            // Full reset path: must reinitialize watches and process unit clauses.
            self.initialize_watches();
            if let Some(conflict_ref) = self.process_initial_clauses() {
                self.record_level0_conflict_chain(conflict_ref);
                return self.declare_unsat_assume(vec![]);
            }
        }

        debug_assert_eq!(self.decision_level, 0);

        // Track irredundant clause count for density-aware protection in
        // reduce_db (#8633). Without this, num_original_clauses stays at 0
        // (from reset_search_state) and reduce_db fires with incorrect
        // density calculations: the SMALL_FORMULA_REDUCE_CAP_THRESHOLD check
        // computes cap = max(2*0, 300) = 300 instead of 2*actual_irredundant,
        // causing over-aggressive clause deletion scheduling. The density-aware
        // protection also uses num_original_clauses to decide whether to relax
        // CORE_LBD protection on dense formulas — with 0 it never fires.
        //
        // Mirrors assumptions.rs:299 (solve_with_assumptions_impl) and
        // solve/mod.rs:331 (solve_no_assumptions).
        self.num_original_clauses = self.arena.irredundant_count();

        // Lazy baseline capture for IC3 memory pressure tracking (#8673).
        // If set_ic3_mode() was called before clauses were added, the baseline
        // is zero. Capture it on the first solve when the arena is populated.
        if self.cold.ic3_mode && self.cold.ic3_baseline_arena_words == 0 {
            let arena_words = self.arena.len();
            if arena_words > 0 {
                self.cold.ic3_baseline_arena_words = arena_words;
            }
        }

        // Scoped BVE for IC3 (#8503): run incremental inprocessing (including
        // scoped BVE) when a push() scope is active and enough conflicts have
        // accumulated. This is the IC3-path equivalent of the inprocessing
        // gate in `solve_with_assumptions()` (assumptions.rs:354-357).
        //
        // Without this, IC3/PDR workloads that do thousands of short solves
        // accumulate clause bloat with no BVE to reduce it, because the
        // IC3 fast path bypasses the regular `solve_with_assumptions` entry
        // point where incremental inprocessing fires.
        //
        // Guard: only run when has_scoped_bve() is true (push() was called)
        // AND the inprocessing conflict limit has been reached. The gates
        // prevent running on every solve call (which would add overhead to
        // the short queries that IC3 relies on for speed).
        //
        // In IC3 mode this remains bounded: `set_ic3_mode()` leaves only BVE
        // enabled, and `run_incremental_inprocessing()` runs BVE only when
        // `has_scoped_bve()` is true.
        if self.has_scoped_bve()
            && self.inprocessing_gates_pass()
            && self.run_incremental_inprocessing()
        {
            return self.declare_unsat_assume(vec![]);
        }

        // Handle empty formula.
        if self.arena.is_empty() {
            return self.ic3_handle_empty_formula(assumptions);
        }

        // Set up assumption tracking using persistent buffers (#8569 Gap 1).
        //
        // Previously allocated 3 x O(num_vars) vectors per query:
        //   is_assumption: vec![false; nv]
        //   assumption_lit: vec![None; nv]
        //   is_failed: vec![false; nv]
        // For 10K-variable systems, this was ~120KB of allocation per query.
        //
        // Now we use persistent buffers on `cold` that are lazily grown to
        // num_vars and sparse-cleared in O(prev_assumptions) by tracking
        // which indices were set.
        let nv = self.num_vars;

        // Sparse-clear entries set by the previous query (O(prev_assumptions),
        // not O(num_vars)). Only clear indices we actually wrote to.
        for &idx in &self.cold.ic3_assumption_indices {
            if idx < self.cold.ic3_is_assumption.len() {
                self.cold.ic3_is_assumption[idx] = false;
                self.cold.ic3_assumption_lit[idx] = None;
            }
        }
        self.cold.ic3_assumption_indices.clear();

        // Lazily grow buffers to num_vars if needed. This only reallocates
        // when the solver adds new variables, not on every query.
        if self.cold.ic3_is_assumption.len() < nv {
            self.cold.ic3_is_assumption.resize(nv, false);
            self.cold.ic3_assumption_lit.resize(nv, None);
        }

        // Set assumption flags (O(assumptions), not O(num_vars)).
        for &lit in assumptions.iter() {
            let vi = lit.variable().index();
            if vi < nv {
                self.cold.ic3_is_assumption[vi] = true;
                self.cold.ic3_assumption_lit[vi] = Some(lit);
                self.cold.ic3_assumption_indices.push(vi);
            }
        }

        let mut failed_assumptions: Vec<Literal> = Vec::new();
        let mut assumption_idx: usize = 0;

        // Update IC3 assumption cache for next call.
        self.cold.prev_assumptions.clear();
        self.cold.prev_assumptions.extend_from_slice(assumptions);
        self.cold.assumption_cache_valid = true;
        self.cold.assumption_cache_trail_len = self.trail.len();

        // ── Search driver ────────────────────────────────────────────────
        //
        // Assumption-based incremental CDCL search (Eén & Sörensson, SAT
        // 2003; Moskewicz et al., DAC 2001): propagate to fixpoint; on a
        // conflict learn a first-UIP clause and backjump; otherwise enqueue
        // the next pending assumption, and once every assumption holds,
        // decide by activity with saved phases. Restarts come in two
        // regimes: IC3 mode runs a per-query Luby schedule (Luby, Sinclair
        // & Zuckerman 1993) scaled by IC3_RESTART_BASE; non-IC3 (BMC)
        // callers keep the solver's Glucose-style LBD-EMA policy.
        let num_assumptions = assumptions.len();
        let luby_restarts = self.cold.ic3_mode;
        let mut restarts_this_query: u32 = 0;
        let mut conflicts_since_query_restart: u64 = 0;
        let mut restart_budget = (luby(2.0, restarts_this_query) * IC3_RESTART_BASE) as u64;

        loop {
            // Parity with the general assumption driver: honor the external
            // interrupt handle and the process-memory gate on every
            // iteration, including conflict-free SAT descents.
            if self.is_interrupted() {
                return self.declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
            }
            // Learned level-0 units and incrementally added clauses can
            // uncover a root contradiction between propagation calls; it is
            // tracked out-of-band in `has_empty_clause` (BCP never sees an
            // empty clause), so check it before propagating.
            if self.has_empty_clause {
                return self.declare_unsat_assume(failed_assumptions);
            }

            if let Some(conflict_ref) = self.search_propagate() {
                // ── Conflict ──
                if self.decision_level == 0 {
                    // Independent of every decision: UNSAT at the root.
                    // Record level-0 proof bookkeeping (a no-op unless proof
                    // logging is active) and fail with whatever assumption
                    // core has been established so far.
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat_assume(failed_assumptions);
                }

                self.num_conflicts += 1;
                self.conflicts_since_restart += 1;
                conflicts_since_query_restart += 1;

                // First-UIP learning + non-chronological backjump. The hook
                // runs before the backjump, while variable levels are still
                // valid: when the conflict rewinds into the assumption
                // prefix, harvest every assumption that contributed (the
                // resolution walk keeps assumptions that the 1UIP derivation
                // resolved away, #186); in non-IC3 mode, also grade the
                // learned clause for the LBD-EMA restart policy.
                let mut learned_lbd: u32 = 0;
                self.analyze_and_backtrack_ic3(conflict_ref, |solver, learned_clause, bt_level| {
                    if (bt_level as usize) < num_assumptions {
                        let conflict_core = solver.resolve_conflict_for_unsat_core(
                            conflict_ref,
                            &solver.cold.ic3_is_assumption,
                            &solver.cold.ic3_assumption_lit,
                        );
                        for assump_lit in conflict_core {
                            if !failed_assumptions.contains(&assump_lit) {
                                failed_assumptions.push(assump_lit);
                            }
                        }
                        // Fallback harvest straight from the learned clause,
                        // for contributing assumptions the conflict-clause
                        // walk cannot expose.
                        for &lit in learned_clause {
                            let var_idx = lit.variable().index();
                            let var_level = solver.var_data[var_idx].level;
                            if var_level > 0
                                && (var_level as usize) <= num_assumptions
                                && var_idx < solver.cold.ic3_is_assumption.len()
                                && solver.cold.ic3_is_assumption[var_idx]
                            {
                                if let Some(assump_lit) = solver.cold.ic3_assumption_lit[var_idx] {
                                    if !failed_assumptions.contains(&assump_lit) {
                                        failed_assumptions.push(assump_lit);
                                    }
                                }
                            }
                        }
                    }
                    if !luby_restarts {
                        learned_lbd = solver.clause_lbd_from_levels(learned_clause);
                    }
                });

                // The backjump may have unwound assumption decisions. Every
                // assumption with index < decision_level is still enqueued
                // (assumption i is always assigned at a level <= i + 1), so
                // resuming the consultation cursor at the new decision level
                // re-examines exactly the ones that may have been undone.
                assumption_idx = assumption_idx.min(self.decision_level as usize);

                if !luby_restarts && learned_lbd > 0 {
                    self.update_lbd_ema(learned_lbd);
                }

                // Per-conflict periodic duties: poll the process-memory gate
                // (consumed by the loop-top interrupt check) and reduce the
                // learned database when its policy fires.
                self.poll_process_memory_limit();
                if self.should_reduce_db() {
                    self.reduce_db();
                }
            } else {
                // ── No conflict: extend the assignment ──
                //
                // Consult pending assumptions first, in the order given. A
                // satisfied assumption is passed over without consuming a
                // decision level; a falsified one fails the query with a
                // core; an unassigned one becomes the next decision.
                if assumption_idx < num_assumptions {
                    debug_assert!(
                        (self.decision_level as usize) <= assumption_idx,
                        "BUG: decision_level {} > assumption_idx {assumption_idx} \
                         — assumptions should advance monotonically",
                        self.decision_level,
                    );
                    let assump_lit = assumptions[assumption_idx];
                    let var_idx = assump_lit.variable().index();
                    debug_assert!(
                        var_idx < self.num_vars,
                        "BUG: assumption literal {assump_lit:?} refers to var {var_idx} \
                         >= num_vars {}",
                        self.num_vars,
                    );

                    if let Some(val) = self.var_value_from_vals(var_idx) {
                        if val != assump_lit.is_positive() {
                            // The assumption is false under the current
                            // assignment. Trace the implication graph behind
                            // the conflicting value for a minimal failing
                            // subset of the assumptions (backward BFS in
                            // `minimize_unsat_core`).
                            let seed = vec![assump_lit.negated()];
                            let mut core = self.minimize_unsat_core(
                                &seed,
                                &self.cold.ic3_is_assumption,
                                &self.cold.ic3_assumption_lit,
                            );

                            // SOUNDNESS (#unsat-core): the walk keys its
                            // assumption lookup by VARIABLE, so it cannot
                            // distinguish two opposite-polarity assumptions
                            // on the same variable. The conflicting
                            // assumption itself is required by construction:
                            // drop any same-variable literal the walk
                            // guessed and re-add the correct polarity.
                            core.retain(|l| l.variable() != assump_lit.variable());
                            core.push(assump_lit);

                            // When the conflicting value was set directly by
                            // the opposite-polarity assumption, include that
                            // assumption too so the returned subset is
                            // itself unsatisfiable. Scan `assumptions`
                            // rather than the per-variable registry: the
                            // registry holds one literal per variable and
                            // cannot reveal that both polarities are
                            // assumed.
                            let opposite = assump_lit.negated();
                            if matches!(self.var_reason_kind(var_idx), ReasonKind::Decision)
                                && assumptions.contains(&opposite)
                            {
                                core.push(opposite);
                            }

                            return self.declare_unsat_assume(core);
                        }
                        // Already true: passed over without a decision level.
                        assumption_idx += 1;
                    } else {
                        // Unassigned: the assumption is the next decision.
                        assumption_idx += 1;
                        self.decide(assump_lit);
                    }
                    continue;
                }

                // All assumptions hold. Restart checks run at propagation
                // fixpoint, so the latest learned clause has asserted its
                // literal first, and they never unwind the assumption
                // prefix.
                if luby_restarts {
                    if conflicts_since_query_restart >= restart_budget {
                        // Luby restart (Luby, Sinclair & Zuckerman 1993):
                        // budgets reset per query and grow along the
                        // schedule; the restart undoes every decision above
                        // the assumption prefix.
                        restarts_this_query = restarts_this_query.saturating_add(1);
                        conflicts_since_query_restart = 0;
                        restart_budget = (luby(2.0, restarts_this_query) * IC3_RESTART_BASE) as u64;

                        let prefix = num_assumptions as u32;
                        if self.decision_level > prefix {
                            self.backtrack_ic3(prefix);
                            self.cold.restarts += 1;
                        }
                        self.conflicts_since_restart = 0;

                        // Decision-order fallback (#8476): the bucket
                        // queue's approximate activity order wins on the
                        // typical short query but hurts the rare long one.
                        // Every restart taken while the bucket path is live
                        // feeds the shared hardness signal; a query that
                        // keeps restarting graduates to exact heap
                        // selection (`bucket_queue_on_restart`).
                        self.bucket_queue_on_restart();

                        assumption_idx = assumption_idx.min(self.decision_level as usize);
                        continue;
                    }
                } else if self.should_restart() {
                    // Non-IC3 (BMC) regime: the solver's Glucose-style
                    // LBD-EMA policy decides when to fire; restart back to
                    // the assumption prefix.
                    self.stats.record_pending_restart_attribution();
                    if num_assumptions == 0 {
                        // No assumption prefix to preserve: full restart.
                        if self.decision_level > 0 {
                            self.backtrack(0);
                            self.cold.restarts += 1;
                            self.bucket_queue_on_restart();
                        }
                        // Consume the restart signal even when there was
                        // nothing to undo — `should_restart()` stays armed
                        // until this resets (see `do_partial_restart`).
                        self.conflicts_since_restart = 0;
                        self.cold.luby_idx += 1;
                        let _ = self.complete_branch_heuristic_epoch_if_needed();
                    } else {
                        self.do_partial_restart(num_assumptions as u32);
                    }
                    continue;
                }

                // Free decision by the activity heuristic with saved phases
                // (domain-restricted when a domain is active).
                if let Some(var) = self.pick_next_decision_variable() {
                    let lit = self.pick_phase(var);
                    self.decide(lit);

                    // SAT-leaning runs can make many decisions between
                    // conflicts; keep the external interrupt honored on
                    // this branch too.
                    if self.is_interrupted() {
                        return self
                            .declare_assume_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                } else {
                    // No unassigned decision variable remains (within the
                    // domain, when one is active): the query is SAT.
                    if self.active_domain.is_some() {
                        // Domain-restricted SAT (#8649): non-domain variables
                        // are don't-cares, so the reconstruction-based
                        // finalizer does not apply; the authoritative gate is
                        // the partial-assignment check against the FULL
                        // clause set — domain BCP must not have left any
                        // clause falsified outright.
                        if !self.verify_domain_restricted_model() {
                            return self.declare_assume_unknown_with_reason(
                                SatUnknownReason::InvalidSatModel,
                            );
                        }
                        return AssumeResult::Sat(self.get_model());
                    }
                    return self.declare_assume_sat_from_current_assignment();
                }
            }
        }
    }

    /// Number of distinct decision levels among a clause's literals — the
    /// clause's "glue" (Audemard & Simon, "Predicting Learnt Clauses Quality
    /// in Modern SAT Solvers", IJCAI 2009). Read-only; feeds the
    /// Glucose-style LBD-EMA restart policy on the non-IC3 route.
    fn clause_lbd_from_levels(&self, clause: &[Literal]) -> u32 {
        let mut levels: Vec<u32> = clause
            .iter()
            .map(|lit| self.var_data[lit.variable().index()].level)
            .filter(|&level| level > 0)
            .collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len() as u32
    }

    /// Handle empty formula in IC3 path (same logic as assumptions.rs but
    /// without constraint handling — IC3 doesn't use constraints).
    fn ic3_handle_empty_formula(&mut self, assumptions: &[Literal]) -> AssumeResult {
        let mut model = self.get_model();
        let mut first_lit_for_var: Vec<Option<Literal>> = vec![None; self.num_vars];

        for &lit in assumptions {
            let vi = lit.variable().index();
            if vi >= self.num_vars {
                continue;
            }
            let desired = lit.is_positive();
            if let Some(prev) = first_lit_for_var[vi] {
                if prev.is_positive() != desired {
                    return AssumeResult::Unsat(vec![prev, lit], None);
                }
            } else {
                first_lit_for_var[vi] = Some(lit);
                model[vi] = desired;
                ay_prefetch::val_set(&mut self.vals, lit.index(), 1);
                ay_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
            }
        }

        self.declare_assume_sat_from_model(model)
    }
}
