// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing: lucky phases, local search, warmup, model verification.

use super::*;

const STARTUP_WALK_MAX_ACTIVE_CLAUSES: usize = 5_000_000;
const STARTUP_WALK_DEFAULT_MAX_ACTIVE_VARS: usize = 100_000;
const STARTUP_WALK_DENSE_MAX_ACTIVE_VARS: usize = 200_000;
const STARTUP_WALK_DENSE_MIN_ACTIVE_CLAUSES: usize = 2_000_000;
const STARTUP_WALK_DENSE_MIN_CLAUSES_PER_VAR: usize = 16;

/// Small-formula lucky gate (#8448): formulas below BOTH bounds keep the
/// legacy unbudgeted lucky attempt AFTER preprocessing (solve/mod.rs).
/// Formulas at or above either bound get the budgeted EARLY lucky attempt at
/// preprocessing entry instead (kissat runs lucky on every size; the measured
/// gap was main-track 00fd8ac9: 23.4M vars / 63M clauses, solved by kissat's
/// forward-false lucky probe with zero search).
pub(super) const LUCKY_SMALL_MAX_ACTIVE_VARS: usize = 50_000;
pub(super) const LUCKY_SMALL_MAX_ACTIVE_CLAUSES: usize = 500_000;

/// AY_AB_LUCKY kill switch semantics: default ON; only the explicit value
/// "0" disables the early lucky phase. (Pure-upside completeness with the
/// model-gate backstop: a lucky SAT is only declared after the full clause-DB
/// verification plus `finalize_sat_model` / `verify_external_model`.)
fn early_lucky_enabled_from(val: Option<&str>) -> bool {
    !matches!(val, Some("0"))
}

fn early_lucky_enabled() -> bool {
    // B26: CLI-owned opt-out (--sat-no-lucky); env retired.
    early_lucky_enabled_from(ay_core::sat_ab_switches().no_lucky.then_some("0"))
}

/// Per-probe wall budget for the early lucky phase: ~1s per million clauses,
/// clamped to [1s, 60s]. A SUCCESSFUL directional sweep costs one full BCP
/// pass over the clause database (it assigns every variable once), so the
/// budget must scale with formula size — a flat small budget would abort the
/// winning forward-false probe on 63M-clause instances. Unlucky probes almost
/// always die much earlier via conflicts (both polarities of some variable
/// fail); the budget only caps the rare deep-failure tail.
fn lucky_probe_budget_for(active_clauses: usize) -> std::time::Duration {
    std::time::Duration::from_millis(((active_clauses as u64) / 1_000).clamp(1_000, 60_000))
}

/// Result of a complete lucky strategy attempt.
///
/// Mirrors CaDiCaL's lucky phase return codes: 10 (SAT), 20 (UNSAT), 0 (not lucky).
enum LuckyResult {
    Sat,
    Unsat,
    NotLucky,
}

/// Result of a lucky propagation discrepancy attempt.
///
/// Mirrors CaDiCaL's `lucky_propagate_discrepency` control flow:
/// - `Continue`: no conflict, variable was handled (may be assigned by propagation,
///   so caller should re-check the same variable via goto-START pattern)
/// - `Failed`: conflict could not be recovered — abort this lucky strategy
/// - `Unsat`: level-1 conflict analysis derived empty clause — formula is UNSAT
enum LuckyDiscrepancy {
    Continue,
    Failed,
    Unsat,
}

/// First SAT-model contract violation found during verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ModelViolation {
    /// A non-deleted clause in the live clause database is unsatisfied.
    ClauseDb {
        clause_index: usize,
        clause_dimacs: Vec<i32>,
    },
}

pub(super) fn startup_walk_allowed_by_size(active_vars: usize, active_clauses: usize) -> bool {
    if active_clauses > STARTUP_WALK_MAX_ACTIVE_CLAUSES {
        return false;
    }
    if active_vars <= STARTUP_WALK_DEFAULT_MAX_ACTIVE_VARS {
        return true;
    }
    if active_vars > STARTUP_WALK_DENSE_MAX_ACTIVE_VARS {
        return false;
    }
    if active_clauses < STARTUP_WALK_DENSE_MIN_ACTIVE_CLAUSES {
        return false;
    }
    active_clauses >= active_vars.saturating_mul(STARTUP_WALK_DENSE_MIN_CLAUSES_PER_VAR)
}

impl Solver {
    // ==========================================================================
    // Lucky Phase (CaDiCaL-style pre-solving)
    // ==========================================================================

    /// Early lucky phase at preprocessing entry (kissat lucky.c).
    ///
    /// Runs kissat's exact probe set (constant all-true / all-false, then
    /// forward/backward polarity sweeps with full propagation) BEFORE any
    /// preprocessing pass, on formulas too large for the legacy
    /// post-preprocess lucky gate.
    ///
    /// The probes run on a SCRATCH propagation engine (`lucky_scratch.rs`)
    /// that reads the clause arena immutably: a FAILED probe cannot corrupt
    /// or even perturb solver state (no watch-list moves, no clause literal
    /// swaps, no phases, no VSIDS/VMTF changes, no learned clauses). This is
    /// load-bearing: an earlier in-solver prototype that probed via
    /// `decide()` + `search_propagate()` left BCP watch/literal-order
    /// perturbations behind after an 81ms failed probe, which sent e3bd4a39
    /// (191K vars / 13M clauses) from 9.7K conflicts (0.7s) to 185K conflicts
    /// (35s) of subsequent search.
    ///
    /// Each probe is bounded by a size-proportional wall budget, and a lucky
    /// model is verified three times before SAT is declared: by the scratch
    /// engine itself, by `finalize_sat_model`, and by `verify_external_model`
    /// (the model gate) — a buggy probe can waste time, never emit a wrong
    /// verdict.
    ///
    /// Returns `Some(result)` when lucky settles the instance, `None` to
    /// continue with normal preprocessing + CDCL.
    ///
    /// Kill switch: AY_AB_LUCKY=0 (default ON).
    pub(super) fn try_lucky_phases_at_preprocess_entry(&mut self) -> Option<SatResult> {
        if !early_lucky_enabled() {
            return None;
        }
        // IC3/PDR drives the solver through assumption queries with forced
        // phases; lucky is a plain-CNF startup heuristic only.
        if self.cold.ic3_mode {
            return None;
        }
        let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars());
        let active_cls = self.arena.active_clause_count();
        // Small formulas keep the legacy (unbudgeted) post-preprocess lucky
        // attempt — running lucky twice would double the startup cost for no
        // extra completeness.
        if active_vars < LUCKY_SMALL_MAX_ACTIVE_VARS && active_cls < LUCKY_SMALL_MAX_ACTIVE_CLAUSES
        {
            return None;
        }

        let budget = lucky_probe_budget_for(active_cls);
        // #lucky-total-cap: 4s across ALL probes. Measured: every successful
        // lucky solve costs <=1.6s (63M-clause 00fd8ac9: 1.4-1.5s); the
        // uncapped failure case cost 43.8s on a 22M-clause giant and flipped
        // three near-budget solves to timeouts.
        const LUCKY_TOTAL_BUDGET: std::time::Duration = std::time::Duration::from_secs(4);
        let t0 = ay_core::time::Instant::now();
        let model = self.lucky_scratch_probe(budget, LUCKY_TOTAL_BUDGET);
        let elapsed = t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        self.stats.lucky_time_ns = self.stats.lucky_time_ns.saturating_add(elapsed);

        model.map(|model| {
            self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
            // Model gate: finalize_sat_model + verify_external_model. On
            // failure this downgrades to Unknown rather than declaring SAT.
            self.declare_sat_from_model(model)
        })
    }

    /// Try lucky assignment strategies before full CDCL search
    ///
    /// Attempts several simple assignment patterns that can quickly solve
    /// "easy" formulas without full CDCL search. Returns Some(true) for SAT,
    /// Some(false) for UNSAT proven at level 0, None to continue to CDCL.
    ///
    /// CaDiCaL reference: lucky.cpp:439-504
    pub(super) fn try_lucky_phases(&mut self) -> Option<bool> {
        if self.is_interrupted() {
            return None;
        }
        // CaDiCaL lucky.cpp:440: must be at root level
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: try_lucky_phases called at decision level {} (expected 0)",
            self.decision_level,
        );
        // #8477: Verify BCP is fully drained before lucky phases begin.
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: try_lucky_phases entry: qhead ({}) != trail.len() ({}) — \
             pending propagations from preprocessing",
            self.qhead,
            self.trail.len(),
        );

        // CaDiCaL: lucky phase decisions are artificial — suppress phase saving
        // in enqueue() to avoid corrupting the phase heuristic.
        self.suppress_phase_saving = true;

        // Monotone strategies: if every clause has at least one positive literal,
        // set all variables true. Symmetric for negative.
        // Reference: Kissat lucky.c:11-80 (no_all_negative_clauses / no_all_positive_clauses)
        //            Kissat lucky.c:323-362 (invocation in kissat_lucky)
        if !self.is_interrupted() {
            match self.lucky_positive_monotone() {
                LuckyResult::Sat if self.lucky_verify_clause_db().is_none() => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Sat => self.lucky_reset(),
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => {
                    self.lucky_reset();
                    if self.has_empty_clause {
                        self.suppress_phase_saving = false;
                        return Some(false);
                    }
                }
            }
        }

        if !self.is_interrupted() {
            match self.lucky_negative_monotone() {
                LuckyResult::Sat if self.lucky_verify_clause_db().is_none() => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Sat => self.lucky_reset(),
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => {
                    self.lucky_reset();
                    if self.has_empty_clause {
                        self.suppress_phase_saving = false;
                        return Some(false);
                    }
                }
            }
        }

        // Directional strategies: forward/backward x positive/negative.
        // Uses level-1 conflict analysis and goto-START re-check.
        // Reference: CaDiCaL lucky.cpp:129-265
        for &(positive, forward) in &[(false, true), (true, true), (false, false), (true, false)] {
            if self.is_interrupted() {
                self.suppress_phase_saving = false;
                return None;
            }
            match self.lucky_directional(positive, forward) {
                LuckyResult::Sat if self.lucky_verify_clause_db().is_none() => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Sat => self.lucky_reset(),
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => {
                    self.lucky_reset();
                    if self.has_empty_clause {
                        self.suppress_phase_saving = false;
                        return Some(false);
                    }
                }
            }
        }

        // Horn strategies: satisfy clauses via first positive/negative literal.
        // Reference: CaDiCaL lucky.cpp:275-435
        for &prefer_positive in &[true, false] {
            if self.is_interrupted() {
                self.suppress_phase_saving = false;
                return None;
            }
            match self.lucky_horn(prefer_positive) {
                LuckyResult::Sat if self.lucky_verify_clause_db().is_none() => {
                    self.suppress_phase_saving = false;
                    return Some(true);
                }
                LuckyResult::Sat => self.lucky_reset(),
                LuckyResult::Unsat => {
                    self.suppress_phase_saving = false;
                    return Some(false);
                }
                LuckyResult::NotLucky => {
                    self.lucky_reset();
                    if self.has_empty_clause {
                        self.suppress_phase_saving = false;
                        return Some(false);
                    }
                }
            }
        }

        self.suppress_phase_saving = false;

        // Propagate any units learned during lucky phases.
        // Capture conflict_ref for LRAT resolution chain (#4397).
        if self.decision_level == 0 {
            if self.is_interrupted() {
                return None;
            }
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return Some(false);
            }
        }

        None // No lucky assignment found
    }

    /// Reset solver state after a failed lucky attempt.
    ///
    /// After backtracking to level 0, exhausts pending BCP propagations.
    /// With chronological backtracking, `backtrack(0)` may compact
    /// out-of-order literals into the trail and set `qhead` below
    /// `trail.len()`. If not propagated, subsequent `decide()` calls
    /// hit the `qhead == trail.len()` precondition, silently skipping
    /// unit implications in release mode and causing false UNSAT (#8477).
    pub(super) fn lucky_reset(&mut self) {
        if self.decision_level > 0 {
            // NOTE: intentionally the PHASE-SAVING backtrack, unlike kissat's
            // backtrack_without_updating_phases. A failed lucky sweep leaves
            // phases pointing toward a nearly-satisfying assignment, which
            // measurably helps subsequent search on small instances (A/B on
            // 9b998be0: 6.3s with phase saving vs 19.8s phase-neutral).
            self.backtrack(0);
        }
        // Exhaust any pending propagations left by chrono-BT compaction.
        // Without this, qhead < trail.len() and the next decide() call
        // proceeds with un-propagated literals (#8477).
        if self.qhead < self.trail.len() {
            if let Some(conflict_ref) = self.search_propagate() {
                // Level-0 conflict during reset means formula is UNSAT.
                // Set the empty clause flag so the caller detects it.
                self.record_level0_conflict_chain(conflict_ref);
                self.has_empty_clause = true;
            }
        }
    }

    /// CaDiCaL-style discrepancy propagation for lucky phases.
    ///
    /// Decides `dec`, propagates. On conflict:
    /// - At level > 1: backtrack one level, try opposite polarity.
    ///   If that also conflicts, give up.
    /// - At level == 1: run full 1UIP conflict analysis to learn a unit clause,
    ///   backtrack to level 0, enqueue the unit, and re-propagate. If that
    ///   also conflicts, the formula is UNSAT.
    ///
    /// Returns `Continue` if no conflict (caller should re-check variable),
    /// `Failed` if unrecoverable, `Unsat` if empty clause derived.
    ///
    /// Reference: CaDiCaL lucky.cpp:129-153 (lucky_propagate_discrepency)
    fn lucky_propagate_discrepancy(&mut self, dec: Literal) -> LuckyDiscrepancy {
        if self.is_interrupted() {
            return LuckyDiscrepancy::Failed;
        }
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: lucky_propagate_discrepancy entry: qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        self.decide(dec);
        let conflict = self.search_propagate();
        if self.is_interrupted() {
            return LuckyDiscrepancy::Failed;
        }

        if let Some(conflict_ref) = conflict {
            if self.decision_level > 1 {
                // Level > 1: backtrack and try opposite polarity.
                // Must exhaust pending BCP after backtrack before deciding,
                // because chrono-BT compaction may leave qhead < trail.len() (#8477).
                self.backtrack(self.decision_level - 1);
                if self.qhead < self.trail.len() && self.search_propagate().is_some() {
                    return LuckyDiscrepancy::Failed;
                }
                self.decide(dec.negated());
                if self.search_propagate().is_some() {
                    return LuckyDiscrepancy::Failed;
                }
                if self.is_interrupted() {
                    return LuckyDiscrepancy::Failed;
                }
                return LuckyDiscrepancy::Continue;
            }

            // Level == 1: full 1UIP conflict analysis -> learns unit, backtracks to 0
            let Some(result) = self.analyze_conflict(conflict_ref) else {
                self.backtrack(0);
                return LuckyDiscrepancy::Failed;
            };
            let uip = result.learned_clause[0];
            debug_assert_eq!(
                result.backtrack_level, 0,
                "Level-1 conflict must backtrack to 0"
            );
            self.backtrack(0);
            // CaDiCaL lucky.cpp:144
            debug_assert_eq!(
                self.decision_level, 0,
                "BUG: not at level 0 after lucky analysis"
            );

            // OTFS Branch B: use existing strengthened clause as driving clause.
            if let Some(driving_ref) = result.otfs_driving_clause {
                self.enqueue(uip, Some(driving_ref));
                self.conflict.return_learned_buf(result.learned_clause);
                self.conflict.return_chain_buf(result.resolution_chain);
            } else {
                // Add the learned unit clause.
                // Use add_learned_clause for ALL sizes so the clause is in the DB
                // with a valid ClauseRef. This ensures record_level0_conflict_chain
                // can find its ID via the reason when building LRAT hints (#4397).
                // Set DiagnosticPass::Learning so diagnostic trace classifies this
                // as a learned clause, not a theory lemma (#4172).
                self.set_diagnostic_pass(DiagnosticPass::Learning);
                let learned_ref = self.add_conflict_learned_clause(
                    result.learned_clause,
                    result.lbd,
                    result.resolution_chain,
                );
                self.clear_diagnostic_pass();
                self.enqueue(uip, Some(learned_ref));
            }

            // Re-propagate the learned unit.
            // Capture conflict_ref for LRAT resolution chain (#4397).
            if let Some(conflict_ref) = self.search_propagate() {
                // Second conflict at level 0 -> UNSAT
                self.record_level0_conflict_chain(conflict_ref);
                return LuckyDiscrepancy::Unsat;
            }
            if self.is_interrupted() {
                return LuckyDiscrepancy::Failed;
            }

            // Learned unit simplified the formula; continue lucky phase
            return LuckyDiscrepancy::Continue;
        }

        // No conflict
        LuckyDiscrepancy::Continue
    }

    /// Positive monotone: if every clause contains at least one positive literal,
    /// the formula is trivially SAT -- set all variables to true.
    ///
    /// A clause with all negative literals cannot be satisfied by setting all
    /// variables true, so we check that no such clause exists. If the check
    /// passes, we assign all unassigned variables to true with no conflicts.
    ///
    /// Reference: Kissat lucky.c:11-45 (no_all_negative_clauses)
    ///            Kissat lucky.c:323-341 (set all variables true)
    fn lucky_positive_monotone(&mut self) -> LuckyResult {
        debug_assert_eq!(self.decision_level, 0);

        // Check: every clause has at least one positive literal that is not
        // assigned false. Kissat lucky.c:20-22: !NEGATED(lit) && VALUE(lit) >= 0
        // No collect needed: the loop body is read-only on the arena.
        for idx in self.arena.indices() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            let has_non_false_positive = lits
                .iter()
                .any(|lit| lit.is_positive() && self.lit_value(*lit) != Some(false));
            if !has_non_false_positive {
                return LuckyResult::NotLucky;
            }
        }

        // All clauses have at least one positive literal -- set all vars true.
        for var_idx in 0..self.num_vars {
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            let lit = Literal::positive(Variable(var_idx as u32));
            self.decide(lit);
            // The propagation must run in EVERY build: it is what advances
            // `qhead` to the trail end, and post-SAT consumers (`minimize_model`,
            // `flip_to_none`) gate on that quiescence. This call sat INSIDE the
            // debug_assert! until 2026-08, so release builds skipped it entirely
            // and every lucky-solved SAT left qhead parked at the root prefix —
            // release-only, caught by the flip_to_none tests the first time the
            // suite ran under --release.
            let _conflict = self.search_propagate();
            debug_assert!(
                _conflict.is_none(),
                "BUG: conflict in positive monotone lucky phase"
            );
        }
        LuckyResult::Sat
    }

    /// Negative monotone: if every clause contains at least one negative literal,
    /// the formula is trivially SAT -- set all variables to false.
    ///
    /// Symmetric to positive monotone. A clause with all positive literals cannot
    /// be satisfied by setting all variables false, so we check that no such
    /// clause exists.
    ///
    /// Reference: Kissat lucky.c:47-80 (no_all_positive_clauses)
    ///            Kissat lucky.c:343-362 (set all variables false)
    fn lucky_negative_monotone(&mut self) -> LuckyResult {
        debug_assert_eq!(self.decision_level, 0);

        // Check: every clause has at least one negative literal that is not
        // assigned false. Kissat lucky.c:56-58: NEGATED(lit) && VALUE(lit) >= 0
        // No collect needed: the loop body is read-only on the arena.
        for idx in self.arena.indices() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            let has_non_false_negative = lits
                .iter()
                .any(|lit| !lit.is_positive() && self.lit_value(*lit) != Some(false));
            if !has_non_false_negative {
                return LuckyResult::NotLucky;
            }
        }

        // All clauses have at least one negative literal -- set all vars false.
        for var_idx in 0..self.num_vars {
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            let lit = Literal::negative(Variable(var_idx as u32));
            self.decide(lit);
            // Same hoisting as the positive twin above: the propagation is
            // load-bearing (qhead quiescence), never assert-only.
            let _conflict = self.search_propagate();
            debug_assert!(
                _conflict.is_none(),
                "BUG: conflict in negative monotone lucky phase"
            );
        }
        LuckyResult::Sat
    }

    /// Try assigning all variables with given polarity and direction.
    ///
    /// Uses CaDiCaL goto-START re-check pattern: after discrepancy handling,
    /// the variable may have been assigned by propagation, so re-check it.
    ///
    /// Reference: CaDiCaL lucky.cpp:155-265
    fn lucky_directional(&mut self, positive: bool, forward: bool) -> LuckyResult {
        // CaDiCaL lucky.cpp:157-158: must not be UNSAT, must be at root level
        debug_assert!(
            !self.has_empty_clause,
            "BUG: lucky_directional called with has_empty_clause=true",
        );
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: lucky_directional not at root level (level={})",
            self.decision_level,
        );
        let make_lit = if positive {
            Literal::positive
        } else {
            Literal::negative
        };

        if forward {
            let mut var_idx = 0;
            while var_idx < self.num_vars {
                if self.is_interrupted() {
                    return LuckyResult::NotLucky;
                }
                if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                    var_idx += 1;
                    continue;
                }
                match self.lucky_propagate_discrepancy(make_lit(Variable(var_idx as u32))) {
                    LuckyDiscrepancy::Continue => continue, // re-check same variable
                    LuckyDiscrepancy::Failed => return LuckyResult::NotLucky,
                    LuckyDiscrepancy::Unsat => return LuckyResult::Unsat,
                }
            }
        } else {
            let mut var_idx = self.num_vars;
            while var_idx > 0 {
                if self.is_interrupted() {
                    return LuckyResult::NotLucky;
                }
                var_idx -= 1;
                if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                    continue;
                }
                match self.lucky_propagate_discrepancy(make_lit(Variable(var_idx as u32))) {
                    LuckyDiscrepancy::Continue => {
                        var_idx += 1; // counteract decrement to re-check same variable
                        continue;
                    }
                    LuckyDiscrepancy::Failed => return LuckyResult::NotLucky,
                    LuckyDiscrepancy::Unsat => return LuckyResult::Unsat,
                }
            }
        }
        LuckyResult::Sat
    }

    /// Try horn strategy: satisfy each clause via first literal of preferred polarity.
    ///
    /// Horn strategies don't use discrepancy -- they abort on conflict.
    /// Remaining unassigned variables get the opposite polarity as default.
    ///
    /// Reference: CaDiCaL lucky.cpp:275-435
    fn lucky_horn(&mut self, prefer_positive: bool) -> LuckyResult {
        // CaDiCaL lucky.cpp:277/375: must be at root level
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: lucky_horn not at root level (level={})",
            self.decision_level,
        );
        // Reuse persistent buffer to avoid arena-proportional allocation (#8599).
        let mut buf = std::mem::take(&mut self.cold.reduce_indices_buf);
        buf.clear();
        buf.extend(self.arena.indices());
        let result = 'horn: {
            for &off in &buf {
                if self.is_interrupted() {
                    break 'horn LuckyResult::NotLucky;
                }
                if self.arena.is_empty_clause(off) {
                    continue;
                }
                let len = self.arena.len_of(off);

                let mut satisfied = false;
                let mut first_match: Option<Literal> = None;

                for j in 0..len {
                    let lit = self.arena.literal(off, j);
                    match self.lit_value(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => continue,
                        None => {
                            if (lit.is_positive() == prefer_positive) && first_match.is_none() {
                                first_match = Some(lit);
                            }
                        }
                    }
                }

                if satisfied {
                    continue;
                }

                match first_match {
                    Some(lit) if !self.var_lifecycle.is_removed(lit.variable().index()) => {
                        self.decide(lit);
                        if self.search_propagate().is_some() {
                            break 'horn LuckyResult::NotLucky;
                        }
                    }
                    Some(_) => continue,
                    None => break 'horn LuckyResult::NotLucky,
                }
            }
            // Fall through: all clauses processed without conflict.
            LuckyResult::Sat // placeholder; overridden below
        };
        self.cold.reduce_indices_buf = buf;
        if !matches!(result, LuckyResult::Sat) {
            return result;
        }

        // Assign remaining variables with opposite polarity
        let default_lit = if prefer_positive {
            Literal::negative
        } else {
            Literal::positive
        };
        for var_idx in 0..self.num_vars {
            if !self.var_is_assigned(var_idx) && !self.var_lifecycle.is_removed(var_idx) {
                self.decide(default_lit(Variable(var_idx as u32)));
                if self.search_propagate().is_some() {
                    return LuckyResult::NotLucky;
                }
            }
        }
        LuckyResult::Sat
    }

    /// Verify that the current internal assignment satisfies all active
    /// clause-DB clauses. Returns `None` if all satisfied, or
    /// `Some((idx, dimacs_lits))` for the first unsatisfied clause.
    ///
    /// Lucky phases rely on BCP to detect conflicts during assignment.
    /// After BVE preprocessing, the 2WL watch state can have subtle
    /// inconsistencies that cause BCP to miss clauses (#8482). This
    /// verification catches those misses before returning a bogus SAT.
    ///
    /// CaDiCaL has the same check as `assert(satisfied())` in lucky.cpp
    /// (lines 177, 204, 234, 262, 316, 364) but only in debug builds.
    /// AY runs it always because the cost is negligible compared to the
    /// O(vars * propagations) cost of the lucky phase itself.
    fn lucky_verify_clause_db(&self) -> Option<(usize, Vec<i32>)> {
        for idx in self.arena.active_indices() {
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            let satisfied = lits.iter().any(|&lit| self.lit_value(lit) == Some(true));
            if !satisfied {
                let all_false = lits.iter().all(|&lit| self.lit_value(lit) == Some(false));
                if all_false {
                    let dimacs: Vec<i32> = lits.iter().map(|l| l.to_dimacs()).collect();
                    return Some((idx, dimacs));
                }
            }
        }
        None
    }

    /// Returns true if walk found a satisfying assignment (SAT), false otherwise.
    pub(super) fn try_walk(&mut self) -> bool {
        if !self.phase_init.walk_enabled || !self.phase_init.startup_walk_enabled {
            return false;
        }

        // Skip startup walk on very large formulas (>5M active clauses). Walk
        // initialization builds occurrence lists by iterating all clauses
        // twice (count + build), costing O(clauses) before any walk steps.
        // CaDiCaL does NOT run walk at startup -- only during periodic
        // rephasing where tick-proportional budgets limit overhead.
        //
        // Raised from 1M to 5M: large industrial formulas (shuffling-2 at
        // 4.7M clauses) benefit significantly from walk-based phase init
        // over JW alone. Walk phases give CDCL a better starting trajectory,
        // reducing conflict count. The O(clauses) setup cost (~1.5s for 4.5M
        // clauses) is worthwhile when the alternative is 40K+ conflicts.
        //
        // (#8448, #8361) The default active-var cap protects formulas such as
        // ecarev-110 (127K vars, 722K clauses), where startup walk spends
        // seconds building and scanning occurrence lists before CDCL gets a
        // turn. Clause-dense random SAT families are different: shuffling-2
        // has ~139K vars but 4.7M mostly binary clauses, and #8361 showed
        // that local-search phase seeding can cut tens of thousands of CDCL
        // conflicts. Keep a narrow density exception for that class while
        // preserving the hard 5M-clause setup cap.
        let active_clauses = self.arena.active_clause_count();
        let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars());
        if !startup_walk_allowed_by_size(active_vars, active_clauses) {
            return false;
        }

        // Use a seed based on problem characteristics for reproducibility
        let seed = (self.num_vars as u64)
            .wrapping_mul(31)
            .wrapping_add(self.num_original_clauses as u64);

        // Run walk to find good phases (written to self.phase only).
        // During preprocessing, no learned clauses exist yet, so
        // irredundant_only is the correct filter.
        crate::walk::walk(
            &self.arena,
            self.num_vars,
            &mut self.phase,
            &mut self.phase_init.walk_prev_phase,
            &mut self.phase_init.walk_stats,
            seed,
            self.phase_init.walk_limit,
            crate::walk::WalkFilter::irredundant_only(),
        )
    }

    /// Run warmup-based phase initialization.
    ///
    /// Uses CDCL propagation (ignoring conflicts) to find good initial phases.
    /// This is more efficient than walk for small/medium instances because
    /// it uses O(1) amortized 2-watched literal propagation instead of O(n^2)
    /// break-value computation.
    pub(super) fn try_warmup(&mut self) {
        if !self.phase_init.warmup_enabled || !self.phase_init.startup_warmup_enabled {
            return;
        }

        // Skip warmup for very small formulas
        if self.num_vars < 20 || self.num_original_clauses < 50 {
            return;
        }

        // Skip warmup on very large formulas (>5M active clauses). Warmup
        // builds its own 2WL watch structure by iterating all clauses,
        // then runs propagation over all variables. Raised from 1M to 5M
        // to match the walk threshold -- large industrial formulas benefit
        // from warmup-derived target phases for stable mode search.
        if self.arena.active_clause_count() > 5_000_000 {
            return;
        }

        // (#8448) Skip warmup on formulas with many active variables.
        // Warmup builds a shadow 2WL watch structure (O(clauses)) and then
        // propagates over all unfixed variables (O(vars * avg_watched)).
        // On ecarev-110 (127K vars, 722K clauses), this takes several seconds.
        // JW phase init is O(total_literals) and sufficient for large formulas.
        // Warmup keeps the plain 100K active-var guard. Unlike walk, it does
        // not have a shuffling-style density exception because it performs a
        // full shadow 2WL build plus propagation over all variables.
        {
            let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars());
            if active_vars > STARTUP_WALK_DEFAULT_MAX_ACTIVE_VARS {
                return;
            }
        }

        crate::warmup::warmup(
            &self.arena,
            self.num_vars,
            &self.phase,
            &mut self.target_phase,
            &mut self.phase_init.warmup_stats,
        );
    }

    /// Jeroslow-Wang initial phase selection.
    ///
    /// For each variable without a saved phase, computes JW scores for both
    /// polarities and sets the initial phase to the polarity with higher score.
    /// JW(l) = sum_{clause c containing l} 2^{-|c|}. This weights short clauses
    /// more heavily, since satisfying a short clause is more constrained.
    ///
    /// Cost: O(total_literals) -- single pass over all active clauses.
    /// On shuffling-2 (4.5M clauses), this takes ~10-20ms.
    ///
    /// Reference: Jeroslow & Wang (1990), "Solving Propositional Satisfiability
    /// Problems". CaDiCaL phases.cpp initial_phase=2 (JW-based).
    pub(super) fn init_jw_phases(&mut self) {
        // Only fill in phases that are still unset (don't override walk/warmup).
        let mut has_unset = false;
        for i in 0..self.num_vars {
            if self.phase[i] == 0 {
                has_unset = true;
                break;
            }
        }
        if !has_unset {
            return;
        }

        // Compute JW scores: pos_score[v] and neg_score[v].
        let mut pos_score = vec![0.0f64; self.num_vars];
        let mut neg_score = vec![0.0f64; self.num_vars];

        for idx in self.arena.indices() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let lits = self.arena.literals(idx);
            let len = lits.len();
            if len == 0 {
                continue;
            }
            // 2^{-len}: for len=2 -> 0.25, len=3 -> 0.125, len=10 -> ~0.001
            let weight = (0.5f64).powi(len as i32);
            for &lit in lits {
                let var = lit.variable().index();
                if var < self.num_vars {
                    if lit.is_positive() {
                        pos_score[var] += weight;
                    } else {
                        neg_score[var] += weight;
                    }
                }
            }
        }

        // Set phase for variables that don't have one yet.
        for i in 0..self.num_vars {
            if self.phase[i] == 0 {
                // Choose polarity with higher JW score.
                self.phase[i] = if pos_score[i] >= neg_score[i] { 1 } else { -1 };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add(solver: &mut Solver, clause: &[i32]) {
        let lits: Vec<Literal> = clause.iter().map(|&d| Literal::from_dimacs(d)).collect();
        assert!(solver.add_clause(lits), "clause {clause:?} rejected");
    }

    /// Set up watches + level-0 propagation so lucky strategies can be
    /// exercised directly (the slice of init_solve they depend on).
    fn prepare(solver: &mut Solver) {
        solver.initialize_watches();
        assert!(
            solver.search_propagate().is_none(),
            "unexpected level-0 conflict in test setup"
        );
    }

    #[test]
    fn lucky_positive_monotone_solves_all_true_cnf() {
        // Every clause has a positive literal => all-true satisfies.
        let mut solver = Solver::new(3);
        add(&mut solver, &[1, 2]);
        add(&mut solver, &[2, 3]);
        add(&mut solver, &[-1, 3]);
        prepare(&mut solver);
        assert!(matches!(solver.lucky_positive_monotone(), LuckyResult::Sat));
        assert!(solver.lucky_verify_clause_db().is_none());
        // End-to-end: the same CNF must come back SAT through solve().
        let mut fresh = Solver::new(3);
        add(&mut fresh, &[1, 2]);
        add(&mut fresh, &[2, 3]);
        add(&mut fresh, &[-1, 3]);
        assert!(matches!(fresh.solve().into_inner(), SatResult::Sat(_)));
    }

    #[test]
    fn lucky_negative_monotone_solves_all_false_cnf() {
        // Every clause has a negative literal => all-false satisfies.
        let mut solver = Solver::new(3);
        add(&mut solver, &[-1, -2]);
        add(&mut solver, &[-2, -3]);
        add(&mut solver, &[1, -3]);
        prepare(&mut solver);
        assert!(matches!(solver.lucky_negative_monotone(), LuckyResult::Sat));
        assert!(solver.lucky_verify_clause_db().is_none());
        let mut fresh = Solver::new(3);
        add(&mut fresh, &[-1, -2]);
        add(&mut fresh, &[-2, -3]);
        add(&mut fresh, &[1, -3]);
        assert!(matches!(fresh.solve().into_inner(), SatResult::Sat(_)));
    }

    #[test]
    fn lucky_forward_false_solves_via_propagation() {
        // (1 v 2) blocks negative-monotone, (-1 v -2) blocks positive-monotone,
        // but the forward-false sweep succeeds: deciding -1 propagates 2 via
        // (1 v 2), and (-1 v -2) is satisfied by -1.
        let mut solver = Solver::new(2);
        add(&mut solver, &[1, 2]);
        add(&mut solver, &[-1, -2]);
        prepare(&mut solver);
        assert!(matches!(
            solver.lucky_positive_monotone(),
            LuckyResult::NotLucky
        ));
        solver.lucky_reset();
        assert!(matches!(
            solver.lucky_negative_monotone(),
            LuckyResult::NotLucky
        ));
        solver.lucky_reset();
        assert!(matches!(
            solver.lucky_directional(false, true),
            LuckyResult::Sat
        ));
        assert!(solver.lucky_verify_clause_db().is_none());
        // x1=false, x2=true is the propagated model.
        assert_eq!(solver.lit_value(Literal::from_dimacs(-1)), Some(true));
        assert_eq!(solver.lit_value(Literal::from_dimacs(2)), Some(true));
    }

    /// Build a SAT formula on 15 vars that defeats EVERY lucky strategy:
    /// - c1..c4  force var 1 true  (kills forward-false at var 2: both
    ///   polarities conflict at level 2)
    /// - c5..c8  force var 4 false (kills forward-true at var 5)
    /// - c9/c10  all-positive + all-negative 3-clauses (kill both monotone
    ///   checks and both horn variants)
    /// - c11..c14 force var 15 true  (kills backward-false at var 14)
    /// - c15..c18 force var 12 false (kills backward-true at var 11)
    fn all_probes_fail_formula(solver: &mut Solver) {
        add(solver, &[1, 2, 3]);
        add(solver, &[1, 2, -3]);
        add(solver, &[1, -2, 3]);
        add(solver, &[1, -2, -3]);
        add(solver, &[-4, 5, 6]);
        add(solver, &[-4, 5, -6]);
        add(solver, &[-4, -5, 6]);
        add(solver, &[-4, -5, -6]);
        add(solver, &[7, 8, 9]);
        add(solver, &[-7, -8, -9]);
        add(solver, &[15, 14, 13]);
        add(solver, &[15, 14, -13]);
        add(solver, &[15, -14, 13]);
        add(solver, &[15, -14, -13]);
        add(solver, &[-12, 11, 10]);
        add(solver, &[-12, 11, -10]);
        add(solver, &[-12, -11, 10]);
        add(solver, &[-12, -11, -10]);
    }

    #[test]
    fn lucky_all_probes_fail_falls_through_with_identical_verdict() {
        let mut solver = Solver::new(15);
        all_probes_fail_formula(&mut solver);
        prepare(&mut solver);
        assert!(
            solver.try_lucky_phases().is_none(),
            "every lucky probe must fail on the gadget formula"
        );
        assert_eq!(
            solver.decision_level, 0,
            "lucky must restore the solver to level 0 after failing"
        );
        // Fall through to normal search: verdict must be SAT (the formula is
        // satisfiable, e.g. 1=T, 4=F, 15=T, 12=F, 7=T, rest false).
        let mut fresh = Solver::new(15);
        all_probes_fail_formula(&mut fresh);
        assert!(matches!(fresh.solve().into_inner(), SatResult::Sat(_)));
    }

    #[test]
    fn early_lucky_solves_large_all_false_cnf_without_search() {
        // 60K vars (above LUCKY_SMALL_MAX_ACTIVE_VARS) so the budgeted EARLY
        // lucky path fires at preprocessing entry; the chain of all-negative
        // binaries is satisfied by all-false (negative monotone probe).
        let n: usize = 60_000;
        let mut solver = Solver::new(n);
        for i in 1..n as i32 {
            add(&mut solver, &[-i, -(i + 1)]);
        }
        let result = solver.solve().into_inner();
        assert!(matches!(result, SatResult::Sat(_)));
        assert_eq!(solver.num_conflicts, 0, "lucky SAT must need zero search");
        assert!(
            solver.stats.lucky_time_ns > 0,
            "early lucky phase must have run (lucky_time_ns recorded)"
        );
    }

    #[test]
    fn early_lucky_env_kill_switch_semantics() {
        assert!(early_lucky_enabled_from(None), "default must be ON");
        assert!(!early_lucky_enabled_from(Some("0")), "0 must disable");
        assert!(early_lucky_enabled_from(Some("1")));
        assert!(early_lucky_enabled_from(Some("")));
    }

    #[test]
    fn lucky_probe_budget_scales_and_clamps() {
        use std::time::Duration;
        assert_eq!(lucky_probe_budget_for(0), Duration::from_secs(1));
        assert_eq!(lucky_probe_budget_for(500_000), Duration::from_secs(1));
        assert_eq!(lucky_probe_budget_for(5_000_000), Duration::from_secs(5));
        assert_eq!(lucky_probe_budget_for(63_000_000), Duration::from_mins(1));
    }

    #[test]
    fn startup_walk_size_gate_allows_shuffling_but_not_ecarev_shape() {
        assert!(startup_walk_allowed_by_size(100_000, 722_000));
        assert!(!startup_walk_allowed_by_size(100_001, 722_000));

        assert!(startup_walk_allowed_by_size(138_711, 4_700_000));
        assert!(!startup_walk_allowed_by_size(127_000, 722_000));
    }

    #[test]
    fn startup_walk_size_gate_keeps_hard_setup_caps() {
        assert!(!startup_walk_allowed_by_size(200_001, 4_700_000));
        assert!(!startup_walk_allowed_by_size(138_711, 5_000_001));
        assert!(!startup_walk_allowed_by_size(138_711, 2_000_000));
    }
}
