// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lookahead scheduling and CDCL loop integration.
//!
//! Lookahead probing is expensive (O(vars * propagation_depth) per round),
//! so it is only triggered when the solver is in stable mode and making
//! poor progress (high LBD ratio). When triggered, the lookahead result
//! is stored and used to override VSIDS for the next decision.
//!
//! ## References
//!
//! - Heule & van Maaren, "Look-Ahead Based SAT Solvers" (2009)
//! - CaDiCaL `lookahead.cpp` (Biere et al.)

use super::*;

impl Solver {
    /// Check whether a lookahead round should be triggered.
    ///
    /// Conditions:
    /// 1. Must be at decision level 0 (lookahead probes from level 0)
    /// 2. Must be in stable mode (lookahead is expensive, focused mode
    ///    uses frequent restarts instead)
    /// 3. Minimum conflict count reached (EMA needs warmup)
    /// 4. Enough conflicts since last lookahead round (cooldown interval)
    /// 5. Search quality is degraded: fast LBD EMA significantly exceeds
    ///    slow EMA, indicating the solver is "stuck" learning poor clauses
    #[inline]
    pub(in crate::solver) fn should_run_lookahead(&self) -> bool {
        if self.decision_level != 0 {
            return false;
        }
        if !self.stable_mode {
            return false;
        }
        // Skip lookahead on Large formulas (#8448): probing is O(vars) even
        // with budgets, and the wall-clock enforcement has granularity issues
        // on formulas with 100K+ variables where iterating var indices alone
        // costs seconds. On ecarev-110 (127K vars), 4 lookahead rounds
        // consumed ~18s of a 60s run while finding 0 useful failed literals.
        if FormulaClass::classify(self.num_vars, self.num_original_clauses) == FormulaClass::Large {
            return false;
        }
        // (#8448) Skip lookahead on Medium formulas with many active vars.
        // Lookahead cost scales with active_vars: each probe pair does
        // decide + search_propagate + backtrack over the entire 2WL structure.
        // On ecarev-110 (127K vars, Medium class), a single round takes 5-10s
        // despite the 500ms wall limit, because the wall check granularity
        // (every 4 vars) can't compensate when individual probes are slow on
        // very large clause databases (720K clauses). The 500ms limit works
        // well for Medium formulas under 50K vars (e.g., FmlaEquivChain at
        // 51K vars completes round 1 in ~500ms and finds 772 failed literals).
        // For formulas above 50K active vars, the per-probe cost makes even
        // 500ms budget enforcement unreliable.
        {
            let active_vars = self.num_vars.saturating_sub(self.trail.len());
            if active_vars > 50_000 {
                return false;
            }
        }
        // (#8448) For Medium formulas, allow only the first lookahead round.
        // On FmlaEquivChain (51K vars), round 1 finds 772 failed literals
        // (essential for solving), but rounds 2-4 find 0 failed literals
        // and consume ~17s (22s total - 5s round 1). Limiting to 1 round
        // saves the entire unproductive tail. The first round is gated by
        // LOOKAHEAD_MIN_CONFLICTS; subsequent rounds are blocked here.
        if FormulaClass::classify(self.num_vars, self.num_original_clauses) == FormulaClass::Medium
            && self.stats.lookahead_rounds >= 1
        {
            return false;
        }
        if self.num_conflicts < LOOKAHEAD_MIN_CONFLICTS {
            return false;
        }
        // Growing interval: the next_lookahead_conflict threshold increases
        // with each round (2x growth in run_lookahead_round). This avoids
        // repeated expensive lookahead rounds on formulas like FmlaEquivChain
        // where each round costs hundreds of ms even with the propagation budget.
        if self.num_conflicts < self.cold.next_lookahead_conflict {
            return false;
        }

        self.cold.lbd_ema_fast > LOOKAHEAD_LBD_THRESHOLD * self.cold.lbd_ema_slow
    }

    /// Run a lookahead round: probe all unassigned variables and store
    /// the best splitting variable for the next CDCL decision.
    ///
    /// Also detects failed literals as a side effect (units forced at
    /// level 0), which can simplify the formula.
    ///
    /// REQUIRES: `decision_level == 0`
    pub(in crate::solver) fn run_lookahead_round(&mut self) {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: run_lookahead_round() called at decision_level {}",
            self.decision_level
        );

        let trail_before = self.trail.len();

        // Run the core lookahead algorithm (defined in lookahead.rs).
        let best_lit = self.lookahead();

        // Store the result for the next decision.
        self.cold.lookahead_decision = best_lit;

        // Update scheduling state with growing backoff (#8322).
        // Each round doubles the interval: 10K, 20K, 40K, 80K, ...
        // This prevents repeated expensive rounds on large formulas while
        // still allowing early rounds that find valuable failed literals.
        // Compute the previous interval BEFORE updating last_lookahead_conflict.
        let prev_interval = self
            .cold
            .next_lookahead_conflict
            .saturating_sub(self.cold.last_lookahead_conflict)
            .max(LOOKAHEAD_INTERVAL);
        self.cold.last_lookahead_conflict = self.num_conflicts;
        let next_interval = (prev_interval * 2).min(200_000);
        self.cold.next_lookahead_conflict = self.num_conflicts.saturating_add(next_interval);

        // Update statistics.
        self.stats.lookahead_rounds += 1;

        // Count failed literals discovered (trail grows when lookahead
        // forces level-0 units via failed literal detection).
        let new_units = self.trail.len().saturating_sub(trail_before) as u64;
        self.stats.lookahead_failed_literals += new_units;

        tracing::info!(
            best_lit = ?best_lit.map(|l| (l.variable().index(), l.is_positive())),
            failed_literals = new_units,
            round = self.stats.lookahead_rounds,
            "lookahead round completed"
        );
    }

    /// Take the stored lookahead decision literal, if any.
    ///
    /// Returns `None` if no lookahead decision is pending, or if the
    /// variable has already been assigned (e.g., by failed literal
    /// detection or BCP since the lookahead ran).
    #[inline]
    pub(in crate::solver) fn take_lookahead_decision(&mut self) -> Option<Literal> {
        let lit = std::mem::take(&mut self.cold.lookahead_decision)?;
        if self.var_is_assigned(lit.variable().index()) {
            // Variable was assigned since lookahead ran (e.g., by
            // failed literal detection). The decision is stale.
            None
        } else {
            self.stats.lookahead_decisions_used += 1;
            Some(lit)
        }
    }
}
