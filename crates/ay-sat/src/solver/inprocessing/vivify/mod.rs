// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Vivification: learned and irredundant clause strengthening.
//!
//! Split into submodules:
//! - `tier`: per-tier clause processing loop
//! - `analysis`: backward trail analysis for conflicts and implied literals

mod analysis;
mod tier;

use super::super::*;
use super::VivifyTierRun;

impl Solver {
    /// Run vivification (wrapper: always reschedules learned vivification).
    ///
    /// REQUIRES: decision_level == 0
    /// ENSURES: decision_level == 0
    pub(in crate::solver) fn vivify(&mut self) -> bool {
        let result = self.vivify_body();
        self.inproc_ctrl
            .vivify
            .reschedule(self.num_conflicts, VIVIFY_INTERVAL);
        result
    }

    /// Vivify body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Vivification tries to remove literals from clauses by temporarily assuming
    /// their negation and propagating. If this leads to a conflict or implies
    /// another literal in the clause, the literal can be removed.
    ///
    /// CaDiCaL vivifies both irredundant and redundant clauses (vivify.cpp).
    /// Irredundant vivification is critical for structured instances (6-47x gap).
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn vivify_body(&mut self) -> bool {
        if !self.enter_inprocessing() {
            return false;
        }

        // Scheduling handled by vivify_skip_reason() in the inprocessing
        // scheduler. No inner threshold — per-tier budgets limit effort. (#8134)

        let run_learned = self.should_vivify_learned();
        let run_irred = self.should_vivify_irred();

        let noccs = self.vivify_literal_scores();
        let mut enqueued_units = false;

        // AY_XP_VIV_PERMILLE (default-OFF measured-infra, see xp_probe_vivify.rs):
        // unset => shipping VIVIFY_EFFORT_PERMILLE, so the default budget is
        // byte-for-byte unchanged.
        let viv_permille = vivify_permille().unwrap_or(VIVIFY_EFFORT_PERMILLE);

        if run_learned {
            // CaDiCaL-style tick-proportional budgeting (vivify.cpp:1744).
            // Budget = VIVIFY_EFFORT_PERMILLE/1000 * (search_ticks - last_vivify_ticks).
            // Floor at VIVIFY_MIN_EFFORT to ensure progress even early in the search.
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_vivify_ticks);
            let raw_budget = ticks_delta * viv_permille / 1000;
            let total_budget = raw_budget.max(VIVIFY_MIN_EFFORT);

            // Split budget across tiers by weight (CaDiCaL vivify.cpp:1753-1764).
            let total_weight =
                VIVIFY_TIER_WEIGHT_CORE + VIVIFY_TIER_WEIGHT_TIER2 + VIVIFY_TIER_WEIGHT_OTHER;
            let budget_core = total_budget * VIVIFY_TIER_WEIGHT_CORE / total_weight;
            let budget_tier2 = total_budget * VIVIFY_TIER_WEIGHT_TIER2 / total_weight;
            let budget_other = total_budget * VIVIFY_TIER_WEIGHT_OTHER / total_weight;

            for (tier, tier_budget) in [
                (VivifyTier::LearnedCore, budget_core),
                (VivifyTier::LearnedTier2, budget_tier2),
                (VivifyTier::LearnedOther, budget_other),
            ] {
                let run = self.vivify_tier(tier, &noccs, tier_budget);
                if run.conflict {
                    return true;
                }
                enqueued_units |= run.enqueued_units;
            }
            self.cold.last_vivify_ticks = self.search_ticks[0] + self.search_ticks[1];
        }

        if run_irred {
            // Irredundant vivification uses its own tick delta and weight.
            let ticks_delta = (self.search_ticks[0] + self.search_ticks[1])
                .saturating_sub(self.cold.last_vivify_irred_ticks);
            let irred_budget = ticks_delta * viv_permille / 1000 * VIVIFY_TIER_WEIGHT_IRRED
                / (VIVIFY_TIER_WEIGHT_CORE
                    + VIVIFY_TIER_WEIGHT_TIER2
                    + VIVIFY_TIER_WEIGHT_OTHER
                    + VIVIFY_TIER_WEIGHT_IRRED);
            // Use at least a minimum budget based on the old fixed count to
            // prevent starvation on problems with very few search ticks.
            let irred_budget = irred_budget.max(VIVIFY_IRRED_CLAUSES_PER_CALL as u64);

            let run = self.vivify_tier(VivifyTier::Irredundant, &noccs, irred_budget);
            if run.conflict {
                return true;
            }
            enqueued_units |= run.enqueued_units;
            self.cold.last_vivify_irred_ticks = self.search_ticks[0] + self.search_ticks[1];
            self.schedule_next_irredundant_vivify(run);
        }

        if enqueued_units && self.vivify_propagate().is_some() {
            return true;
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: vivify() did not restore decision level to 0"
        );
        false
    }

    /// Compute Jeroslow-Wang literal occurrence scores used to rank candidates.
    fn vivify_literal_scores(&self) -> Vec<i64> {
        // nocc(L) = sum over clauses C containing L of 2^(12 - min(|C|, 12))
        // Reference: CaDiCaL vivify.cpp:1370-1384
        let num_lits = self.num_vars * 2;
        let mut noccs: Vec<i64> = vec![0; num_lits];
        for idx in self.arena.active_indices() {
            // Skip garbage-kept husks — deleted from the live formula but
            // still yielded by active_indices() (heuristic accuracy only;
            // wf_ff5991a1 Defect 2 hardening).
            if self.arena.is_garbage_any(idx) {
                continue;
            }
            let shift = 12i32 - self.arena.len_of(idx) as i32;
            let score: i64 = if shift < 1 { 1 } else { 1i64 << shift };
            for &lit in self.arena.literals(idx) {
                let li = lit.index();
                if li < num_lits {
                    noccs[li] += score;
                }
            }
        }
        noccs
    }

    #[inline]
    fn schedule_next_irredundant_vivify(&mut self, run: VivifyTierRun) {
        if run.is_low_yield() {
            // Large-formula backoff cap (#8655): on BMC formulas, exponential
            // backoff can push the interval too long. Cap at 8x for large formulas.
            let max_mult = if self.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
                8
            } else {
                VIVIFY_IRRED_MAX_DELAY_MULTIPLIER
            };
            self.cold.vivify_irred_delay_multiplier = self
                .cold
                .vivify_irred_delay_multiplier
                .saturating_mul(2)
                .min(max_mult);
        } else {
            self.cold.vivify_irred_delay_multiplier = 1;
        }

        let delay = VIVIFY_IRRED_INTERVAL.saturating_mul(self.cold.vivify_irred_delay_multiplier);
        self.inproc_ctrl
            .vivify_irred
            .reschedule(self.num_conflicts, delay);
    }

    #[inline]
    fn vivify_clause_score(lits: &[Literal], noccs: &[i64]) -> i64 {
        let mut best = 0i64;
        let mut second = 0i64;
        for &lit in lits {
            let s = noccs.get(lit.index()).copied().unwrap_or(0);
            if s > best {
                second = best;
                best = s;
            } else if s > second {
                second = s;
            }
        }
        best + second
    }

    /// Run only irredundant (original-clause) vivification.
    ///
    /// This entry point is kept for focused tests and diagnostics. The normal
    /// solve loop should call `vivify()`, which schedules learned + irredundant
    /// tiers together.
    #[cfg(test)]
    pub(in crate::solver) fn vivify_irredundant(&mut self) -> bool {
        if !self.enter_inprocessing() || !self.inproc_ctrl.vivify.enabled {
            return false;
        }

        let noccs = self.vivify_literal_scores();
        self.ensure_reason_clause_marks_current();
        let run = self.vivify_tier(
            VivifyTier::Irredundant,
            &noccs,
            VIVIFY_IRRED_CLAUSES_PER_CALL as u64,
        );
        if run.conflict {
            return true;
        }

        self.schedule_next_irredundant_vivify(run);

        run.enqueued_units && self.vivify_propagate().is_some()
    }

    /// Run irredundant vivification during preprocessing (#8135).
    ///
    /// On small dense formulas (e.g., clique_n2_k10: 180 vars, 3160 clauses),
    /// vivification before BVE shortens clauses, reduces occurrence counts, and
    /// enables more effective variable elimination. Kissat achieves 88%
    /// vivification success on clique formulas; running vivification during
    /// preprocessing ensures AY gets the same benefit.
    ///
    /// Runs vivification in a **convergence loop**: each round that strengthens
    /// clauses creates new opportunities for the next round (shorter clauses
    /// produce stronger BCP propagation). The loop stops when:
    /// - A round produces no strengthening (convergence), or
    /// - The total tick budget is exhausted, or
    /// - PREPROCESS_VIVIFY_MAX_ROUNDS rounds have been completed.
    ///
    /// Kissat achieves its 88% vivification rate through repeated probing
    /// rounds during inprocessing, each of which calls vivify. AY matches
    /// this by running multiple rounds during preprocessing. The per-round
    /// budget is generous (VIVIFY_MIN_EFFORT = 1M ticks), and literal scores
    /// are recomputed between rounds so that shortened clauses get accurate
    /// candidate rankings.
    ///
    /// Returns true if UNSAT was derived (level-0 conflict from vivification).
    pub(in crate::solver) fn vivify_preprocess(&mut self) -> bool {
        if !self.inproc_ctrl.vivify.enabled {
            return false;
        }
        if self.decision_level != 0 {
            return false;
        }
        self.ensure_reason_clause_marks_current();

        // Total budget for all preprocessing vivification rounds.
        // Kissat's effective preprocessing vivification budget is ~10M ticks
        // (mineffort=10 * 1M). Use the same generous budget so that multiple
        // convergence rounds can complete on dense formulas.
        let total_budget = VIVIFY_MIN_EFFORT * PREPROCESS_VIVIFY_MAX_ROUNDS as u64;
        let mut total_ticks_used: u64 = 0;
        let mut total_strengthened: u64 = 0;
        let mut total_processed: u64 = 0;

        for round in 0..PREPROCESS_VIVIFY_MAX_ROUNDS {
            // Respect the preprocessing wall-clock deadline (#8448).
            // Without this check, vivification runs up to MAX_ROUNDS * 1M ticks
            // even when the preprocessing budget is exhausted. On Schur_161_5
            // (757 vars, 28K clauses), this caused 9-11s vivification within a
            // 2s preprocessing budget.
            if self.preprocess_timed_out() {
                break;
            }

            let remaining_budget = total_budget.saturating_sub(total_ticks_used);
            // Per-round budget: the remaining total budget, capped at
            // VIVIFY_MIN_EFFORT per round to allow multiple rounds.
            let round_budget = remaining_budget.min(VIVIFY_MIN_EFFORT);
            if round_budget == 0 {
                break;
            }

            // Recompute literal occurrence scores between rounds (#8360).
            // Clauses shortened in the previous round change occurrence counts,
            // which affects candidate ranking. Without recomputation, the
            // second round uses stale scores and processes candidates in a
            // suboptimal order, reducing vivification effectiveness.
            let noccs = self.vivify_literal_scores();

            let ticks_before = self.cold.vivify_ticks;
            let run = self.vivify_tier(VivifyTier::Irredundant, &noccs, round_budget);
            let ticks_used = self.cold.vivify_ticks.saturating_sub(ticks_before);
            total_ticks_used += ticks_used;
            total_strengthened += run.strengthened;
            total_processed += run.processed;

            if run.conflict {
                return true;
            }

            if run.enqueued_units && self.vivify_propagate().is_some() {
                return true;
            }

            // Convergence check: if this round strengthened nothing, further
            // rounds will not find new opportunities either.
            if run.strengthened == 0 {
                tracing::info!(
                    round = round + 1,
                    total_processed,
                    total_strengthened,
                    "preprocess vivification converged (no progress)"
                );
                break;
            }

            tracing::info!(
                round = round + 1,
                processed = run.processed,
                strengthened = run.strengthened,
                total_strengthened,
                "preprocess vivification round complete"
            );

            // Propagate level-0 consequences from unit clauses derived
            // during this round before starting the next round. This
            // ensures the next round sees the simplified formula.
            if self.decision_level > 0 {
                self.backtrack_without_phase_saving(0);
            }
        }

        if total_strengthened > 0 {
            tracing::info!(
                total_processed,
                total_strengthened,
                total_ticks_used,
                "preprocess vivification complete"
            );
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: vivify_preprocess did not restore decision level to 0"
        );
        false
    }
}
