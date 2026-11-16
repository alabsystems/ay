// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat 4.0.4's vivification schedule (`--sat-vivify-kissat`).
//!
//! Kissat vivifies once in every probe round (`probe.c:26-43`) under one
//! budget, 10% of the search ticks since the last probe round with a 10M
//! floor (`vivify.c:1395-1458`, `SET_EFFORT_LIMIT` in `kimits.h`). The budget
//! is split cumulatively in the ratio tier1:tier2:tier3:irredundant =
//! 3:3:1:3, so a tier that stops early leaves its ticks to the next one. The
//! irredundant share is 0 while its delay counter skips the round; an
//! irredundant pass that strengthens under 1% of the clauses it tries adds
//! one skipped round, and a productive one halves the delay. The tiers are
//! the focused-mode ones (`vivifyfocusedtiers`), and tier2's share goes to
//! tier1 when their glue limits are equal. No learned-clause tier runs
//! without learned clauses.
//!
//! AY's default gives the learned tiers and the irredundant clauses separate
//! budgets on their own conflict intervals (the irredundant one doubling up
//! to 64x), gates both by a tick threshold, classifies tier2 with the stable
//! boundary, and never vivifies in search on formulas under 1,000 variables
//! with density above 30.

use super::super::super::*;
use super::VivifyTierRun;

/// Kissat `vivifyeffort` (per mille).
const KISSAT_VIVIFY_EFFORT_PERMILLE: u64 = 100;
/// Kissat `mineffort` (10, in millions of ticks).
const KISSAT_MIN_EFFORT: u64 = 10_000_000;
/// Kissat `vivifytier1`, `vivifytier2`, `vivifytier3`, `vivifyirr`.
const KISSAT_VIVIFY_WEIGHTS: [u64; 4] = [3, 3, 1, 3];

impl Solver {
    /// Compute Jeroslow-Wang literal occurrence scores used to rank candidates,
    /// or under `--sat-vivify-order-kissat` Kissat's plain occurrence counts
    /// over the large clauses (vivify.c:49-56: every live clause of size > 2,
    /// learned ones included; binary clauses are not counted).
    pub(in crate::solver) fn vivify_literal_scores(&self) -> Vec<i64> {
        // nocc(L) = sum over clauses C containing L of 2^(12 - min(|C|, 12))
        // Reference: CaDiCaL vivify.cpp:1370-1384
        let num_lits = self.num_vars * 2;
        let mut noccs: Vec<i64> = vec![0; num_lits];
        let kissat_counts = self.cold.vivify_order_kissat;
        for idx in self.arena.active_indices() {
            // Skip garbage-kept husks — deleted from the live formula but
            // still yielded by active_indices() (heuristic accuracy only;
            // wf_ff5991a1 Defect 2 hardening).
            if self.arena.is_garbage_any(idx) {
                continue;
            }
            let len = self.arena.len_of(idx);
            if kissat_counts && len <= 2 {
                continue;
            }
            let shift = 12i32 - len as i32;
            let score: i64 = if kissat_counts || shift < 1 {
                1
            } else {
                1i64 << shift
            };
            for &lit in self.arena.literals(idx) {
                let li = lit.index();
                if li < num_lits {
                    noccs[li] += score;
                }
            }
        }
        noccs
    }

    /// The tier a clause belongs to for vivification: AY's reduction tiers,
    /// or under `--sat-vivify-kissat` Kissat's focused ones (`vivify.c:128-134`).
    pub(in crate::solver) fn vivify_clause_tier(&self, clause_idx: usize) -> ClauseTier {
        if !self.cold.vivify_kissat {
            return self.clause_tier(clause_idx);
        }
        let lbd = self.arena.lbd(clause_idx);
        if lbd <= self.tiers.tier1_lbd[0] {
            ClauseTier::Core
        } else if lbd <= self.tiers.tier2_lbd[0] {
            ClauseTier::Tier1
        } else {
            ClauseTier::Tier2
        }
    }

    /// Kissat `kissat_vivify` (see the module comment). Returns true on UNSAT.
    pub(super) fn vivify_body_kissat(&mut self) -> bool {
        if !self.enter_inprocessing() {
            return false;
        }
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let reference = ticks_now
            .saturating_sub(self.cold.last_inprobe_ticks)
            .max(KISSAT_MIN_EFFORT);
        let total = reference * KISSAT_VIVIFY_EFFORT_PERMILLE / 1000;

        let [mut tier1, mut tier2, mut tier3, mut irr] = KISSAT_VIVIFY_WEIGHTS;
        if !self.inproc_ctrl.vivify_irred.enabled || self.cold.vivify_irr_kissat_delay.delaying() {
            irr = 0;
        }
        if self.arena.redundant_count() == 0 {
            (tier1, tier2, tier3) = (0, 0, 0);
        }
        if tier1 > 0 && tier2 > 0 && self.tiers.tier1_lbd[0] == self.tiers.tier2_lbd[0] {
            (tier1, tier2) = (tier1 + tier2, 0);
        }
        let sum = tier1 + tier2 + tier3 + irr;
        if sum == 0 {
            return false;
        }

        let noccs = self.vivify_literal_scores();
        let start = self.cold.vivify_ticks;
        let mut limit = 0u64;
        let mut enqueued_units = false;
        for (tier, weight) in [
            (VivifyTier::LearnedCore, tier1),
            (VivifyTier::LearnedTier2, tier2),
            (VivifyTier::LearnedOther, tier3),
            (VivifyTier::Irredundant, irr),
        ] {
            if weight == 0 {
                continue;
            }
            limit += total * weight / sum;
            let budget = limit.saturating_sub(self.cold.vivify_ticks - start);
            let before = self.vivify_tier_snapshot();
            let run: VivifyTierRun = self.vivify_tier(tier, &noccs, budget);
            self.vivify_tier_account(tier, before);
            if run.conflict {
                return true;
            }
            enqueued_units |= run.enqueued_units;
            if tier == VivifyTier::Irredundant {
                let stats = &mut self.inproc.vivifier.stats;
                stats.irred_calls_inproc = stats.irred_calls_inproc.saturating_add(1);
                if run.is_low_yield() {
                    self.cold.vivify_irr_kissat_delay.bump();
                } else {
                    self.cold.vivify_irr_kissat_delay.reduce();
                }
            }
        }
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        self.cold.last_vivify_ticks = ticks_now;
        self.cold.last_vivify_irred_ticks = ticks_now;

        if enqueued_units && self.vivify_propagate().is_some() {
            return true;
        }
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: vivify() did not restore decision level to 0"
        );
        false
    }
}
