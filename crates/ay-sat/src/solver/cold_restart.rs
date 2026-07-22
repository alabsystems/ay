// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cold restart: periodic full search state reset for long-run diversification.
//!
//! Standard warm restarts preserve all learned state (clauses, variable scores,
//! phase saving), which can trap the solver in unproductive search regions.
//! Cold restart periodically forgets selected learned information to escape
//! these regions. The FO (Forget Order) variant randomizes variable branching
//! scores, forcing exploration of different search subspaces.
//!
//! Trigger schedule: conflict-count based with linear growth.
//!   `conflicts_since_last_cold_restart >= COLD_RESTART_INTERVAL * (count + 1)`
//! Later cold restarts happen less frequently, giving the solver more time
//! between disruptions.
//!
//! Reference: Xindi Zhang, Zhihan Chen, Shaowei Cai. "Revisiting Restarts of
//! CDCL: Cold Restart." arXiv:2404.16387v2, May 2024.

use super::*;

impl Solver {
    /// Check whether the linear cold-restart schedule should fire.
    ///
    /// Returns false when cold restart is disabled (env `AY_NO_COLD_RESTART`)
    /// or when too few conflicts have elapsed since the last cold restart.
    #[inline]
    pub(super) fn should_cold_restart(&self) -> bool {
        if !self.cold.cold_restart_enabled {
            return false;
        }

        let conflicts_since_last_cold = self
            .num_conflicts
            .saturating_sub(self.cold.cold_restart_last_conflict);
        let threshold =
            COLD_RESTART_INTERVAL.saturating_mul(self.cold.cold_restart_count.saturating_add(1));

        conflicts_since_last_cold >= threshold
    }

    /// Perform a cold restart: backtrack to level 0 and optionally forget
    /// variable ordering (FO) and/or variable phases (FP).
    ///
    /// FO (Forget Order): randomize VSIDS heap scores and VMTF queue ordering.
    /// This forces exploration of different search subspaces without removing
    /// any learned clauses. The paper shows FO alone gives +6-9 instances on
    /// SAT-COMP benchmarks.
    ///
    /// FP (Forget Phases): randomize all variable phases. Breaks phase-saving
    /// inertia. Disabled by default since FO alone is safer.
    ///
    /// All learned clauses are preserved (no FC variant by default).
    ///
    /// Reference: Zhang et al. (2024), arXiv:2404.16387, Section 3.
    pub(super) fn do_cold_restart(&mut self) {
        let cold_restart_count = self.cold.cold_restart_count;

        // Backtrack to decision level 0, unassigning all variables.
        self.backtrack(0);

        // FO: Forget Order — randomize variable branching scores.
        if self.cold.cold_restart_fo_enabled {
            // Use distinct seeds for heap vs queue to avoid correlated orderings.
            let seed = cold_restart_count
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1);
            self.vsids.shuffle_scores(seed);
            self.vsids.shuffle_queue(cold_restart_count);
        }

        // FP: Forget Phases — randomize all variable polarities.
        if self.cold.cold_restart_fp_enabled {
            self.rephase_random();
        }

        self.cold.cold_restart_count = cold_restart_count.saturating_add(1);
        self.cold.cold_restart_last_conflict = self.num_conflicts;
        self.conflicts_since_restart = 0;
        self.stats.cold_restarts += 1;
    }
}
