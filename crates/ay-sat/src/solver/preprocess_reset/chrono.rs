// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The ordinary chronological selection, with admission at actual visits.

use super::*;
use crate::solver::conflict_analysis_minimize::admitted::Policy;

impl Solver {
    pub(in crate::solver) fn chrono_backtrack_level_admitted<P: Policy>(
        &mut self,
        jump: u32,
        p: &P,
    ) -> Result<u32, P::Error> {
        p.work(1)?;
        debug_assert!(jump < self.decision_level);
        if !self.chrono_enabled || jump == 0 || jump >= self.decision_level.saturating_sub(1) {
            return Ok(jump);
        }
        let actual = if self.decision_level - jump > CHRONO_LEVEL_LIMIT {
            p.counter(self.stats.chrono_backtracks, 1)?;
            self.stats.chrono_backtracks += 1;
            self.decision_level - 1
        } else if self.chrono_reuse_trail && !self.deep_dive_full_backjump() {
            self.chrono_reuse_level_admitted(jump, p)?
        } else {
            jump
        };
        if actual != jump {
            self.emit_diagnostic_chrono_backtrack(self.decision_level, jump, actual);
        }
        Ok(actual)
    }

    /// Find the best variable above the jump level and return its level.
    ///
    /// This implements CaDiCaL's `chronoreusetrail` optimization. Instead of
    /// always backtracking to the asserting level, we look for valuable variables
    /// above that level. In stable mode, we look for the variable with highest
    /// VSIDS activity. In focused mode, we look for the most recently bumped
    /// variable. We then backtrack only to the level containing that trail
    /// position, preserving more of the useful search state.
    ///
    /// Key: we use trail POSITION to determine level, not the variable's stored
    /// level. This is important for correctness with chronological backtracking
    /// where variables can have out-of-order level assignments.
    pub(in crate::solver) fn chrono_reuse_level_admitted<P: Policy>(
        &mut self,
        jump: u32,
        p: &P,
    ) -> Result<u32, P::Error> {
        p.work(1)?;
        debug_assert!(jump < self.decision_level);
        let Some(&start) = self.trail_lim.get(jump as usize) else {
            return Ok(jump);
        };
        if start >= self.trail.len() {
            return Ok(jump);
        }
        let mut best = start;
        match self.active_branch_heuristic {
            BranchHeuristic::Evsids | BranchHeuristic::Chb => {
                let mut score = self.vsids.activity(self.trail[start].variable());
                for i in start + 1..self.trail.len() {
                    p.work(1)?;
                    let candidate = self.vsids.activity(self.trail[i].variable());
                    if score < candidate {
                        best = i;
                        score = candidate;
                    }
                }
            }
            BranchHeuristic::Vmtf => {
                let mut order = self.vsids.bump_order(self.trail[start].variable());
                for i in start + 1..self.trail.len() {
                    p.work(1)?;
                    let candidate = self.vsids.bump_order(self.trail[i].variable());
                    if order < candidate {
                        best = i;
                        order = candidate;
                    }
                }
            }
        }
        let mut level = jump;
        loop {
            p.work(1)?;
            if level >= self.decision_level - 1
                || level as usize >= self.trail_lim.len()
                || self.trail_lim[level as usize] > best
            {
                break;
            }
            level += 1;
        }
        if level > jump {
            p.counter(self.stats.chrono_backtracks, 1)?;
            self.stats.chrono_backtracks += 1;
        }
        debug_assert!(level >= jump && level < self.decision_level);
        Ok(level)
    }
}
