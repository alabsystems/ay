// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Branch-heuristic selection helpers and MAB epoch management.

use super::*;

impl Solver {
    #[inline]
    pub(super) fn legacy_branch_heuristic(&self) -> BranchHeuristic {
        if self.stable_mode {
            BranchHeuristic::Evsids
        } else {
            BranchHeuristic::Vmtf
        }
    }

    /// Switch the active branch heuristic, handling CHB score swapping.
    ///
    /// When transitioning to or from CHB, the EVSIDS activities array and
    /// chb_scores array are swapped so the binary heap always orders by
    /// the active heuristic's scores.
    pub(super) fn switch_branch_heuristic(&mut self, new_heuristic: BranchHeuristic) {
        let old = self.active_branch_heuristic;
        if old == new_heuristic {
            return;
        }
        let leaving_chb = old == BranchHeuristic::Chb;
        let entering_chb = new_heuristic == BranchHeuristic::Chb;
        if leaving_chb || entering_chb {
            self.vsids.swap_chb_scores();
        }
        self.active_branch_heuristic = new_heuristic;
    }

    pub(super) fn sync_active_branch_heuristic(&mut self) {
        let target = match self.cold.branch_selector_mode {
            BranchSelectorMode::LegacyCoupled => self.legacy_branch_heuristic(),
            BranchSelectorMode::Fixed(heuristic) => heuristic,
            BranchSelectorMode::MabUcb1 if self.stable_mode => {
                if self
                    .cold
                    .branch_mab
                    .is_arm_active(self.active_branch_heuristic)
                {
                    self.active_branch_heuristic
                } else {
                    self.cold.branch_mab.select_next_arm()
                }
            }
            BranchSelectorMode::MabUcb1 => self.legacy_branch_heuristic(),
        };
        self.switch_branch_heuristic(target);
    }

    pub(super) fn reset_branch_heuristic_selector(&mut self) {
        self.cold.branch_mab.reset();
        let target = match self.cold.branch_selector_mode {
            BranchSelectorMode::LegacyCoupled => self.legacy_branch_heuristic(),
            BranchSelectorMode::Fixed(heuristic) => heuristic,
            BranchSelectorMode::MabUcb1 if self.stable_mode => self.cold.branch_mab.default_arm(),
            BranchSelectorMode::MabUcb1 => self.legacy_branch_heuristic(),
        };
        self.switch_branch_heuristic(target);
        self.start_branch_heuristic_epoch();
    }

    #[inline]
    pub(super) fn start_branch_heuristic_epoch(&mut self) {
        self.cold.branch_mab.start_epoch(
            self.num_conflicts,
            self.num_decisions,
            self.num_propagations,
            self.stats.lbd_sum,
            self.stats.lbd_count,
        );
    }

    /// Complete the current MAB epoch and select the next arm.
    ///
    /// Returns `true` if the active branch heuristic was switched to a different
    /// arm. The caller uses this to skip trail reuse on arm switches
    /// (AE-Kissat-MAB `restart.c:192`).
    ///
    /// In `MabUcb1` mode, epoch scoring is gated behind stable mode. In focused
    /// mode, the MAB is not consulted and the legacy heuristic is used instead
    /// (AE-Kissat-MAB `restart.c:188`: `if (solver->stable && solver->mab)`).
    ///
    /// Stable epochs shorter than the MAB conflict threshold stay open across
    /// restarts. Otherwise frequent short stable restarts can discard every
    /// telemetry sample before the selector has enough conflicts to score.
    pub(super) fn complete_branch_heuristic_epoch_if_needed(&mut self) -> bool {
        match self.cold.branch_selector_mode {
            BranchSelectorMode::LegacyCoupled | BranchSelectorMode::Fixed(_) => {
                self.sync_active_branch_heuristic();
                false
            }
            BranchSelectorMode::MabUcb1 => {
                // Gate 3: stable-mode-only MAB (AE-Kissat-MAB restart.c:188).
                if !self.stable_mode {
                    let prev = self.active_branch_heuristic;
                    self.switch_branch_heuristic(self.legacy_branch_heuristic());
                    self.start_branch_heuristic_epoch();
                    return self.active_branch_heuristic != prev;
                }

                let completed = self.cold.branch_mab.finalize_epoch(
                    self.active_branch_heuristic,
                    self.num_conflicts,
                    self.num_decisions,
                    self.num_propagations,
                    self.stats.lbd_sum,
                    self.stats.lbd_count,
                );
                let arm_switched = if completed {
                    let prev = self.active_branch_heuristic;
                    let next = self.cold.branch_mab.select_next_arm();
                    self.switch_branch_heuristic(next);
                    if next != prev {
                        self.stats.mab_arm_switches += 1;
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                if completed {
                    self.start_branch_heuristic_epoch();
                }
                arm_switched
            }
        }
    }

    #[inline]
    pub(super) fn pick_branch_variable_by_active_heuristic(&mut self) -> Option<Variable> {
        let picked = self.pick_branch_variable_by_heuristic(self.active_branch_heuristic);
        if picked.is_some()
            && self.stats.dense_clique_mab_branch_route_enabled != 0
            && matches!(self.cold.branch_selector_mode, BranchSelectorMode::MabUcb1)
        {
            self.stats.record_dense_clique_mab_branch_route_exercised();
        }
        picked
    }

    #[inline]
    fn pick_branch_variable_by_heuristic(
        &mut self,
        heuristic: BranchHeuristic,
    ) -> Option<Variable> {
        match heuristic {
            BranchHeuristic::Evsids | BranchHeuristic::Chb => loop {
                match self.vsids.pick_branching_variable(&self.vals) {
                    Some(var) if self.var_lifecycle.is_removed(var.index()) => {
                        self.vsids.remove_from_heap(var);
                    }
                    result => break result,
                }
            },
            BranchHeuristic::Vmtf => self.vsids.pick_branching_variable_vmtf_with_lifecycle(
                &self.vals,
                self.var_lifecycle.as_slice(),
            ),
        }
    }

    #[inline]
    pub(super) fn branch_priority_is_lower(
        &self,
        lhs: Variable,
        rhs: Variable,
        heuristic: BranchHeuristic,
    ) -> bool {
        match heuristic {
            BranchHeuristic::Evsids | BranchHeuristic::Chb => {
                self.vsids.activity(lhs) < self.vsids.activity(rhs)
            }
            BranchHeuristic::Vmtf => self.vsids.bump_order(lhs) < self.vsids.bump_order(rhs),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mab_sync_uses_vmtf_in_focused_mode() {
        let mut solver = Solver::new(4);
        solver.set_branch_selector_ucb1(true);

        assert!(!solver.stable_mode);
        assert_eq!(solver.active_branch_heuristic, BranchHeuristic::Vmtf);

        solver.switch_branch_heuristic(BranchHeuristic::Chb);
        solver.sync_active_branch_heuristic();

        assert_eq!(
            solver.active_branch_heuristic,
            BranchHeuristic::Vmtf,
            "focused MAB mode must fall back to the legacy VMTF brancher"
        );
    }

    #[test]
    fn test_mab_reset_uses_vmtf_in_focused_mode() {
        let mut solver = Solver::new(4);
        solver.set_branch_selector_ucb1(true);
        solver.switch_branch_heuristic(BranchHeuristic::Chb);
        solver.stable_mode = false;

        solver.reset_branch_heuristic_selector();

        assert_eq!(
            solver.active_branch_heuristic,
            BranchHeuristic::Vmtf,
            "focused MAB reset must preserve the legacy focused VMTF brancher"
        );
    }

    #[test]
    fn test_mab_reset_uses_default_arm_in_stable_mode() {
        let mut solver = Solver::new(4);
        solver.stable_mode = true;
        solver.set_branch_selector_ucb1(true);
        solver.switch_branch_heuristic(BranchHeuristic::Vmtf);

        solver.reset_branch_heuristic_selector();

        assert_eq!(
            solver.active_branch_heuristic,
            BranchHeuristic::Evsids,
            "stable MAB reset must start from the default AE-Kissat arm"
        );
        assert!(solver
            .cold
            .branch_mab
            .is_arm_active(solver.active_branch_heuristic));
    }

    #[test]
    fn test_mab_sync_reenters_stable_on_active_arm() {
        let mut solver = Solver::new(4);
        solver.set_branch_selector_ucb1(true);
        solver.switch_branch_heuristic(BranchHeuristic::Vmtf);

        solver.stable_mode = true;
        solver.sync_active_branch_heuristic();

        assert_eq!(
            solver.active_branch_heuristic,
            BranchHeuristic::Evsids,
            "stable MAB mode must start from an active AE-Kissat arm, not focused VMTF"
        );
        assert!(solver
            .cold
            .branch_mab
            .is_arm_active(solver.active_branch_heuristic));
    }

    #[test]
    fn test_mab_focused_epoch_completion_resets_without_scoring_vmtf() {
        let mut solver = Solver::new(4);
        solver.set_branch_selector_ucb1(true);
        solver.num_conflicts = crate::mab::DEFAULT_HEURISTIC_EPOCH_MIN_CONFLICTS;
        solver.num_decisions = 10;
        solver.num_propagations = 100;

        let switched = solver.complete_branch_heuristic_epoch_if_needed();
        let stats = solver.branch_heuristic_epoch_stats();

        assert!(!switched);
        assert_eq!(
            solver.active_branch_heuristic,
            BranchHeuristic::Vmtf,
            "focused MAB epoch completion must keep legacy VMTF active"
        );
        assert_eq!(
            stats[BranchHeuristic::Vmtf.arm_index()].pulls,
            0,
            "focused-mode work must not be scored as a MAB VMTF pull"
        );
    }

    #[test]
    fn test_mab_stable_short_epochs_accumulate_until_threshold() {
        let mut solver = Solver::new(4);
        solver.set_branch_selector_ucb1(true);
        solver.set_branch_selector_epoch_min_conflicts(10);
        solver.stable_mode = true;
        solver.sync_active_branch_heuristic();

        solver.num_conflicts = 6;
        solver.num_decisions = 6;
        solver.num_propagations = 60;
        solver.stats.lbd_sum = 12;
        solver.stats.lbd_count = 6;

        assert!(
            !solver.complete_branch_heuristic_epoch_if_needed(),
            "sub-threshold stable epoch must not switch arms"
        );
        assert_eq!(
            solver.branch_heuristic_epoch_stats()[BranchHeuristic::Evsids.arm_index()].pulls,
            0,
            "sub-threshold stable telemetry must not be scored"
        );

        solver.num_conflicts = 10;
        solver.num_decisions = 10;
        solver.num_propagations = 100;
        solver.stats.lbd_sum = 20;
        solver.stats.lbd_count = 10;

        assert!(
            solver.complete_branch_heuristic_epoch_if_needed(),
            "threshold-crossing stable epoch should score and explore the next arm"
        );
        assert_eq!(
            solver.branch_heuristic_epoch_stats()[BranchHeuristic::Evsids.arm_index()].pulls,
            1,
            "stable telemetry must accumulate across short restart intervals"
        );
        assert_eq!(
            solver.active_branch_heuristic,
            BranchHeuristic::Chb,
            "AE-Kissat 2-arm MAB should explore CHB after the first EVSIDS epoch"
        );
    }

    #[test]
    fn test_dense_clique_mab_branch_route_records_decision_exercise() {
        let mut solver = Solver::new(4);
        solver.set_branch_selector_ucb1(true);
        solver.set_dense_clique_mab_branch_route_enabled(true);

        assert!(solver.pick_branch_variable_by_active_heuristic().is_some());

        assert_eq!(solver.dense_clique_mab_branch_route_exercise_count(), 1);
        assert!(solver.dense_clique_mab_branch_route_exercised());
    }
}
