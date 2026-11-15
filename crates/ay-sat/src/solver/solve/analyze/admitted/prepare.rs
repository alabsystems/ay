// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::counted_decision::invalid;
use crate::vsids::counted_analysis::ActivityStage;

impl Solver {
    pub(in crate::solver) fn prepare_counted_learning(
        &self,
        result: &ConflictResult,
        owner: &CountedAdmission,
    ) -> AdmissionResult<()> {
        owner.admit(96, 0)?;
        if ay_core::captured_misc_cli_flags().is_none() {
            return Err(invalid(
                owner,
                "learning requires captured process configuration",
            ));
        }
        let prune = self.should_prune_conflict_analysis_experiments();
        if result.learned_clause.is_empty()
            || result.backtrack_level >= self.decision_level
            || result.otfs_driving_clause.is_some()
            || !self.has_live_clause_trace()
            || self.cold.trace_ext_conflict
            || self.cold.diagnostic_trace.is_some()
            || self.cold.portfolio_clause_exporter.is_some()
            || (!prune
                && (self.cold.observer.is_some()
                    || self.cold.tla_trace.is_some()
                    || self.dip.enabled))
            || self.two_stage_clause_management
        {
            return Err(invalid(
                owner,
                "selected ordinary learning hook or driving path is not admitted",
            ));
        }
        if self.fixed_count > i64::MAX - 2
            || self.stats.lbd_count == u64::MAX
            || self
                .stats
                .lbd_sum
                .checked_add(u64::from(result.lbd))
                .is_none()
            || self
                .stats
                .lbd_buckets
                .iter()
                .any(|count| *count == u64::MAX)
        {
            return Err(invalid(owner, "learning statistics overflow"));
        }
        #[cfg(ay_logging)]
        if self.log_enabled {
            return Err(invalid(owner, "learning logging is not admitted"));
        }
        // Insertion and enqueue perform the exact selected scans under this
        // owner. This fixed admission covers EMA/root marks and no-op hooks.
        Ok(())
    }

    pub(in crate::solver) fn complete_counted_learning(
        &mut self,
        result: &mut ConflictResult,
        actual: u32,
        owner: &CountedAdmission,
    ) -> AdmissionResult<usize> {
        let off = self.learn_asserting_clause_admitted(result, actual, &Counted(owner))?;
        if !self.should_prune_conflict_analysis_experiments() {
            self.eager_subsume_counted(off, owner)?;
        }
        match self.active_branch_heuristic {
            BranchHeuristic::Evsids => self.vsids.decay_counted(ActivityStage::Evsids, owner)?,
            BranchHeuristic::Chb => self
                .vsids
                .decay_counted(ActivityStage::DormantEvsids, owner)?,
            BranchHeuristic::Vmtf => owner.admit(1, 0)?,
        }
        // two-stage and DIP hooks were rejected when selected, never disabled.
        // The real reduction predicate includes a reconstruction-record scan
        // only when a clause-byte limit is installed.
        owner.admit(32, 0)?;
        if self.cold.max_clause_db_bytes.is_some() {
            owner.admit(self.inproc.reconstruction.len(), 0)?;
        }
        if self.should_reduce_db() {
            return Err(invalid(
                owner,
                "selected post-learning database reduction is not admitted",
            ));
        }
        owner.check()?;
        Ok(off)
    }
}
