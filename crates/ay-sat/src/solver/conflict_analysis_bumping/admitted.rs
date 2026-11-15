// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::conflict_analysis_finalize::admitted::Policy;
use crate::vsids::counted_analysis::ActivityStage;

mod reason;

impl Solver {
    pub(in crate::solver) fn bump_analyzed_variables_admitted<P: Policy>(
        &mut self,
        p: &P,
    ) -> Result<(), P::Error> {
        p.work(8)?;
        let chb_active = matches!(
            self.cold.branch_selector_mode, BranchSelectorMode::MabUcb1 if self.stable_mode
        ) || matches!(
            self.cold.branch_selector_mode,
            BranchSelectorMode::Fixed(BranchHeuristic::Chb)
        );
        if chb_active {
            p.activity(self, ActivityStage::Chb)?;
        }
        match self.active_branch_heuristic {
            BranchHeuristic::Evsids => p.activity(self, ActivityStage::Evsids)?,
            BranchHeuristic::Chb => p.activity(self, ActivityStage::DormantEvsids)?,
            BranchHeuristic::Vmtf => {
                p.prepare_bump_order(self)?;
                self.bump_order_sort_buf.clear();
                self.bump_order_sort_buf.extend(
                    self.conflict
                        .analyzed_vars()
                        .iter()
                        .map(|&idx| (self.vsids.bump_order(Variable(idx as u32)), idx)),
                );
                p.sort_bumps(&mut self.bump_order_sort_buf)?;
                p.activity(self, ActivityStage::Vmtf)?;
            }
        }
        Ok(())
    }

    pub(in crate::solver) fn bump_reason_literals_admitted<P: Policy>(
        &mut self,
        p: &P,
    ) -> Result<(), P::Error> {
        let Some((mode, depth, limit)) = self.reason_bump_parameters(p)? else {
            return Ok(());
        };
        let saved = self.conflict.analyzed_vars().len();
        let mut added = 0;
        self.add_reason_literals_admitted(
            self.conflict.asserting_literal().negated(),
            depth,
            &mut added,
            limit,
            p,
        )?;
        for index in 0..self.conflict.learned_count() {
            p.work(1)?;
            if added >= limit {
                break;
            }
            let lit = self.conflict.learned_at(index);
            self.add_reason_literals_admitted(lit.negated(), depth, &mut added, limit, p)?;
        }
        if added >= limit {
            p.counter(self.cold.bumpreason_delay_interval[mode] as u64, 1)?;
            p.work(self.conflict.analyzed_vars().len() - saved)?;
            self.conflict.rollback_analyzed(saved, &mut self.var_data);
            self.cold.bumpreason_delay_interval[mode] += 1;
        } else {
            self.cold.bumpreason_delay_interval[mode] /= 2;
        }
        self.cold.bumpreason_delay_remaining[mode] = self.cold.bumpreason_delay_interval[mode];
        Ok(())
    }

    fn reason_bump_parameters<P: Policy>(
        &mut self,
        p: &P,
    ) -> Result<Option<(usize, u32, usize)>, P::Error> {
        p.work(16)?;
        if bumpreason_depth_override() == Some(0) {
            return Ok(None);
        }
        let kissat = self.cold.bump_reasons_kissat;
        if kissat && (self.cold.kissat_probing || self.decision_level == 1) {
            return Ok(None);
        }
        if !kissat && self.cold.bumpreason_decision_rate > 100.0 {
            return Ok(None);
        }
        let mode = if kissat {
            0
        } else {
            usize::from(self.stable_mode)
        };
        if self.cold.bumpreason_delay_remaining[mode] > 0 {
            self.cold.bumpreason_delay_remaining[mode] -= 1;
            return Ok(None);
        }
        if kissat && self.cold.kissat_decision_rate[usize::from(self.stable_mode)].value() >= 10.0 {
            return Ok(None);
        }
        let depth =
            bumpreason_depth_override().unwrap_or(if self.stable_mode && !kissat { 2 } else { 1 });
        debug_assert!(depth > 0);
        let saved = self.conflict.analyzed_vars().len();
        let limit = if kissat {
            p.work(saved)?;
            let above = self
                .conflict
                .analyzed_vars()
                .iter()
                .filter(|&&var| self.var_data[var].level > 0)
                .count();
            p.scale(above, 9, 1)?
        } else {
            p.scale(saved, 10, 0)?
        };
        Ok(Some((mode, depth, limit)))
    }
}
