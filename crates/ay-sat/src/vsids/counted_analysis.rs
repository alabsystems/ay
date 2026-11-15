// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepay the selected real activity kernel, never a replacement heuristic.
//! Preparation does not mutate scores or queue. The wrapper then invokes the
//! same ordinary kernels, with fallible growth inside actual sparse repair.

use super::*;
use crate::counted_storage::{try_reserve, try_vec_with, Result};
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

mod heap;
pub(in crate::vsids) use heap::{HeapOrdinary, HeapPolicy};
#[cfg(test)]
mod decay_tests;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ActivityStage {
    Chb,
    Evsids,
    DormantEvsids,
    Vmtf,
}

pub(super) fn pay_product(owner: &CountedAdmission, a: usize, b: usize) -> Result<()> {
    owner.admit(
        a.checked_mul(b)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?,
        0,
    )
}

impl VSIDS {
    /// Prepay the selected ordinary decay, including rescale/heap repair.
    /// No heuristic substitution: invoke the existing exact kernels.
    pub(crate) fn decay_counted(
        &mut self,
        stage: ActivityStage,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(8, 0)?;
        if !self.decay.is_finite()
            || self.decay <= 0.0
            || !self.increment.is_finite()
            || self.increment <= 0.0
        {
            return Err(invalid(owner, "invalid activity decay state"));
        }
        let rescale = self.increment / self.decay > 1e100;
        match stage {
            ActivityStage::Evsids => {
                if rescale {
                    self.prepare_analysis_rescale(owner)?;
                }
                owner.check()?;
                self.decay();
            }
            ActivityStage::DormantEvsids => {
                if !self.chb_loaded || self.chb_scores.is_none() {
                    return Err(invalid(owner, "dormant decay requires loaded scores"));
                }
                if rescale {
                    owner.admit(self.chb_scores.as_ref().map_or(0, Vec::len), 0)?;
                }
                owner.check()?;
                self.decay_evsids_dormant();
            }
            _ => return Err(invalid(owner, "invalid counted decay stage")),
        }
        owner.check()
    }

    pub(crate) fn analysis_activity_counted(
        &mut self,
        vars: &[usize],
        vals: &[i8],
        sorted: &[(u64, usize)],
        stage: ActivityStage,
        owner: &CountedAdmission,
    ) -> Result<()> {
        self.prepare_counted_analysis_activity(vars, stage, owner)?;
        match stage {
            ActivityStage::Chb => {
                self.chb_bump_batch(vars);
                self.chb_on_conflict();
            }
            ActivityStage::Evsids => {
                self.batch_bump_admitted(vars, vals, true, &heap::HeapCounted(owner))?;
            }
            ActivityStage::DormantEvsids => {
                self.bump_evsids_score_dormant_batch(vars);
                for &var in vars {
                    self.bump_vmtf_order_only(Variable(var as u32), vals);
                }
            }
            ActivityStage::Vmtf => self.batch_bump_queue_sorted(sorted, vals),
        }
        owner.check()
    }

    pub(crate) fn prepare_counted_analysis_activity(
        &mut self,
        vars: &[usize],
        stage: ActivityStage,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(8, 0)?;
        // CHB's on_conflict runs even for an empty analyzed batch.
        if stage == ActivityStage::Chb && self.chb_conflicts == u64::MAX {
            return Err(invalid(owner, "CHB conflict counter overflow"));
        }
        if vars.is_empty() {
            return Ok(());
        }
        let in_heap = self.analysis_activity_census(vars, owner)?;
        if stage != ActivityStage::Chb && (stage == ActivityStage::Vmtf || !self.queue_freeze) {
            self.bump_counter
                .checked_add(vars.len() as u64)
                .ok_or_else(|| invalid(owner, "VMTF bump counter overflow"))?;
        }
        pay_product(owner, vars.len(), 16)?;
        match stage {
            ActivityStage::Chb => self.prepare_analysis_chb(in_heap, owner),
            ActivityStage::Evsids => {
                if self.analysis_may_rescale(vars, &self.activities, owner)? {
                    self.prepare_analysis_rescale(owner)?;
                }
                Ok(()) // real shared repair admits its selected steps after the bump
            }
            ActivityStage::DormantEvsids => {
                if !self.chb_loaded {
                    return Err(invalid(owner, "dormant EVSIDS requires loaded CHB"));
                }
                let Some(scores) = self.chb_scores.as_ref() else {
                    return Err(invalid(owner, "dormant EVSIDS has no scores"));
                };
                if self.analysis_may_rescale(vars, scores, owner)? {
                    owner.admit(scores.len(), 0)?;
                }
                Ok(())
            }
            ActivityStage::Vmtf => Ok(()),
        }
    }

    fn analysis_activity_census(&self, vars: &[usize], owner: &CountedAdmission) -> Result<usize> {
        let mut in_heap = 0;
        for &var in vars {
            owner.admit(1, 0)?;
            if var >= self.activities.len()
                || var >= self.heap_pos.len()
                || var >= self.bump_order.len()
            {
                return Err(invalid(owner, "activity variable is out of bounds"));
            }
            if self.heap_pos[var] != INVALID_POS {
                in_heap += 1;
            }
        }
        Ok(in_heap)
    }

    fn prepare_analysis_chb(&mut self, in_heap: usize, owner: &CountedAdmission) -> Result<()> {
        if self.chb_scores.is_none() {
            let scores = try_vec_with(owner, self.activities.len(), |_| 0.0)?;
            let last = try_vec_with(owner, self.activities.len(), |_| 0)?;
            self.chb_scores = Some(scores);
            self.chb_last_conflict = Some(last);
        }
        if self.chb_loaded {
            self.prepare_analysis_heap(in_heap, owner)?;
        }
        Ok(())
    }

    fn analysis_may_rescale(
        &self,
        vars: &[usize],
        scores: &[f64],
        owner: &CountedAdmission,
    ) -> Result<bool> {
        // This conservative margin also covers duplicate vars and rounded
        // repeated additions, without allocating a shadow score array.
        let bound = batch::ACTIVITY_RESCALE_LIMIT * 0.25;
        let mut possible = self.increment >= bound / vars.len() as f64;
        for &var in vars {
            owner.admit(1, 0)?;
            possible |= scores[var] >= bound;
        }
        Ok(possible)
    }
}
