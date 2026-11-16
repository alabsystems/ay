// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::ConflictAnalyzer;
use crate::counted_storage::{try_reserve, Result};
use crate::decision_trace::counted_decision::invalid;
use crate::solver::VarData;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

impl ConflictAnalyzer {
    /// The actual forward LRAT chain and its parallel pivot vector share the
    /// original owner. Append and private/exceptional retirement are paid.
    pub(crate) fn prepare_counted_standard_chain(
        &mut self,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(4, 0)?;
        try_reserve(owner, &mut self.resolution_chain, 1)?;
        try_reserve(owner, &mut self.resolution_chain_pivots, 1)
    }

    /// Reserve the original get_result prepend before it mutates the clause.
    pub(crate) fn prepare_counted_finalize_result(
        &mut self,
        owner: &CountedAdmission,
    ) -> Result<()> {
        let work = self
            .learned
            .len()
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 0)?;
        try_reserve(owner, &mut self.learned, 1)
    }

    /// Native marking precedes register_jit_seen. The standard scope prepays
    /// this complete scan so interrupted bookkeeping cannot leak seen flags.
    pub(crate) fn retire_counted_standard(&mut self, vars: &mut [VarData]) {
        for data in vars.iter_mut() {
            data.set_seen(false);
        }
        self.retire_counted_ic3(vars);
        self.resolution_chain.clear();
        self.resolution_chain_pivots.clear();
    }

    /// The normal constructor has only scalars and empty, unallocated buffers.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        Ok(Self::new(num_vars))
    }

    /// The scoped counted walk starts with retired analysis scratch. Refusing
    /// legacy live scratch avoids silently discarding a proof chain or the
    /// ordinary clear() residual-mark diagnostic. Its own retirement is quiet
    /// and prepaid; it is not the ordinary next-conflict clear operation.
    pub(crate) fn prepare_counted_ic3_entry(
        &self,
        vars: &[VarData],
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(1, 0)?;
        if !self.seen_to_clear.is_empty()
            || !self.learned.is_empty()
            || self.asserting_lit.is_some()
            || !self.resolution_chain.is_empty()
            || !self.resolution_chain_pivots.is_empty()
            || !self.lbd_to_clear.is_empty()
        {
            return Err(invalid(
                owner,
                "counted IC3 analysis requires retired scratch",
            ));
        }
        #[cfg(debug_assertions)]
        if self.seen_true_count != 0 {
            return Err(invalid(
                owner,
                "counted IC3 analysis has stale seen accounting",
            ));
        }
        let scans = if cfg!(debug_assertions) { 2 } else { 1 };
        let work = vars
            .len()
            .checked_mul(scans)
            .and_then(|n| n.checked_add(16))
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        // The validation scan is real; debug also executes clear()'s existing
        // full-array assertion. Fixed reset/destruction bookkeeping is prepaid.
        owner.admit(work, 0)?;
        if vars.iter().any(|data| data.is_seen()) {
            return Err(invalid(
                owner,
                "counted IC3 analysis has untracked seen marks",
            ));
        }
        Ok(())
    }

    pub(crate) fn prepare_counted_ic3_seen(&mut self, owner: &CountedAdmission) -> Result<()> {
        // Mark/reset and each retained list element's eventual disposal.
        owner.admit(4, 0)?;
        try_reserve(owner, &mut self.seen_to_clear, 1)
    }

    pub(crate) fn prepare_counted_ic3_learned(&mut self, owner: &CountedAdmission) -> Result<()> {
        #[cfg(debug_assertions)]
        owner.admit(self.learned.len(), 0)?; // add_to_learned's duplicate check
        owner.admit(2, 0)?;
        try_reserve(owner, &mut self.learned, 1)
    }

    pub(crate) fn prepare_counted_minimize_copy(&mut self, owner: &CountedAdmission) -> Result<()> {
        // Copy traversal and eventual buffer clear/destruction are paid here.
        let work = self
            .learned
            .len()
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 0)?;
        try_reserve(owner, &mut self.clause_buf, self.learned.len())
    }

    /// No callbacks, allocation, logging or assertions during retirement.
    /// Every visited slot and retained element was prepaid before insertion.
    /// This also works while an internal/opaque-payload panic is unwinding.
    pub(crate) fn retire_counted_ic3(&mut self, vars: &mut [VarData]) {
        for &var in &self.seen_to_clear {
            if let Some(data) = vars.get_mut(var) {
                data.set_seen(false);
            }
        }
        for &level in &self.lbd_to_clear {
            if let Some(seen) = self.lbd_seen.get_mut(level) {
                *seen = false;
            }
        }
        self.seen_to_clear.clear();
        self.learned.clear();
        self.asserting_lit = None;
        self.lbd_to_clear.clear();
        #[cfg(debug_assertions)]
        {
            self.seen_true_count = 0;
        }
        self.learned_max_level = 0;
        self.learned_max_swap_idx = usize::MAX;
        self.learned_level_tracking_valid = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allocation_free_analyzer_preserves_normal_initial_state() {
        let owner = crate::counted_storage::test_owner(100_000, 100_000);
        let actual = ConflictAnalyzer::try_new_counted(7, &owner).unwrap();
        let expected = ConflictAnalyzer::new(7);
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert_eq!(
            owner.usage().unwrap().storage_admitted,
            size_of::<ConflictAnalyzer>()
        );
    }
}
