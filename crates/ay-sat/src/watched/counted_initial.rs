// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pre-admission for the existing exact initial watch layout and its ordering.

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};

type Result<T> = std::result::Result<T, CountedAdmissionError>;

impl ExactWatchPlan {
    pub(crate) fn try_new_counted(num_lits: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(size_of::<Self>(), 0)?;
        Ok(Self {
            counts: crate::counted_storage::try_vec_with(owner, num_lits, |_| 0)?,
        })
    }

    pub(crate) fn count_watch_counted(
        &mut self,
        lit: Literal,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(2, 0)?;
        let Some(count) = self.counts.get_mut(lit.index()) else {
            return Err(owner.refuse(CountedAdmissionError::Original(
                QueryError::Invalid("initial watch escaped admitted namespace").into(),
            )));
        };
        *count = count
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        Ok(())
    }
}

impl WatchedLists {
    pub(crate) fn apply_exact_layout_counted(
        &mut self,
        plan: &ExactWatchPlan,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(2, 0)?;
        if !self.is_unbuilt() || self.meta.len() != plan.counts.len() {
            return Err(owner.refuse(CountedAdmissionError::Original(
                QueryError::Invalid("initial watch layout is not fresh").into(),
            )));
        }
        let mut total = 0usize;
        for &count in &plan.counts {
            owner.admit(2, 0)?;
            let capacity = match count {
                0 => 0,
                1 | 2 => 2,
                _ => count
                    .checked_next_power_of_two()
                    .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?,
            };
            total = total
                .checked_add(capacity as usize)
                .filter(|n| u32::try_from(*n).is_ok())
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        }
        let reserved = if total >= WATCH_BUF_LARGE_ENTRIES {
            total
                .checked_add(total / WATCH_BUF_EXACT_BUILD_HEADROOM_DIVISOR)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?
        } else {
            total
        };
        let transaction = plan
            .counts
            .len()
            .checked_mul(4)
            .and_then(|n| n.checked_add(total))
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(transaction, 0)?;
        self.buf_entries = crate::counted_storage::try_reserved_exact(owner, reserved)?;
        // Fresh exact-sized metadata and the full unified reservation make
        // every allocation branch in this unchanged layout function a no-op.
        self.apply_exact_layout(plan);
        owner.check()
    }
}
