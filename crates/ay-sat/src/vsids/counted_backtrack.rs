// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capacity-only preparation for real backtrack heap/queue reinsertion.

use super::*;
use crate::counted_storage::{try_reserve, Result};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

#[derive(Default)]
pub(crate) struct BacktrackReservation {
    heap: usize,
    buckets: bucket_queue::BacktrackBuckets,
}

impl VSIDS {
    pub(crate) fn plan_backtrack_candidate(
        &self,
        var: Variable,
        bucket: bool,
        plan: &mut BacktrackReservation,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(1, 0)?;
        if self.heap_pos[var.index()] == INVALID_POS {
            plan.heap = plan
                .heap
                .checked_add(1)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        }
        if bucket {
            self.bucket_queue
                .plan_backtrack(var, &self.activities, &mut plan.buckets, owner)?;
        }
        Ok(())
    }

    pub(crate) fn reserve_backtrack(
        &mut self,
        plan: BacktrackReservation,
        owner: &CountedAdmission,
    ) -> Result<()> {
        let final_len = self
            .heap
            .len()
            .checked_add(plan.heap)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        // One push plus at most floor(log2(final_len)) sift-up iterations per
        // candidate. Reimplied lambda variables may not need their reservation.
        let depth = final_len.bit_width() as usize;
        let work = plan
            .heap
            .checked_mul(depth + 1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 0)?;
        try_reserve(owner, &mut self.heap, plan.heap)?;
        self.bucket_queue.reserve_backtrack(plan.buckets, owner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::counted_storage::test_owner;

    fn empty_heap() -> VSIDS {
        let mut vsids = VSIDS::new(64);
        for index in 0..64 {
            vsids.remove_from_heap(Variable(index as u32));
            vsids.activities[index] = ((index * 17) % 64) as f64;
        }
        vsids.heap.shrink_to_fit();
        vsids
    }

    #[test]
    fn paid_real_heap_and_bucket_growth_never_allocates_during_reinsertion() {
        let mut expected = empty_heap();
        let mut actual = empty_heap();
        let owner = test_owner(1_000_000, 1_000_000);
        let mut plan = BacktrackReservation::default();
        for index in (0..64).rev() {
            actual
                .plan_backtrack_candidate(Variable(index), true, &mut plan, &owner)
                .unwrap();
        }
        actual.reserve_backtrack(plan, &owner).unwrap();
        let capacity = actual.heap.capacity();
        for index in (0..64).rev() {
            let var = Variable(index);
            actual.insert_into_heap(var);
            actual.bucket_queue_insert(var);
            expected.insert_into_heap(var);
            expected.bucket_queue_insert(var);
            assert_eq!(actual.heap.capacity(), capacity);
        }
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert!(owner.usage().unwrap().storage_admitted >= 64 * size_of::<u32>());
    }

    #[test]
    fn heap_growth_refusal_preserves_membership_and_priority_order() {
        let mut actual = empty_heap();
        let before = format!("{actual:?}");
        let owner = test_owner(1_000_000, 0);
        let mut plan = BacktrackReservation::default();
        actual
            .plan_backtrack_candidate(Variable(1), false, &mut plan, &owner)
            .unwrap();
        assert_eq!(
            actual.reserve_backtrack(plan, &owner),
            Err(CountedAdmissionError::StorageExhausted)
        );
        assert_eq!(format!("{actual:?}"), before);
    }
}
