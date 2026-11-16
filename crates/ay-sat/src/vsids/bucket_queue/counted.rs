// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_reserve, Result};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

#[derive(Default)]
pub(in crate::vsids) struct BacktrackBuckets {
    additions: [usize; MAX_BUCKETS],
    membership_len: usize,
}

impl BucketQueue {
    pub(in crate::vsids) fn admit_selection(&self, owner: &CountedAdmission) -> Result<()> {
        // During one selection the cursor only moves forward. Every queued
        // member is popped at most once, and every empty class crossed once.
        let work = self
            .len()
            .checked_add(MAX_BUCKETS)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 0)
    }

    pub(in crate::vsids) fn plan_backtrack(
        &self,
        var: Variable,
        activities: &[f64],
        plan: &mut BacktrackBuckets,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(1, 0)?;
        if self.contains(var) {
            return Ok(());
        }
        let bucket = Self::activity_to_bucket_relative(activities[var.index()], self.max_exponent);
        plan.additions[bucket] = plan.additions[bucket]
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        let end = var
            .index()
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        plan.membership_len = plan.membership_len.max(end);
        Ok(())
    }

    pub(in crate::vsids) fn reserve_backtrack(
        &mut self,
        plan: BacktrackBuckets,
        owner: &CountedAdmission,
    ) -> Result<()> {
        let growth = plan.membership_len.saturating_sub(self.in_queue.len());
        owner.admit(growth, 0)?; // ensure_capacity's later initialization
        try_reserve(owner, &mut self.in_queue, growth)?;
        owner.admit(MAX_BUCKETS, 0)?; // planning visits
        for (bucket, additional) in self.buckets.iter_mut().zip(plan.additions) {
            owner.admit(additional, 0)?; // actual insertion visits
            try_reserve(owner, bucket, additional)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::counted_storage::test_owner;

    #[test]
    fn paid_all_bucket_classes_and_membership_growth_are_allocation_free_after_reserve() {
        let mut actual = BucketQueue::new();
        actual.max_exponent = f64_exponent(2f64.powi(31));
        let activities: Vec<_> = (0..64).map(|i| 2f64.powi(i % 32)).collect();
        let mut expected = actual.clone();
        let mut plan = BacktrackBuckets::default();
        let owner = test_owner(1_000_000, 1_000_000);
        for index in 0..64 {
            actual
                .plan_backtrack(Variable(index), &activities, &mut plan, &owner)
                .unwrap();
        }
        actual.reserve_backtrack(plan, &owner).unwrap();
        let capacities = actual.buckets.each_ref().map(|bucket| bucket.capacity());
        let membership_capacity = actual.in_queue.capacity();
        for index in 0..64 {
            actual.push_with_activity(Variable(index), &activities);
            expected.push_with_activity(Variable(index), &activities);
            assert_eq!(
                actual.buckets.each_ref().map(|bucket| bucket.capacity()),
                capacities
            );
            assert_eq!(actual.in_queue.capacity(), membership_capacity);
        }
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
}
