// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Geometric native container maintenance for versioned LOGICAL work. Unlike
//! the older narrow callback API, this does not claim a hash-probe CPU bound.

use super::*;
use crate::term::controlled_intern::counted::{
    storage, CountedTermError, TermConstructionAdmission,
};

type CountedResult<T> = std::result::Result<T, CountedTermError>;

impl TermStore {
    pub(in crate::term::controlled_intern) fn counted_bucket_plan(
        &self,
        hash: u64,
        owner: &dyn TermConstructionAdmission,
    ) -> CountedResult<BucketPlan> {
        owner.admit(1, 0)?;
        let bucket = self.hash_cons.get(&hash);
        let len = bucket.map_or(0, Vec::len);
        let capacity = bucket.map_or(0, Vec::capacity);
        let bucket_bytes = if len < capacity {
            0
        } else {
            capacity
                .checked_mul(2)
                .and_then(|n| n.max(4).checked_mul(size_of::<TermId>()))
                .ok_or_else(|| storage::storage(owner))?
        };
        Ok(BucketPlan {
            existing: None,
            len,
            capacity,
            present: bucket.is_some(),
            bucket_bytes,
        })
    }

    pub(in crate::term::controlled_intern) fn counted_reserve(
        &mut self,
        hash: u64,
        plan: &BucketPlan,
        owner: &dyn TermConstructionAdmission,
    ) -> CountedResult<PreparedBucket> {
        self.true_memory_cache.set(0);
        storage::reserve(&mut self.terms, 1, owner)?;
        if plan.present {
            owner.admit(1, 0)?;
            let bucket = self
                .hash_cons
                .get_mut(&hash)
                .ok_or(CountedTermError::InvalidInput)?;
            storage::reserve(bucket, 1, owner)?;
            let growth = bucket
                .capacity()
                .checked_sub(plan.capacity)
                .and_then(|n| n.checked_mul(size_of::<TermId>()))
                .ok_or_else(|| storage::storage(owner))?;
            Ok(PreparedBucket { new: None, growth })
        } else {
            self.counted_hash_reserve(owner)?;
            let mut bucket = Vec::new();
            storage::reserve(&mut bucket, 1, owner)?;
            Ok(PreparedBucket {
                growth: bucket.capacity() * size_of::<TermId>(),
                new: Some(bucket),
            })
        }
    }

    fn counted_hash_reserve(&mut self, owner: &dyn TermConstructionAdmission) -> CountedResult<()> {
        owner.admit(1, 0)?;
        if self.hash_cons.len() == self.hash_cons.capacity() {
            let old = self.hash_cons.allocation_size();
            let bytes = old
                .checked_mul(4)
                .and_then(|n| n.checked_add(4096))
                .ok_or_else(|| storage::storage(owner))?;
            owner.admit(
                self.hash_cons
                    .len()
                    .checked_add(old)
                    .ok_or_else(|| storage::work(owner))?,
                bytes,
            )?;
        }
        self.hash_cons
            .try_reserve(1)
            .map_err(|_| storage::storage(owner))
    }

    pub(in crate::term::controlled_intern) fn counted_credit(
        &mut self,
        heap: usize,
        bucket: usize,
        owner: &dyn TermConstructionAdmission,
    ) -> CountedResult<Credit> {
        owner.admit(1, 0)?;
        let total = size_of::<TermEntry>()
            .checked_add(heap)
            .and_then(|n| n.checked_add(bucket))
            .ok_or_else(|| storage::storage(owner))?;
        let instance = self
            .instance_term_bytes
            .checked_add(total)
            .ok_or_else(|| storage::storage(owner))?;
        let heaps = self
            .heap_data_bytes
            .checked_add(heap)
            .ok_or_else(|| storage::storage(owner))?;
        let buckets = self
            .bucket_capacity_bytes
            .checked_add(bucket)
            .ok_or_else(|| storage::storage(owner))?;
        adjust_global(total, 0).map_err(|_| storage::storage(owner))?;
        self.instance_term_bytes = instance;
        self.heap_data_bytes = heaps;
        self.bucket_capacity_bytes = buckets;
        Ok(Credit { heap, bucket })
    }
}
