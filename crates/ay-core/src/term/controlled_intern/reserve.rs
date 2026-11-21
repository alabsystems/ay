// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fallible container reserve and exact successful legacy memory accounting.

use super::*;
use crate::term::GLOBAL_TERM_BYTES;
use std::mem::size_of;

mod counted;
mod probe;
mod work;

pub(super) struct BucketPlan {
    pub existing: Option<TermId>,
    len: usize,
    capacity: usize,
    present: bool,
    pub bucket_bytes: usize,
}

pub(super) struct PreparedBucket {
    new: Option<Vec<TermId>>,
    pub growth: usize,
}

pub(super) struct Credit {
    heap: usize,
    bucket: usize,
}

fn limit() -> ControlledTermInternError {
    ControlledTermInternError::ResourceLimit
}

fn product(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b).ok_or_else(limit)
}

fn vector_cost<T>(len: usize) -> Result<usize> {
    product(
        len.checked_mul(2)
            .and_then(|n| n.checked_add(9))
            .ok_or_else(limit)?,
        size_of::<T>(),
    )
}

fn adjust_global(credit: usize, unused: usize) -> Result<()> {
    // Other stores updating this approximate counter do not exhaust this
    // invocation's storage. Retry contention; only arithmetic overflow refuses.
    #[allow(deprecated)]
    GLOBAL_TERM_BYTES
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
            current
                .checked_add(credit)
                .map(|next| next.saturating_sub(unused))
        })
        .map(|_| ())
        .map_err(|_| limit())
}

impl TermStore {
    pub(super) fn controlled_registry_credit(&mut self, bytes: usize) -> Result<()> {
        let instance = self
            .instance_term_bytes
            .checked_add(bytes)
            .ok_or_else(limit)?;
        let heap = self.heap_data_bytes.checked_add(bytes).ok_or_else(limit)?;
        adjust_global(bytes, 0)?;
        self.instance_term_bytes = instance;
        self.heap_data_bytes = heap;
        Ok(())
    }

    pub(super) fn controlled_slots(&self) -> Result<usize> {
        // allocation_size includes actual buckets even after tombstone-heavy
        // rollback; capacity() alone is only items + remaining growth.
        (self.hash_cons.allocation_size() / size_of::<(u64, Vec<TermId>)>())
            .checked_add(32)
            .ok_or_else(limit)
    }

    pub(super) fn controlled_probe_fee(&self, admission: &mut Admission<'_>) -> Result<()> {
        admission.pay(
            probe::work(self.hash_cons.allocation_size(), self.hash_cons.len())?,
            0,
        )
    }

    pub(super) fn controlled_bucket_plan(
        &self,
        hash: u64,
        term: &TermData,
        sort: &Sort,
        comparison_work: usize,
        admission: &mut Admission<'_>,
    ) -> Result<BucketPlan> {
        self.controlled_probe_fee(admission)?;
        let bucket = self.hash_cons.get(&hash);
        if let Some(ids) = bucket {
            for &id in ids {
                // Integer payload and recursive requested-sort equality are
                // both included in the caller's admitted comparison bound.
                admission.pay(comparison_work, 0)?;
                let entry = self
                    .terms
                    .get(id.index())
                    .ok_or(ControlledTermInternError::InvalidInput)?;
                if let (
                    TermData::Const(Constant::Rational(requested)),
                    TermData::Const(Constant::Rational(stored)),
                ) = (term, &entry.term)
                {
                    // Ratio equality may divide arbitrary-precision operands;
                    // byte equality pricing alone does not bound that work.
                    super::rational::admit(&requested.0, admission)?;
                    super::rational::admit(&stored.0, admission)?;
                }
                if &entry.term == term && &entry.sort == sort {
                    return Ok(BucketPlan {
                        existing: Some(id),
                        len: ids.len(),
                        capacity: ids.capacity(),
                        present: true,
                        bucket_bytes: 0,
                    });
                }
            }
        }
        let len = bucket.map_or(0, Vec::len);
        let capacity = bucket.map_or(0, Vec::capacity);
        let bucket_bytes = if len < capacity {
            0
        } else {
            product(vector_cost::<TermId>(len)?, 8)?
        };
        Ok(BucketPlan {
            existing: None,
            len,
            capacity,
            present: bucket.is_some(),
            bucket_bytes,
        })
    }

    fn controlled_map_reserve(&mut self, admission: &mut Admission<'_>) -> Result<()> {
        if self.hash_cons.capacity() == self.hash_cons.len() {
            let old = self.controlled_slots()?;
            let items = self.hash_cons.len().checked_add(1).ok_or_else(limit)?;
            let future = product(
                old.checked_add(items)
                    .and_then(|n| n.checked_add(32))
                    .ok_or_else(limit)?,
                4,
            )?;
            // Pinned hashbrown groups, including worst-case collisions and
            // in-place displacement. Storage and the 128 unit fee are unchanged.
            let scans = work::scans(self.hash_cons.allocation_size(), self.hash_cons.len())?;
            let bytes = product(
                old.checked_add(future).ok_or_else(limit)?,
                size_of::<(u64, Vec<TermId>)>() + 32,
            )?;
            admission.pay(product(scans, 128)?, product(bytes, 8)?)?;
        } else {
            admission.pay(1, 0)?;
        }
        self.hash_cons.try_reserve(1).map_err(|_| limit())
    }

    pub(super) fn controlled_reserve(
        &mut self,
        hash: u64,
        plan: &BucketPlan,
        admission: &mut Admission<'_>,
    ) -> Result<PreparedBucket> {
        self.true_memory_cache.set(0);
        if self.terms.len() == self.terms.capacity() {
            let bytes = vector_cost::<TermEntry>(self.terms.len())?;
            admission.pay(bytes, product(bytes, 8)?)?;
        } else {
            admission.pay(1, 0)?;
        }
        self.terms.try_reserve_exact(1).map_err(|_| limit())?;
        if plan.present {
            self.controlled_probe_fee(admission)?;
            let bucket = self
                .hash_cons
                .get_mut(&hash)
                .ok_or(ControlledTermInternError::InvalidInput)?;
            if plan.len == plan.capacity {
                admission.pay(vector_cost::<TermId>(plan.len)?, plan.bucket_bytes)?;
            } else {
                admission.pay(1, 0)?;
            }
            bucket.try_reserve_exact(1).map_err(|_| limit())?;
            let growth = product(
                bucket.capacity().saturating_sub(plan.capacity),
                size_of::<TermId>(),
            )?;
            Ok(PreparedBucket { new: None, growth })
        } else {
            self.controlled_map_reserve(admission)?;
            admission.pay(16, plan.bucket_bytes)?;
            let mut bucket = Vec::new();
            bucket.try_reserve_exact(1).map_err(|_| limit())?;
            Ok(PreparedBucket {
                growth: product(bucket.capacity(), size_of::<TermId>())?,
                new: Some(bucket),
            })
        }
    }

    pub(super) fn controlled_credit(&mut self, heap: usize, bucket: usize) -> Result<Credit> {
        let inline = size_of::<TermEntry>();
        let total = inline
            .checked_add(heap)
            .and_then(|n| n.checked_add(bucket))
            .ok_or_else(limit)?;
        let instance = self
            .instance_term_bytes
            .checked_add(total)
            .ok_or_else(limit)?;
        let heaps = self.heap_data_bytes.checked_add(heap).ok_or_else(limit)?;
        let buckets = self
            .bucket_capacity_bytes
            .checked_add(bucket)
            .ok_or_else(limit)?;
        adjust_global(total, 0)?;
        self.instance_term_bytes = instance;
        self.heap_data_bytes = heaps;
        self.bucket_capacity_bytes = buckets;
        Ok(Credit { heap, bucket })
    }

    pub(super) fn controlled_settle(
        &mut self,
        credit: Credit,
        heap: usize,
        bucket: usize,
    ) -> Result<()> {
        let unused_heap = credit.heap.checked_sub(heap).ok_or_else(limit)?;
        let unused_bucket = credit.bucket.checked_sub(bucket).ok_or_else(limit)?;
        let unused = unused_heap.checked_add(unused_bucket).ok_or_else(limit)?;
        // Preserve the credited fields if contention refuses this bounded CAS.
        adjust_global(0, unused)?;
        self.instance_term_bytes -= unused;
        self.heap_data_bytes -= unused_heap;
        self.bucket_capacity_bytes -= unused_bucket;
        // Approximate owned-memory accounting, NOT a work/storage grant refund.
        // Match Drop's saturating policy if a quiescent testing reset occurred.
        Ok(())
    }

    pub(super) fn controlled_commit_bucket(
        &mut self,
        hash: u64,
        id: TermId,
        entry: TermEntry,
        prepared: PreparedBucket,
    ) -> Result<()> {
        match prepared.new {
            Some(mut bucket) => {
                bucket.push(id);
                self.terms.push(entry);
                self.hash_cons.insert(hash, bucket);
            }
            None => {
                // Presence was checked before commit and &mut self excludes
                // mutation between that check and this reserved push.
                let bucket = self
                    .hash_cons
                    .get_mut(&hash)
                    .ok_or(ControlledTermInternError::InvalidInput)?;
                self.terms.push(entry);
                bucket.push(id);
            }
        }
        Ok(())
    }
}
