// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Radix-based priority queue for monotone-pop sequences.
//!
//! Port of CaDiCaL's `reap.hpp`/`reap.cpp`. Elements are unsigned integers
//! popped in increasing order. Uses XOR-based bucket assignment:
//! `bucket = 32 - clz(element ^ last_popped)`. Amortized O(1) push/pop.
//!
//! Used by clause shrinking to find the next shrinkable literal without
//! linear trail scanning.

/// Radix priority queue with monotone-increasing pop order.
#[derive(Clone)]
pub(crate) struct Reap {
    num_elements: usize,
    last_deleted: u32,
    min_bucket: u32,
    max_bucket: u32,
    buckets: [Vec<u32>; 33],
}

impl Reap {
    /// Create a new empty Reap.
    pub(crate) fn new() -> Self {
        Self {
            num_elements: 0,
            last_deleted: 0,
            min_bucket: 32,
            max_bucket: 0,
            buckets: std::array::from_fn(|_| Vec::new()),
        }
    }

    /// Push an element. Must be >= last_deleted (monotone invariant).
    #[inline]
    pub(crate) fn push(&mut self, e: u32) {
        debug_assert!(
            self.last_deleted <= e,
            "Reap::push({e}) < last_deleted({})",
            self.last_deleted
        );
        let diff = e ^ self.last_deleted;
        let bucket = 32 - diff.leading_zeros(); // 0..=32
        self.buckets[bucket as usize].push(e);
        if self.min_bucket > bucket {
            self.min_bucket = bucket;
        }
        if self.max_bucket < bucket {
            self.max_bucket = bucket;
        }
        self.num_elements += 1;
    }

    /// Pop the smallest element. Amortized O(1).
    ///
    /// CaDiCaL reap.cpp:46-117: in-place redistribution avoids allocation.
    #[inline]
    pub(crate) fn pop(&mut self) -> u32 {
        debug_assert!(self.num_elements > 0, "Reap::pop() on empty queue");
        let mut i = self.min_bucket;
        loop {
            debug_assert!(i < 33);
            debug_assert!(i <= self.max_bucket);
            let bucket = &self.buckets[i as usize];
            if bucket.is_empty() {
                i += 1;
                self.min_bucket = i;
                continue;
            }

            let res;
            if i > 0 {
                // Non-zero bucket: find minimum, redistribute rest.
                // CaDiCaL reap.cpp:58-83: iterate in-place, push non-min
                // elements to lower buckets, then clear source bucket.
                // No temporary Vec allocation needed.
                let s = &self.buckets[i as usize];
                let mut min_val = u32::MAX;
                let mut min_idx = 0;
                for (idx, &val) in s.iter().enumerate() {
                    if val < min_val {
                        min_val = val;
                        min_idx = idx;
                    }
                }
                res = min_val;

                // Redistribute non-minimum elements to lower buckets
                // (relative to the new last_deleted = res).
                // Iterate the source bucket in-place: push each non-min
                // element directly to its target bucket before clearing.
                let bucket_len = self.buckets[i as usize].len();
                for k in 0..bucket_len {
                    if k == min_idx {
                        continue;
                    }
                    let other = self.buckets[i as usize][k];
                    let diff = other ^ res;
                    let j = 32 - diff.leading_zeros();
                    debug_assert!(j < i);
                    self.buckets[j as usize].push(other);
                    if self.min_bucket > j {
                        self.min_bucket = j;
                    }
                }

                self.buckets[i as usize].clear();

                // Update max_bucket if we emptied the top bucket
                if self.max_bucket == i {
                    self.max_bucket = i.saturating_sub(1);
                }
            } else {
                // Bucket 0: exact match — O(1) pop
                res = self.last_deleted;
                debug_assert!(!self.buckets[0].is_empty());
                debug_assert_eq!(self.buckets[0][0], res);
                self.buckets[0].pop();
            }

            // Update min_bucket if current bucket is now empty
            if self.min_bucket == i && self.buckets[i as usize].is_empty() {
                self.min_bucket = (i + 1).min(32);
            }

            self.num_elements -= 1;
            debug_assert!(self.last_deleted <= res);
            self.last_deleted = res;
            return res;
        }
    }

    /// Clear all elements and reset state.
    pub(crate) fn clear(&mut self) {
        for bucket in &mut self.buckets {
            bucket.clear();
        }
        self.num_elements = 0;
        self.last_deleted = 0;
        self.min_bucket = 32;
        self.max_bucket = 0;
    }

    /// Check if the queue is empty.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.num_elements == 0
    }
}

#[cfg(test)]
#[path = "reap_tests.rs"]
mod tests;
