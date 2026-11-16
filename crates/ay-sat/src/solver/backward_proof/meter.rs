// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing reconstruction counts with cancellation-only inner checkpoints.

use super::cancellation::Cancellation;
use super::{BackwardProofFailure, BackwardProofLimits, BackwardProofResource, LratStep};
use ay_core::time::Instant;
use std::{collections::HashSet, hash::Hash, mem::size_of};

pub(super) struct BackwardProofMeter<'a> {
    pub(super) limits: &'a BackwardProofLimits,
    pub(super) bytes: usize,
    pub(super) steps: usize,
    pub(super) literals: usize,
    pub(super) hints: usize,
    pub(super) work: u64,
    control: Cancellation<'a>,
}

impl<'a> BackwardProofMeter<'a> {
    #[cfg(test)]
    pub(super) fn new(limits: &'a BackwardProofLimits) -> Result<Self, BackwardProofFailure> {
        Self::with_cancellation(limits, &|| true)
    }

    pub(super) fn with_cancellation(
        limits: &'a BackwardProofLimits,
        keep_going: &'a dyn Fn() -> bool,
    ) -> Result<Self, BackwardProofFailure> {
        let meter = Self {
            limits,
            bytes: 0,
            steps: 0,
            literals: 0,
            hints: 0,
            work: 0,
            control: Cancellation::new(keep_going),
        };
        meter.check_deadline()?;
        Ok(meter)
    }

    pub(super) fn check_deadline(&self) -> Result<(), BackwardProofFailure> {
        self.control.check_latched()?;
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BackwardProofFailure::Deadline);
        }
        self.poll()?;
        // An accepting callback can consume the remaining original deadline.
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BackwardProofFailure::Deadline);
        }
        Ok(())
    }

    pub(super) fn poll(&self) -> Result<(), BackwardProofFailure> {
        self.control.poll()
    }

    pub(super) fn tick(&mut self) -> Result<(), BackwardProofFailure> {
        self.work = self
            .work
            .checked_add(1)
            .ok_or(BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Bytes,
            })?;
        if self.work.is_multiple_of(1024) {
            self.check_deadline()
        } else {
            self.poll()
        }
    }

    fn add_count(
        current: &mut usize,
        additional: usize,
        limit: usize,
        resource: BackwardProofResource,
    ) -> Result<(), BackwardProofFailure> {
        let actual = current
            .checked_add(additional)
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        if actual > limit {
            return Err(BackwardProofFailure::Limit {
                resource,
                limit,
                actual,
            });
        }
        *current = actual;
        Ok(())
    }

    pub(super) fn add_step(&mut self) -> Result<(), BackwardProofFailure> {
        Self::add_count(
            &mut self.steps,
            1,
            self.limits.max_steps,
            BackwardProofResource::Steps,
        )
    }

    pub(super) fn add_literals(&mut self, count: usize) -> Result<(), BackwardProofFailure> {
        Self::add_count(
            &mut self.literals,
            count,
            self.limits.max_literals,
            BackwardProofResource::Literals,
        )
    }

    pub(super) fn add_hint(&mut self) -> Result<(), BackwardProofFailure> {
        Self::add_count(
            &mut self.hints,
            1,
            self.limits.max_hints,
            BackwardProofResource::Hints,
        )
    }

    pub(super) fn reserve_to<T>(
        &mut self,
        vec: &mut Vec<T>,
        target: usize,
        resource: BackwardProofResource,
    ) -> Result<(), BackwardProofFailure> {
        let old_capacity = vec.capacity();
        if target <= old_capacity {
            return self.poll();
        }
        let requested_delta = target
            .checked_sub(old_capacity)
            .and_then(|delta| delta.checked_mul(size_of::<T>()))
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        let requested = self.bytes.checked_add(requested_delta).ok_or(
            BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Bytes,
            },
        )?;
        if requested > self.limits.max_bytes {
            return Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Bytes,
                limit: self.limits.max_bytes,
                actual: requested,
            });
        }
        self.poll()?;
        vec.try_reserve_exact(target - vec.len())
            .map_err(|_| BackwardProofFailure::Allocation { resource })?;
        self.check_deadline()?;
        let actual_delta = vec
            .capacity()
            .checked_sub(old_capacity)
            .and_then(|delta| delta.checked_mul(size_of::<T>()))
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        let actual = self.bytes.checked_add(actual_delta).ok_or(
            BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Bytes,
            },
        )?;
        if actual > self.limits.max_bytes {
            drop(std::mem::take(vec));
            return Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Bytes,
                limit: self.limits.max_bytes,
                actual,
            });
        }
        self.bytes = actual;
        Ok(())
    }

    pub(super) fn push<T>(
        &mut self,
        vec: &mut Vec<T>,
        value: T,
        resource: BackwardProofResource,
    ) -> Result<(), BackwardProofFailure> {
        let required = vec
            .len()
            .checked_add(1)
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        if required > vec.capacity() {
            let target = if vec.capacity() == 0 {
                4
            } else {
                vec.capacity().saturating_mul(2)
            }
            .max(required);
            self.reserve_to(vec, target, resource)?;
        }
        self.poll()?;
        vec.push(value);
        Ok(())
    }

    pub(super) fn insert_hash_set<T: Eq + Hash>(
        &mut self,
        seen: &mut HashSet<T>,
        value: T,
        resource: BackwardProofResource,
    ) -> Result<bool, BackwardProofFailure> {
        self.poll()?;
        if seen.contains(&value) {
            return Ok(false);
        }
        if seen.len() == seen.capacity() {
            let required = seen
                .len()
                .checked_add(1)
                .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
            let target = if seen.capacity() == 0 {
                4
            } else {
                seen.capacity().saturating_mul(2)
            }
            .max(required);
            let requested_delta = target
                .checked_sub(seen.capacity())
                .and_then(|delta| delta.checked_mul(32))
                .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
            let requested = self.bytes.checked_add(requested_delta).ok_or(
                BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Bytes,
                },
            )?;
            if requested > self.limits.max_bytes {
                return Err(BackwardProofFailure::Limit {
                    resource: BackwardProofResource::Bytes,
                    limit: self.limits.max_bytes,
                    actual: requested,
                });
            }
            let old_capacity = seen.capacity();
            self.poll()?;
            seen.try_reserve(target - seen.len())
                .map_err(|_| BackwardProofFailure::Allocation { resource })?;
            self.check_deadline()?;
            let actual_delta = seen
                .capacity()
                .checked_sub(old_capacity)
                .and_then(|delta| delta.checked_mul(32))
                .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
            let actual = self.bytes.checked_add(actual_delta).ok_or(
                BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Bytes,
                },
            )?;
            if actual > self.limits.max_bytes {
                drop(std::mem::take(seen));
                return Err(BackwardProofFailure::Limit {
                    resource: BackwardProofResource::Bytes,
                    limit: self.limits.max_bytes,
                    actual,
                });
            }
            self.bytes = actual;
        }
        self.poll()?;
        Ok(seen.insert(value))
    }

    pub(super) fn insert_seen(
        &mut self,
        seen: &mut HashSet<i64>,
        value: i64,
    ) -> Result<bool, BackwardProofFailure> {
        self.insert_hash_set(seen, value, BackwardProofResource::Hints)
    }

    pub(super) fn clone_slice<T: Clone>(
        &mut self,
        slice: &[T],
        resource: BackwardProofResource,
    ) -> Result<Vec<T>, BackwardProofFailure> {
        let mut result = Vec::new();
        self.reserve_to(&mut result, slice.len(), resource)?;
        for value in slice {
            self.poll()?;
            result.push(value.clone());
        }
        Ok(result)
    }

    pub(super) fn sort_steps_by_clause_id(
        &mut self,
        steps: &mut [LratStep],
    ) -> Result<(), BackwardProofFailure> {
        let len = steps.len();
        if len < 2 {
            return self.check_deadline();
        }
        for start in (0..(len / 2)).rev() {
            self.sift_steps_down(steps, start, len)?;
        }
        for end in (1..len).rev() {
            self.tick()?;
            steps.swap(0, end);
            self.sift_steps_down(steps, 0, end)?;
        }
        self.check_deadline()
    }

    fn sift_steps_down(
        &mut self,
        steps: &mut [LratStep],
        mut root: usize,
        end: usize,
    ) -> Result<(), BackwardProofFailure> {
        loop {
            self.tick()?;
            let Some(mut child) = root.checked_mul(2).and_then(|value| value.checked_add(1)) else {
                return Err(BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Steps,
                });
            };
            if child >= end {
                return Ok(());
            }
            if child + 1 < end && steps[child].clause_id < steps[child + 1].clause_id {
                child += 1;
            }
            if steps[root].clause_id >= steps[child].clause_id {
                return Ok(());
            }
            steps.swap(root, child);
            root = child;
        }
    }
}
