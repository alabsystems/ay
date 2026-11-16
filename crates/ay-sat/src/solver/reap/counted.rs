// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission for the actual radix queue. A pop can grow several destination
//! buckets; its minimum scan and redistribution are a single paid transaction.

use super::Reap;
use crate::counted_storage::{try_reserve, Result};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};

impl Reap {
    pub(in crate::solver) fn push_counted(
        &mut self,
        value: u32,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(8, 0)?;
        if value < self.last_deleted || self.num_elements == usize::MAX {
            return Err(invalid(owner));
        }
        let index = (32 - (value ^ self.last_deleted).leading_zeros()) as usize;
        try_reserve(owner, &mut self.buckets[index], 1)?;
        owner.check()?;
        self.push(value);
        owner.check()
    }

    pub(in crate::solver) fn pop_counted(&mut self, owner: &CountedAdmission) -> Result<u32> {
        // Includes the unchanged kernel's bounded metadata scan, final update,
        // and eventual queue clearing. Planning storage is fixed, not a Vec.
        owner.admit(192, size_of::<[usize; 33]>())?;
        if self.num_elements == 0 || self.min_bucket > 32 || self.max_bucket > 32 {
            return Err(invalid(owner));
        }
        let index = (self.min_bucket as usize..=32)
            .find(|&i| !self.buckets[i].is_empty())
            .ok_or_else(|| invalid(owner))?;
        if index > self.max_bucket as usize {
            return Err(invalid(owner));
        }
        if index > 0 {
            self.reserve_redistribution(index, owner)?;
        } else {
            owner.admit(self.buckets[0].len(), 0)?;
            if self.buckets[0]
                .iter()
                .any(|&value| value != self.last_deleted)
            {
                return Err(invalid(owner));
            }
        }
        owner.check()?;
        let value = self.pop();
        owner.check()?;
        Ok(value)
    }

    fn reserve_redistribution(&mut self, index: usize, owner: &CountedAdmission) -> Result<()> {
        let source = &self.buckets[index];
        let mut minimum = u32::MAX;
        let mut minimum_index = 0;
        // Same strict comparison and first-minimum tie choice as ordinary pop.
        for (position, &value) in source.iter().enumerate() {
            owner.admit(2, 0)?;
            if value < minimum {
                minimum = value;
                minimum_index = position;
            }
        }
        if minimum < self.last_deleted {
            return Err(invalid(owner));
        }
        let mut destinations = [0usize; 33];
        for (position, &value) in source.iter().enumerate() {
            // Planning visit, unchanged kernel visit, and push/cleanup.
            owner.admit(5, 0)?;
            if position == minimum_index {
                continue;
            }
            let target = (32 - (value ^ minimum).leading_zeros()) as usize;
            if target >= index {
                return Err(invalid(owner));
            }
            destinations[target] = destinations[target]
                .checked_add(1)
                .ok_or_else(|| invalid(owner))?;
        }
        for (bucket, additional) in self.buckets.iter_mut().zip(destinations) {
            owner.admit(1, 0)?;
            if additional > 0 {
                try_reserve(owner, bucket, additional)?;
            }
        }
        Ok(())
    }
}

fn invalid(owner: &CountedAdmission) -> CountedAdmissionError {
    owner.refuse(CountedAdmissionError::Original(
        QueryError::Invalid("invalid counted shrink radix queue").into(),
    ))
}

#[cfg(test)]
mod tests;
