// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reserve counted BCP storage before any watch transaction is destructive.

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

type Result<T> = std::result::Result<T, CountedAdmissionError>;

#[cfg(test)]
mod learning_tests;

pub(crate) fn reserve_vec<T>(
    values: &mut Vec<T>,
    required: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    if required <= values.capacity() {
        return Ok(());
    }
    // Keep geometric growth: reserving exactly one more trail element at each
    // propagation would turn a linear implication chain into quadratic copies.
    // The existing unified-watch growth policy caps large allocation steps.
    let capacity = values.capacity();
    let grown = if capacity < WATCH_BUF_LARGE_ENTRIES {
        capacity.checked_mul(2)
    } else {
        capacity.checked_add(capacity / WATCH_BUF_GROWTH_STEP_DIVISOR)
    }
    .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let target = required.max(grown).max(4);
    let work = target
        .checked_add(values.len())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    let bytes = target
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    // Charge the new logical allocation and the possible existing-value copy.
    // Allocator-internal metadata/RSS is still governed by the memory owner.
    owner.admit(work, bytes)?;
    values
        .try_reserve_exact(target - values.len())
        .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))
}

impl WatchList {
    pub(crate) fn reserve_counted(
        &mut self,
        required: usize,
        owner: &CountedAdmission,
    ) -> Result<()> {
        reserve_vec(&mut self.entries, required, owner)
    }
}

impl WatchedLists {
    /// Prepay the exact two ordinary insertions without relocating regions.
    /// Binary grow inserts shift the long suffix; fast inserts rotate it.
    /// Keeping metadata untouched preserves that algorithm choice and order.
    pub(crate) fn reserve_counted_learned_pair(
        &mut self,
        first: Literal,
        second: Literal,
        owner: &CountedAdmission,
    ) -> Result<()> {
        use crate::decision_trace::counted_decision::invalid;
        owner.admit(16, 0)?;
        if first == second || first.index() >= self.meta.len() || second.index() >= self.meta.len()
        {
            return Err(invalid(owner, "invalid learned watch pair"));
        }
        self.reserve_counted_appends(&[first, second], owner)
    }

    /// Prepay one ordinary conflict-level relocation without changing regions
    /// or adding a watch that the original detached-watch path would omit.
    pub(crate) fn reserve_counted_conflict_move(
        &mut self,
        literal: Literal,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(8, 0)?;
        if literal.index() >= self.meta.len() {
            return Err(crate::decision_trace::counted_decision::invalid(
                owner,
                "invalid conflict watch destination",
            ));
        }
        self.reserve_counted_appends(&[literal], owner)
    }

    // Callers pass distinct destinations; no speculative region movement.
    fn reserve_counted_appends(
        &mut self,
        destinations: &[Literal],
        owner: &CountedAdmission,
    ) -> Result<()> {
        let mut end = self.buf_entries.len();
        let mut capacity = self.buf_entries.capacity();
        for &literal in destinations {
            let old = self.meta[literal.index()];
            if old.len < old.capacity {
                continue;
            }
            let count = (old.len as usize)
                .checked_mul(2)
                .map(|n| n.max(2))
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            let next = end
                .checked_add(count)
                .filter(|n| *n <= u32::MAX as usize)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            owner.admit(count.saturating_add(old.len as usize), 0)?;
            if next > capacity {
                let grown = if capacity < WATCH_BUF_LARGE_ENTRIES {
                    capacity.checked_mul(2)
                } else {
                    capacity.checked_add(capacity / WATCH_BUF_GROWTH_STEP_DIVISOR)
                }
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                capacity = next.max(grown).max(4);
                let bytes = capacity
                    .checked_mul(std::mem::size_of::<u64>())
                    .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                owner.admit(capacity.saturating_add(end), bytes)?;
            }
            end = next;
        }
        if capacity > self.buf_entries.capacity() {
            self.buf_entries
                .try_reserve_exact(capacity - self.buf_entries.len())
                .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        }
        owner.check()
    }

    /// `destinations` contains one entry for each possible move from the
    /// current source watch list, sorted by literal. It is not the whole CNF.
    pub(crate) fn reserve_counted_replacements(
        &mut self,
        destinations: &[Literal],
        owner: &CountedAdmission,
    ) -> Result<()> {
        let mut plans = Vec::new();
        reserve_vec(&mut plans, destinations.len(), owner)?;
        let mut cursor = 0;
        let mut end = self.buf_entries.len();
        while cursor < destinations.len() {
            owner.admit(1, 0)?;
            let literal = destinations[cursor];
            let start = cursor;
            while cursor < destinations.len() && destinations[cursor] == literal {
                owner.admit(1, 0)?;
                cursor += 1;
            }
            let meta = self.meta[literal.index()];
            let required = (meta.len as usize)
                .checked_add(cursor - start)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            if required <= meta.capacity as usize {
                continue;
            }
            let capacity = required
                .checked_next_power_of_two()
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?
                .max(2);
            end = end
                .checked_add(capacity)
                .filter(|end| *end <= u32::MAX as usize)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
            // Copy the old region and initialize the complete new region.
            owner.admit(
                capacity
                    .checked_add(meta.len as usize)
                    .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?,
                0,
            )?;
            plans.push((literal.index(), meta, capacity));
        }
        // At most one unified-buffer relocation, priced by its actual size.
        reserve_vec(&mut self.buf_entries, end, owner)?;
        for (literal, old, capacity) in plans {
            owner.check()?;
            let offset = self.buf_entries.len();
            let begin = old.offset as usize;
            self.buf_entries
                .extend_from_within(begin..begin + old.len as usize);
            self.buf_entries.resize(offset + capacity, 0);
            self.dead_slots += old.capacity as usize;
            self.meta[literal] = WatchMeta {
                offset: offset as u32,
                capacity: capacity as u32,
                ..old
            };
        }
        owner.check()
    }
}
