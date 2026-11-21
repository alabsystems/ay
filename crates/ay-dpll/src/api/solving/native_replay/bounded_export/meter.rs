// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::{
    NativeReplayExportBudget, NativeReplayExportError as Error,
    NativeReplayExportResource as Resource,
};

pub(super) type Result<T> = std::result::Result<T, Error>;

pub(super) struct Meter<'a> {
    pub(super) budget: &'a mut NativeReplayExportBudget,
    pub(super) progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

impl Meter<'_> {
    pub(super) fn fail<T>(&mut self, error: Error) -> Result<T> {
        let error = *self.budget.refusal.get_or_insert(error);
        Err(error)
    }

    pub(super) fn poll(&mut self) -> Result<()> {
        self.charge(0, 0)
    }

    pub(super) fn charge(&mut self, work: usize, storage: usize) -> Result<()> {
        if let Some(error) = self.budget.refusal {
            return Err(error);
        }
        let next_work = self.budget.usage.work.saturating_add(work);
        let next_storage = self.budget.usage.storage_bytes.saturating_add(storage);
        if work == usize::MAX
            || work
                > self
                    .budget
                    .limits
                    .max_work
                    .saturating_sub(self.budget.usage.work)
        {
            return self.fail(Error::Limit {
                resource: Resource::Work,
                limit: self.budget.limits.max_work,
                requested: next_work,
            });
        }
        if storage == usize::MAX
            || storage
                > self
                    .budget
                    .limits
                    .max_storage_bytes
                    .saturating_sub(self.budget.usage.storage_bytes)
        {
            return self.fail(Error::Limit {
                resource: Resource::Storage,
                limit: self.budget.limits.max_storage_bytes,
                requested: next_storage,
            });
        }
        // Latch before invoking caller code. A caught callback panic cannot
        // turn this same budget into a fresh, uncancelled attempt.
        self.budget.refusal = Some(Error::Cancelled);
        if !(self.progress)(work, storage) {
            return Err(Error::Cancelled);
        }
        self.budget.refusal = None;
        self.budget.usage.work = next_work;
        self.budget.usage.storage_bytes = next_storage;
        Ok(())
    }

    pub(super) fn depth(&mut self, depth: usize) -> Result<()> {
        self.charge(1, 0)?;
        if depth > self.budget.limits.max_depth {
            return self.fail(Error::Limit {
                resource: Resource::Depth,
                limit: self.budget.limits.max_depth,
                requested: depth,
            });
        }
        Ok(())
    }

    pub(super) fn output(&mut self, bytes: usize) -> Result<()> {
        let next = self.budget.usage.output_bytes.saturating_add(bytes);
        if bytes
            > self
                .budget
                .limits
                .max_output_bytes
                .saturating_sub(self.budget.usage.output_bytes)
        {
            return self.fail(Error::Limit {
                resource: Resource::Output,
                limit: self.budget.limits.max_output_bytes,
                requested: next,
            });
        }
        self.charge(bytes, 0)?;
        self.budget.usage.output_bytes = next;
        Ok(())
    }

    /// Charge a complete new capacity before asking the allocator for it.
    /// Historical charges are retained when a collection grows or is dropped.
    pub(super) fn reserve<T>(&mut self, values: &mut Vec<T>, additional: usize) -> Result<()> {
        let needed = match values.len().checked_add(additional) {
            Some(needed) => needed,
            None => return self.fail(Error::Allocation),
        };
        if needed <= values.capacity() {
            return Ok(());
        }
        let capacity = needed.max(values.capacity().saturating_mul(2)).max(4);
        let bytes = match capacity.checked_mul(size_of::<T>()) {
            Some(bytes) => bytes,
            None => return self.fail(Error::Allocation),
        };
        self.charge(values.len().saturating_mul(size_of::<T>()), bytes)?;
        if values.try_reserve_exact(capacity - values.len()).is_err() {
            return self.fail(Error::Allocation);
        }
        Ok(())
    }

    pub(super) fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> Result<()> {
        self.charge(1, 0)?;
        self.reserve(values, 1)?;
        values.push(value);
        Ok(())
    }
}

/// Charge hash/probe/key-comparison work before a borrowed membership lookup.
pub(super) fn constructor_lookup(
    context: &ay_frontend::Context,
    name: &str,
    meter: &mut Meter<'_>,
) -> Result<()> {
    meter.charge(
        context
            .native_input_constructor_storage_capacity()
            .saturating_mul(2)
            .saturating_add(8)
            .saturating_mul(name.len().saturating_add(1)),
        0,
    )
}

/// Bound the small family of named-sort/catalogue lookups, including misses.
pub(super) fn sort_lookup(
    context: &ay_frontend::Context,
    name: &str,
    meter: &mut Meter<'_>,
) -> Result<()> {
    meter.charge(
        context
            .native_input_sort_storage_capacity()
            .saturating_mul(2)
            .saturating_add(32)
            .saturating_mul(name.len().saturating_add(1)),
        0,
    )
}
