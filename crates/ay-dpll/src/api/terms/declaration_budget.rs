// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One cumulative owner for native declaration input, copies and commit polling.

use crate::api::{
    NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationRefusal as Refusal,
};
use ay_core::time::Instant;
use std::mem::size_of;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

pub(super) struct Meter<'a> {
    pub(super) budget: &'a mut Budget,
    pub(super) progress: &'a mut dyn FnMut(usize, usize) -> bool,
    pub(super) interrupt: Arc<AtomicBool>,
    pub(super) deadline: Option<Instant>,
}

impl Meter<'_> {
    pub(super) fn fail<T>(&mut self, refusal: Refusal) -> Result<T, Error> {
        let refusal = *self.budget.refusal.get_or_insert(refusal);
        Err(refusal.into())
    }
    pub(super) fn pay(&mut self, work: usize, storage: usize, depth: usize) -> Result<(), Error> {
        if let Some(refusal) = self.budget.refusal {
            return Err(refusal.into());
        }
        if work == usize::MAX
            || work
                > self
                    .budget
                    .limits
                    .work
                    .saturating_sub(self.budget.usage.work)
        {
            return self.fail(Refusal::Work {
                limit: self.budget.limits.work,
                requested: self.budget.usage.work.saturating_add(work),
            });
        }
        if storage == usize::MAX
            || storage
                > self
                    .budget
                    .limits
                    .storage
                    .saturating_sub(self.budget.usage.storage_bytes)
        {
            return self.fail(Refusal::Storage {
                limit: self.budget.limits.storage,
                requested: self.budget.usage.storage_bytes.saturating_add(storage),
            });
        }
        if depth > self.budget.limits.depth.min(128) {
            return self.fail(Refusal::Depth {
                limit: self.budget.limits.depth.min(128),
                requested: depth,
            });
        }
        // Sticky before caller code: catching a callback panic cannot renew it.
        self.budget.refusal = Some(Refusal::Cancelled);
        if !(self.progress)(work, storage)
            || ay_core::resource::check_stop_requested()
            || self.interrupt.load(Ordering::Relaxed)
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(Refusal::Cancelled.into());
        }
        self.budget.refusal = None;
        self.budget.usage.work += work;
        self.budget.usage.storage_bytes += storage;
        Ok(())
    }
    pub(super) fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> Result<(), Error> {
        if values.len() == values.capacity() {
            let capacity = values.capacity().saturating_mul(2).max(4);
            self.pay(values.len(), capacity.saturating_mul(size_of::<T>()), 0)?;
            if values.try_reserve_exact(capacity - values.len()).is_err() {
                return self.fail(Refusal::Allocation);
            }
        }
        values.push(value);
        Ok(())
    }
    pub(super) fn text(&mut self, name: &str) -> Result<(), Error> {
        self.pay(name.len().saturating_add(1), name.len(), 0)
    }
}
