// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One cumulative scope for admission, distribution, rewriting and export.

use ay_core::resource::{current_check_stop, current_guard, CheckStop, Guard};

#[derive(Clone, Copy)]
pub(super) struct Limits {
    pub(super) work: usize,
    pub(super) growth: usize,
    pub(super) nodes: usize,
    pub(super) branches: usize,
    pub(super) depth: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            work: 2_000_000,
            growth: 8 * 1024 * 1024,
            nodes: 65_536,
            branches: 64,
            depth: 128,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Failure {
    Declined,
    Stopped,
}

pub(super) struct Scope<'a> {
    pub(super) remaining: Limits,
    open: &'a dyn Fn() -> bool,
    original: Option<CheckStop>,
    guard: Option<Guard>,
    stopped: bool,
}

impl<'a> Scope<'a> {
    pub(super) fn new(limits: Limits, open: &'a dyn Fn() -> bool) -> Self {
        let original = current_check_stop();
        Self {
            remaining: limits,
            open,
            guard: current_guard(),
            stopped: original.is_err(),
            original: original.ok().flatten(),
        }
    }

    pub(super) fn poll(&mut self) -> Result<(), Failure> {
        if self.stopped {
            return Err(Failure::Stopped);
        }
        // A panicking foreign owner must not leave reusable projection credit.
        self.stopped = true;
        if self.original.as_ref().is_some_and(|stop| stop())
            || self
                .guard
                .as_ref()
                .is_some_and(|guard| guard.poll().is_some())
            || ay_core::resource::process_cancelled()
            || !(self.open)()
        {
            return Err(Failure::Stopped);
        }
        self.stopped = false;
        Ok(())
    }

    pub(super) fn work(&mut self, count: usize) -> Result<(), Failure> {
        self.poll()?;
        self.remaining.work = self.remaining.work.checked_sub(count).ok_or_else(|| {
            self.stopped = true;
            Failure::Stopped
        })?;
        // The local algorithm ceiling is not a fresh caller allowance. Every
        // accepted debit also reaches the original Guard and its ancestors,
        // even if a nested operation has replaced the thread-local scope.
        if let Some(guard) = &self.guard {
            if u64::try_from(count)
                .ok()
                .and_then(|cost| guard.tick(cost).ok())
                .is_none()
            {
                self.stopped = true;
                return Err(Failure::Stopped);
            }
        }
        Ok(())
    }

    /// Charge a cumulative logical-storage ledger before allocation, including
    /// name bytes; freed scratch is not refunded. The factor of two allows for
    /// ordinary growth, but this is not an allocator-accurate heap or RSS cap:
    /// allocator capacity minima, metadata and Arc headers are not measured.
    /// Work/node/depth limits and the ambient memory stop apply independently.
    pub(super) fn grow<T>(&mut self, count: usize) -> Result<(), Failure> {
        self.work(1)?;
        let amount = count
            .checked_mul(std::mem::size_of::<T>())
            .and_then(|n| n.checked_mul(2));
        self.remaining.growth = amount
            .and_then(|n| self.remaining.growth.checked_sub(n))
            .ok_or_else(|| {
                self.stopped = true;
                Failure::Stopped
            })?;
        Ok(())
    }

    pub(super) fn node(&mut self) -> Result<(), Failure> {
        self.work(1)?;
        self.remaining.nodes = self.remaining.nodes.checked_sub(1).ok_or_else(|| {
            self.stopped = true;
            Failure::Stopped
        })?;
        Ok(())
    }

    pub(super) fn branch(&mut self, count: usize) -> Result<(), Failure> {
        self.work(count)?;
        self.remaining.branches = self.remaining.branches.checked_sub(count).ok_or_else(|| {
            self.stopped = true;
            Failure::Stopped
        })?;
        Ok(())
    }

    pub(super) fn depth(&mut self, depth: usize) -> Result<(), Failure> {
        self.work(1)?;
        if depth > self.remaining.depth {
            self.stopped = true;
            return Err(Failure::Stopped);
        }
        Ok(())
    }
}
