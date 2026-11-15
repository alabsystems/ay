// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::ReplayCancellation;
use crate::transform::array_ghost_pairs::source_premises::SourceControl;
use std::cell::Cell;

const MAX_WORK: usize = 8_000_000;
const MAX_BYTES: usize = 64 * 1024 * 1024;
pub(super) const MAX_OBLIGATIONS: usize = 4_096;

pub(super) struct Control<'p> {
    deadline: Instant,
    cancellation: ReplayCancellation,
    stopped: Cell<bool>,
    work: Cell<usize>,
    bytes: Cell<usize>,
    parent: Option<&'p SourceControl<'p>>,
    #[cfg(test)]
    pub(super) calls: Cell<usize>,
    #[cfg(test)]
    pub(super) stop_at: Cell<Option<usize>>,
}

impl<'p> Control<'p> {
    pub(super) fn new(deadline: Instant, cancellation: &CancellationToken) -> Self {
        Self {
            deadline,
            cancellation: ReplayCancellation::new(cancellation),
            stopped: Cell::new(false),
            work: Cell::new(MAX_WORK),
            bytes: Cell::new(MAX_BYTES),
            parent: None,
            #[cfg(test)]
            calls: Cell::new(0),
            #[cfg(test)]
            stop_at: Cell::new(None),
        }
    }

    /// Borrow the live attempt ledger; local counters can only tighten it.
    /// No snapshot, reservation, renewed deadline or copied value is created.
    pub(super) fn with_source(
        deadline: Instant,
        cancellation: &CancellationToken,
        parent: &'p SourceControl<'p>,
    ) -> Self {
        let mut control = Self::new(deadline, cancellation);
        control.parent = Some(parent);
        control
    }

    pub(super) fn poll(&self) -> ChcResult<()> {
        if self.parent.is_some_and(|parent| parent.poll().is_none()) {
            return self.refuse("parent attempt refusal");
        }
        if self.stopped.get()
            || self.cancellation.is_cancelled()
            || Instant::now() >= self.deadline
            || ay_core::TermStore::global_memory_exceeded()
        {
            return self.refuse("deadline, cancellation or prior resource refusal");
        }
        #[cfg(test)]
        {
            let next = self.calls.get() + 1;
            self.calls.set(next);
            if self.stop_at.get() == Some(next) {
                return self.refuse("injected cancellation");
            }
        }
        Ok(())
    }

    pub(super) fn charge(&self, work: usize, bytes: usize) -> ChcResult<()> {
        self.poll()?;
        if self
            .parent
            .is_some_and(|parent| parent.debit(work, bytes).is_none())
        {
            return self.refuse("parent aggregate work/copy limit");
        }
        let (Some(work), Some(bytes)) = (
            self.work.get().checked_sub(work),
            self.bytes.get().checked_sub(bytes),
        ) else {
            return self.refuse("aggregate work/copy/output limit");
        };
        self.work.set(work);
        self.bytes.set(bytes);
        Ok(())
    }

    pub(super) fn refuse<T>(&self, reason: &str) -> ChcResult<T> {
        self.stopped.set(true);
        if let Some(parent) = self.parent {
            parent.stop();
        }
        Err(invalid(reason))
    }

    #[cfg(test)]
    pub(super) fn with_limits(token: &CancellationToken, work: usize, bytes: usize) -> Self {
        let result = Self::new(Instant::now() + Duration::from_secs(60), token);
        result.work.set(work);
        result.bytes.set(bytes);
        result
    }

    #[cfg(test)]
    pub(super) fn bytes_used(&self) -> usize {
        MAX_BYTES - self.bytes.get()
    }
}

#[cfg(test)]
mod tests;
