// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{ChcQueryPlaybackError as Error, Result};
use ay_core::time::Instant;

#[derive(Clone, Copy)]
enum Stop {
    Cancelled,
    Deadline,
}

/// One original absolute endpoint and a sticky caller-owned progress callback.
///
/// Reuse this control across all rows, unfolding passes and V2 projection. No
/// operation renews its deadline. The callback may debit an existing external
/// owner; polls are cooperative observations, not an allocation cost model.
pub struct ChcQueryPlaybackControl<'a> {
    deadline: Instant,
    progress: &'a mut dyn FnMut() -> bool,
    stopped: Option<Stop>,
    pub(crate) owner: std::sync::Arc<()>,
}

impl<'a> ChcQueryPlaybackControl<'a> {
    pub fn new(deadline: Instant, progress: &'a mut dyn FnMut() -> bool) -> Result<Self> {
        let mut control = Self {
            deadline,
            progress,
            stopped: None,
            owner: std::sync::Arc::new(()),
        };
        control.poll()?;
        Ok(control)
    }

    pub(crate) fn require_owner(&self, owner: &std::sync::Arc<()>) -> Result<()> {
        if !std::sync::Arc::ptr_eq(&self.owner, owner) {
            return Err(Error::ForeignControl);
        }
        Ok(())
    }

    pub(crate) fn poll(&mut self) -> Result<()> {
        if let Some(stop) = self.stopped {
            return Err(match stop {
                Stop::Cancelled => Error::Cancelled,
                Stop::Deadline => Error::DeadlineExceeded,
            });
        }
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Deadline);
            return Err(Error::DeadlineExceeded);
        }
        // Pre-latch before calling arbitrary caller code; catching its panic
        // cannot resume this same invocation with a renewed callback grant.
        self.stopped = Some(Stop::Cancelled);
        if !(self.progress)() {
            return Err(Error::Cancelled);
        }
        self.stopped = None;
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Deadline);
            return Err(Error::DeadlineExceeded);
        }
        Ok(())
    }

    pub(super) fn finish<T>(&mut self, result: Result<T>) -> Result<T> {
        match result {
            Ok(value) => match self.poll() {
                Ok(()) => Ok(value),
                Err(error) => {
                    drop(value);
                    Err(error)
                }
            },
            Err(error) => {
                self.poll()?;
                Err(error)
            }
        }
    }

    pub(super) fn reserve<T>(
        &mut self,
        values: &mut Vec<T>,
        additional: usize,
        limit: usize,
    ) -> Result<()> {
        self.poll()?;
        let len = values
            .len()
            .checked_add(additional)
            .ok_or(Error::LimitExceeded)?;
        if len > limit {
            return Err(Error::LimitExceeded);
        }
        values
            .try_reserve_exact(additional)
            .map_err(|_| Error::AllocationFailed)?;
        self.poll()
    }

    pub(super) fn push<T>(&mut self, values: &mut Vec<T>, value: T, limit: usize) -> Result<()> {
        self.poll()?;
        if values.len() >= limit {
            return Err(Error::LimitExceeded);
        }
        if values.len() == values.capacity() {
            let growth = values.len().max(4).min(limit - values.len());
            self.reserve(values, growth, limit)?;
        }
        values.push(value);
        Ok(())
    }
}
