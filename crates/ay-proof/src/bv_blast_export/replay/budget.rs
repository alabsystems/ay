// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Polls between two clock reads of `limits.deadline`.
///
/// The replay polls at every literal edge, so consecutive polls are a set
/// insert or a comparison apart, and reading the clock at each of them was
/// most of a long replay's time: sampled 2026-10-09 on corpus9 0644's strict
/// run, `Instant::now` under `clauses::validate`, `sets::clause_eq` and
/// `validate_cnf` took 24% of the process's samples. Read every 256th poll, a
/// passed deadline is still seen within microseconds. The cancellation
/// callback is still asked at every poll, and the admission polls
/// ([`ReplayBudget::poll_admission`]) always read the clock.
const CLOCK_STRIDE: u32 = 256;

pub(super) struct ReplayBudget<'a, 'p> {
    pub(super) limits: &'a BvBlastValidateLimits,
    work: u64,
    keep_going: &'p mut dyn FnMut() -> bool,
    refused: bool,
    /// When [`Self::poll`] reads the clock.
    clock: ay_core::time::ClockStride,
}

impl<'a, 'p> ReplayBudget<'a, 'p> {
    pub(super) fn new(
        limits: &'a BvBlastValidateLimits,
        keep_going: &'p mut dyn FnMut() -> bool,
    ) -> Self {
        Self {
            limits,
            work: 0,
            keep_going,
            refused: false,
            clock: ay_core::time::ClockStride::new(CLOCK_STRIDE),
        }
    }

    /// A poll inside the replay: the callback every time, the clock on the
    /// first of every [`CLOCK_STRIDE`] polls.
    pub(super) fn poll(&mut self) -> Result<(), BvBlastValidateError> {
        let clocked = self.clock.due();
        self.poll_with_clock(clocked)
    }

    /// A poll that admits the replay or its result: it reads the clock.
    pub(super) fn poll_admission(&mut self) -> Result<(), BvBlastValidateError> {
        self.poll_with_clock(true)
    }

    fn poll_with_clock(&mut self, clocked: bool) -> Result<(), BvBlastValidateError> {
        if self.refused {
            return Err(BvBlastValidateError::Cancelled);
        }
        if clocked && self.deadline_passed() {
            return Err(BvBlastValidateError::DeadlineExceeded);
        }
        // A callback panic caught by an inner consumer cannot re-enable this
        // attempt. Only a normal true return clears the pre-latched refusal.
        self.refused = true;
        if !(self.keep_going)() {
            return Err(BvBlastValidateError::Cancelled);
        }
        self.refused = false;
        if clocked && self.deadline_passed() {
            return Err(BvBlastValidateError::DeadlineExceeded);
        }
        Ok(())
    }

    fn deadline_passed(&self) -> bool {
        self.limits
            .deadline
            .is_some_and(|end| Instant::now() >= end)
    }

    pub(super) fn count(
        &self,
        resource: &'static str,
        actual: usize,
        limit: usize,
    ) -> Result<(), BvBlastValidateError> {
        if actual <= limit {
            Ok(())
        } else {
            Err(BvBlastValidateError::ResourceLimit {
                resource,
                limit: u64::try_from(limit).unwrap_or(u64::MAX),
                actual: u64::try_from(actual).unwrap_or(u64::MAX),
            })
        }
    }

    pub(super) fn add_work(&mut self, units: usize) -> Result<(), BvBlastValidateError> {
        let Some(work) = u64::try_from(units)
            .ok()
            .and_then(|units| self.work.checked_add(units))
        else {
            self.refused = true;
            return Err(BvBlastValidateError::WorkOverflow);
        };
        self.work = work;
        if self.work > self.limits.max_work {
            return Err(BvBlastValidateError::ResourceLimit {
                resource: "validation work",
                limit: self.limits.max_work,
                actual: self.work,
            });
        }
        self.poll()
    }

    pub(super) fn work(&self) -> u64 {
        self.work
    }
}
