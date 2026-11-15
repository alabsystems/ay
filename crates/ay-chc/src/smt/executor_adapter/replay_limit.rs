// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One unchanged deadline across opaque checked-SMT replay phases.

use ay_core::time::Instant;

use super::replay_cancellation::ReplayCancellation;

/// Diagnostic identity of the observation that declined this existing limit.
/// This carries no authority and never adds another cancellation sample.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ReplayLimitRefusal {
    OriginalDeadline,
    InheritedCancellation,
}

#[derive(Clone, Copy)]
pub(crate) enum ReplayLimit<'a> {
    Legacy,
    Until(Instant),
    Cancellable {
        deadline: Instant,
        cancellation: &'a ReplayCancellation,
    },
}

impl<'a> ReplayLimit<'a> {
    pub(super) fn deadline(self) -> Option<Instant> {
        match self {
            Self::Legacy => None,
            Self::Until(deadline) | Self::Cancellable { deadline, .. } => Some(deadline),
        }
    }

    pub(crate) fn cancellation(self) -> Option<&'a ReplayCancellation> {
        match self {
            Self::Cancellable { cancellation, .. } => Some(cancellation),
            Self::Legacy | Self::Until(_) => None,
        }
    }

    pub(crate) fn check(self) -> Option<()> {
        self.check_with_clock(&mut Instant::now)
    }

    fn check_with_clock(self, now: &mut impl FnMut() -> Instant) -> Option<()> {
        self.check_diagnostic_with_clock(now).ok()
    }

    pub(super) fn check_diagnostic(self) -> Result<(), ReplayLimitRefusal> {
        self.check_diagnostic_with_clock(&mut Instant::now)
    }

    /// Intersect the unchanged limit with an owner's retained ceiling using
    /// one wall observation. Caller cancellation is still sampled on both
    /// sides of that observation; neither deadline can be enlarged.
    pub(super) fn check_diagnostic_with_owner_deadline(
        self,
        owner_deadline: Instant,
    ) -> Result<(), ReplayLimitRefusal> {
        self.check_diagnostic_with_clock_and_owner(&mut Instant::now, Some(owner_deadline))
    }

    fn check_diagnostic_with_clock(
        self,
        now: &mut impl FnMut() -> Instant,
    ) -> Result<(), ReplayLimitRefusal> {
        self.check_diagnostic_with_clock_and_owner(now, None)
    }

    fn check_diagnostic_with_clock_and_owner(
        self,
        now: &mut impl FnMut() -> Instant,
        owner_deadline: Option<Instant>,
    ) -> Result<(), ReplayLimitRefusal> {
        if self
            .cancellation()
            .is_some_and(ReplayCancellation::is_cancelled)
        {
            return Err(ReplayLimitRefusal::InheritedCancellation);
        }
        let observed = self.deadline().or(owner_deadline).map(|_| now());
        let expired = self
            .deadline()
            .zip(observed)
            .is_some_and(|(deadline, observed)| observed >= deadline);
        let cancelled = self
            .cancellation()
            .is_some_and(ReplayCancellation::is_cancelled);
        // Keep the exact two cancellation observations and one optional clock
        // observation of check_with_clock. Report the first declining stage.
        if expired {
            return Err(ReplayLimitRefusal::OriginalDeadline);
        }
        if cancelled {
            return Err(ReplayLimitRefusal::InheritedCancellation);
        }
        // Preserve the old order: the original limit's post-clock cancellation
        // precedes the owner's separate ceiling. Only the clock read is shared.
        if owner_deadline
            .zip(observed)
            .is_some_and(|(deadline, observed)| observed >= deadline)
        {
            return Err(ReplayLimitRefusal::OriginalDeadline);
        }
        Ok(())
    }

    pub(crate) fn phase<T>(self, operation: impl FnOnce() -> Option<T>) -> Option<T> {
        self.phase_with_clock(Instant::now, operation)
    }

    // The injected clock is private, solely to test the production admission
    // sequence deterministically. There is no user-configurable clock or limit.
    fn phase_with_clock<T>(
        self,
        mut now: impl FnMut() -> Instant,
        operation: impl FnOnce() -> Option<T>,
    ) -> Option<T> {
        self.check_with_clock(&mut now)?;
        let proposed = operation();
        self.check_with_clock(&mut now)?;
        proposed
    }

    /// #completed-check-accepted: admit `operation` at entry and never consult
    /// the clock or cancellation after it returns. Use this only where every
    /// `Some` the operation can return is a completed check (its own inner
    /// phases still refuse overruns BETWEEN their steps); a stop that lands
    /// after the last step must not turn a finished check into a refusal.
    pub(crate) fn admit<T>(self, operation: impl FnOnce() -> Option<T>) -> Option<T> {
        self.admit_with_clock(Instant::now, operation)
    }

    fn admit_with_clock<T>(
        self,
        mut now: impl FnMut() -> Instant,
        operation: impl FnOnce() -> Option<T>,
    ) -> Option<T> {
        self.check_with_clock(&mut now)?;
        operation()
    }
}

#[cfg(test)]
mod diagnostic_tests;
#[cfg(test)]
mod tests;
