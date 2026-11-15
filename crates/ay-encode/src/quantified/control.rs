// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

pub(super) struct Control<'a> {
    deadline: Instant,
    token: CancellationToken,
    stopped: Cell<Option<QuantifiedQueryUnknownReason>>,
    clock: &'a dyn Fn() -> Instant,
    memory_exceeded: &'a dyn Fn() -> bool,
}

impl<'a> Control<'a> {
    pub(super) fn new(
        started: Instant,
        budget: Duration,
        parent: &CancellationToken,
        clock: &'a dyn Fn() -> Instant,
    ) -> crate::Result<Self> {
        let deadline = started
            .checked_add(budget)
            .filter(|_| !budget.is_zero())
            .ok_or(crate::EncodeError::Chc(ay_chc::ChcError::Timeout(0)))?;
        let control = Self {
            deadline,
            token: parent.sticky_child(),
            stopped: Cell::new(None),
            clock,
            memory_exceeded: &ay_core::TermStore::global_memory_exceeded,
        };
        control.require_live()?;
        Ok(control)
    }

    pub(super) fn token(&self) -> &CancellationToken {
        &self.token
    }

    pub(super) fn now(&self) -> Instant {
        (self.clock)()
    }

    pub(super) fn row_deadline(&self, rows_left: usize) -> Option<Instant> {
        self.require_live().ok()?;
        let now = self.now();
        let remaining = self.deadline.saturating_duration_since(now);
        let share = remaining.checked_div(u32::try_from(rows_left).ok()?)?;
        Some(now.checked_add(share)?.min(self.deadline))
    }

    pub(super) fn reason(&self) -> Option<QuantifiedQueryUnknownReason> {
        if let Some(reason) = self.stopped.get() {
            return Some(reason);
        }
        let reason = if self.token.is_cancelled() {
            Some(QuantifiedQueryUnknownReason::Cancelled)
        } else if (self.memory_exceeded)() {
            Some(QuantifiedQueryUnknownReason::MemoryExhausted)
        } else if self.now() >= self.deadline {
            Some(QuantifiedQueryUnknownReason::BudgetExhausted)
        } else {
            None
        };
        if reason.is_some() {
            self.stopped.set(reason);
            self.token.cancel();
        }
        reason
    }

    pub(super) fn require_live(&self) -> crate::Result<()> {
        match self.reason() {
            None => Ok(()),
            Some(QuantifiedQueryUnknownReason::Cancelled) => Err(crate::EncodeError::Cancelled),
            Some(QuantifiedQueryUnknownReason::MemoryExhausted) => Err(
                ay_chc::ChcError::Verification("quantified batch memory exhausted".into()).into(),
            ),
            Some(_) => Err(ay_chc::ChcError::Timeout(0).into()),
        }
    }

    pub(super) fn remaining(&self) -> crate::Result<Duration> {
        self.require_live()?;
        Ok(self.deadline.saturating_duration_since(self.now()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn observed_memory_refusal_stays_terminal_after_the_probe_recovers() {
        let start = Instant::now();
        let clock = || start;
        let memory = Cell::new(false);
        let probe = || memory.get();
        let parent = CancellationToken::new();
        let mut control = Control::new(start, Duration::from_secs(10), &parent, &clock).unwrap();
        control.memory_exceeded = &probe;
        assert_eq!(control.reason(), None);
        memory.set(true);
        assert_eq!(
            control.reason(),
            Some(QuantifiedQueryUnknownReason::MemoryExhausted)
        );
        memory.set(false);
        assert_eq!(
            control.reason(),
            Some(QuantifiedQueryUnknownReason::MemoryExhausted)
        );
        assert!(control.require_live().is_err());
        assert!(!parent.is_cancelled());
        let fresh = Control::new(start, Duration::from_secs(10), &parent, &clock).unwrap();
        assert_eq!(fresh.reason(), None);
    }
}
