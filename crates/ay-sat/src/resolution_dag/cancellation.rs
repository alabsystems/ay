// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-thread cancellation; never stores a borrowed callback in the solver
//! or its `Send + 'static` proof writer.

use super::{Instant, ResolutionProofError, ResolutionProofPhase};
use ay_core::time::ClockStride;
use std::cell::{Cell, RefCell};

/// Checks between two clock reads of [`ProofControl::check`]'s deadline. A
/// check follows at most one 256-literal chunk or one clause of work, so a
/// passed deadline is seen within microseconds; the callback is still asked
/// at every check. Read at every check, the clock was 5% of a long strict
/// producer run (corpus9 0644, sampled 2026-10-09; DR-34).
const CHECK_CLOCK_STRIDE: u32 = 64;

pub(crate) struct ProofControl<'a> {
    keep_going: RefCell<&'a mut dyn FnMut() -> bool>,
    state: Cell<State>,
    /// Conflicts the solver reported spending (`record_conflicts`).
    conflicts: Cell<u64>,
    /// When [`Self::check`] reads the clock.
    clock: ClockStride,
    /// The latest deadline a check saw pass. Time is monotonic, so a later
    /// check against it, or against an earlier one, fails without waiting
    /// for its stride.
    passed: Cell<Option<Instant>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Ready,
    Calling,
    Cancelled,
}

impl<'a> ProofControl<'a> {
    pub(crate) fn new(keep_going: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            keep_going: RefCell::new(keep_going),
            state: Cell::new(State::Ready),
            conflicts: Cell::new(0),
            clock: ClockStride::new(CHECK_CLOCK_STRIDE),
            passed: Cell::new(None),
        }
    }

    /// Note the solver's conflict count, and return it.
    pub(super) fn record_conflicts(&self, conflicts: u64) -> u64 {
        self.conflicts.set(conflicts);
        conflicts
    }

    /// The conflicts recorded so far; `0` when no search ran.
    pub(crate) fn conflicts(&self) -> u64 {
        self.conflicts.get()
    }

    pub(super) fn poll(&self) -> Result<(), ResolutionProofError> {
        if self.state.replace(State::Calling) != State::Ready {
            self.state.set(State::Cancelled);
            return Err(ResolutionProofError::Cancelled);
        }
        // Latch before caller code: even a panic caught by a lower-level
        // guard cannot resurrect this attempt. Reentrant polling fails closed
        // without reborrowing the callback. No thread or lifetime cast is used.
        let Ok(mut keep_going) = self.keep_going.try_borrow_mut() else {
            self.state.set(State::Cancelled);
            return Err(ResolutionProofError::Cancelled);
        };
        if keep_going() && self.state.get() == State::Calling {
            self.state.set(State::Ready);
            Ok(())
        } else {
            self.state.set(State::Cancelled);
            Err(ResolutionProofError::Cancelled)
        }
    }

    pub(super) fn check(
        &self,
        deadline: Option<Instant>,
        phase: ResolutionProofPhase,
    ) -> Result<(), ResolutionProofError> {
        self.poll()?;
        // Read the clock after caller work, never grant a fresh relative
        // allowance if the callback itself consumed the remaining deadline.
        let Some(end) = deadline else {
            return Ok(());
        };
        if self.passed.get().is_some_and(|seen| end <= seen) {
            return Err(ResolutionProofError::DeadlineExceeded { phase });
        }
        if self.clock.due() && Instant::now() >= end {
            self.passed.set(Some(end));
            return Err(ResolutionProofError::DeadlineExceeded { phase });
        }
        Ok(())
    }

    pub(super) fn check_latched(&self) -> Result<(), ResolutionProofError> {
        if self.state.get() == State::Ready {
            Ok(())
        } else {
            self.state.set(State::Cancelled);
            Err(ResolutionProofError::Cancelled)
        }
    }

    pub(crate) fn run<T>(
        &self,
        operation: impl FnOnce(&Self) -> Result<T, ResolutionProofError>,
    ) -> Result<T, ResolutionProofError> {
        self.poll()?;
        let result = operation(self);
        // A caught callback panic/refusal remains terminal, but a new callback
        // must not replace an ordinary error which the operation already found.
        self.check_latched()?;
        if result.is_ok() {
            // Operation-local solver, writer and replay scratch are gone.
            // A refused attempt never publishes a SAT model or a proof.
            self.poll()?;
        }
        result
    }
}

#[cfg(test)]
mod tests;
