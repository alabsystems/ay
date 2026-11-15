// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed caller-thread cancellation; no callback can revive a refused attempt.

use super::BackwardProofFailure;
use std::cell::Cell;

pub(super) struct Cancellation<'a> {
    keep_going: &'a dyn Fn() -> bool,
    state: Cell<State>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Ready,
    Calling,
    Cancelled,
}

impl<'a> Cancellation<'a> {
    pub(super) fn new(keep_going: &'a dyn Fn() -> bool) -> Self {
        Self {
            keep_going,
            state: Cell::new(State::Ready),
        }
    }

    pub(super) fn check_latched(&self) -> Result<(), BackwardProofFailure> {
        if self.state.get() == State::Ready {
            Ok(())
        } else {
            self.state.set(State::Cancelled);
            Err(BackwardProofFailure::Cancelled)
        }
    }

    pub(super) fn poll(&self) -> Result<(), BackwardProofFailure> {
        // Pre-latch before entering caller code. If an inner panic catcher
        // returns control here later, the same attempt remains cancelled.
        if self.state.replace(State::Calling) != State::Ready {
            self.state.set(State::Cancelled);
            return Err(BackwardProofFailure::Cancelled);
        }
        if (self.keep_going)() && self.state.get() == State::Calling {
            self.state.set(State::Ready);
            Ok(())
        } else {
            // In particular, an outer accepting callback cannot clear the
            // cancellation recorded by a nested poll or latch check.
            self.state.set(State::Cancelled);
            Err(BackwardProofFailure::Cancelled)
        }
    }
}
