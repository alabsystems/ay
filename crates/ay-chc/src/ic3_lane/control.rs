// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative, attempt-local control for IC3 candidate preparation.
//!
//! A rung may have an earlier deadline than its parent lane. Its callback polls
//! the same parent, so a fresh rung cannot revive a refused whole-lane attempt.
//! Individual clone/hash/simplification and SAT operations remain opaque; this
//! is not a hard response-time bound.

use ay_core::time::Instant;
use std::cell::{Cell, RefCell};

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Ready,
    Calling,
    Stopped,
}

pub(super) struct Control<'a> {
    deadline: Instant,
    keep_going: RefCell<&'a mut dyn FnMut() -> bool>,
    state: Cell<State>,
    #[cfg(test)]
    clock: Option<&'a dyn Fn() -> Instant>,
}

impl<'a> Control<'a> {
    pub(super) fn new(deadline: Instant, keep_going: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            deadline,
            keep_going: RefCell::new(keep_going),
            state: Cell::new(State::Ready),
            #[cfg(test)]
            clock: None,
        }
    }

    pub(super) fn deadline(&self) -> Instant {
        self.deadline
    }

    #[cfg(test)]
    pub(super) fn stopped(&self) -> bool {
        self.state.get() != State::Ready
    }

    fn now(&self) -> Instant {
        #[cfg(test)]
        if let Some(clock) = self.clock {
            return clock();
        }
        Instant::now()
    }

    pub(super) fn poll(&self) -> Option<()> {
        if self.state.get() != State::Ready {
            self.state.set(State::Stopped);
            return None;
        }
        // Pre-latch also survives a callback panic caught by an outer frame.
        self.state.set(State::Calling);
        if self.now() >= self.deadline
            || !(self.keep_going.borrow_mut())()
            || self.now() >= self.deadline
            || self.state.get() != State::Calling
        {
            self.state.set(State::Stopped);
            return None;
        }
        self.state.set(State::Ready);
        Some(())
    }

    #[cfg(test)]
    pub(super) fn with_clock(
        deadline: Instant,
        keep_going: &'a mut dyn FnMut() -> bool,
        clock: &'a dyn Fn() -> Instant,
    ) -> Self {
        let mut control = Self::new(deadline, keep_going);
        control.clock = Some(clock);
        control
    }
}
