// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Invocation-local stop state for expression rewrites. Node-limit fallback
//! preserves existing semantics; a caller cancellation discards the whole result.

pub(crate) struct RewriteBudget<'a> {
    remaining: std::cell::Cell<usize>,
    #[cfg(test)]
    polls: std::cell::Cell<usize>,
    stopped: std::cell::Cell<bool>,
    should_stop: std::cell::RefCell<&'a mut dyn FnMut() -> bool>,
}

impl<'a> RewriteBudget<'a> {
    pub(crate) fn new(nodes: usize, should_stop: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            remaining: std::cell::Cell::new(nodes),
            #[cfg(test)]
            polls: std::cell::Cell::new(0),
            stopped: std::cell::Cell::new(false),
            should_stop: std::cell::RefCell::new(should_stop),
        }
    }
    pub(crate) fn get(&self) -> usize {
        self.remaining.get()
    }
    pub(crate) fn set(&self, value: usize) {
        self.remaining.set(value);
    }
    #[cfg(test)]
    pub(crate) fn poll_count(&self) -> usize {
        self.polls.get()
    }
    pub(crate) fn stopped(&self) -> bool {
        #[cfg(test)]
        self.polls.set(self.polls.get() + 1);
        if self.stopped.get() {
            return true;
        }
        let stopped = (self.should_stop.borrow_mut())();
        if stopped {
            self.stopped.set(true);
        }
        stopped
    }
}
