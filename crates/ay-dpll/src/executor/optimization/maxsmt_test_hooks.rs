// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thread-local fault injection for MaxSMT resource-decline regressions.

use std::cell::Cell;

thread_local! {
    static CHECKED_DECISIONS_BEFORE_DECLINE: Cell<Option<usize>> = const { Cell::new(None) };
}

/// Panic-safe scope forcing one checked MaxSMT decision to decline after the
/// requested number of preceding decisions. Thread-local state keeps parallel
/// tests and independent solvers isolated.
pub(in crate::executor) struct CheckedDecisionDeclineGuard(Option<usize>);

impl CheckedDecisionDeclineGuard {
    pub(in crate::executor) fn after(preceding: usize) -> Self {
        let previous = CHECKED_DECISIONS_BEFORE_DECLINE.with(|state| {
            let previous = state.get();
            state.set(Some(preceding));
            previous
        });
        Self(previous)
    }
}

impl Drop for CheckedDecisionDeclineGuard {
    fn drop(&mut self) {
        CHECKED_DECISIONS_BEFORE_DECLINE.with(|state| state.set(self.0));
    }
}

pub(super) fn decline_checked_decision() -> bool {
    CHECKED_DECISIONS_BEFORE_DECLINE.with(|state| match state.get() {
        Some(0) => {
            state.set(None);
            true
        }
        Some(remaining) => {
            state.set(Some(remaining - 1));
            false
        }
        None => false,
    })
}
