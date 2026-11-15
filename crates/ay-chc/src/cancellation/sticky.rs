// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared observation of upstream refusal, without upward cancellation writes.

use super::*;

#[derive(Debug)]
pub(super) struct StickyUpstream {
    flags: Vec<Arc<AtomicBool>>,
    observed: AtomicBool,
}

impl StickyUpstream {
    pub(super) fn is_cancelled(&self) -> bool {
        if self.observed.load(Ordering::Relaxed)
            || self.flags.iter().any(|flag| flag.load(Ordering::Relaxed))
        {
            // Refusal only: this flag publishes no solver data or evidence.
            self.observed.store(true, Ordering::Relaxed);
            true
        } else {
            false
        }
    }
}

impl CancellationToken {
    /// Start an attempt that cannot resume after observing caller cancellation.
    ///
    /// Clones, children and tokens linked to this attempt share its upstream
    /// observation. If any descendant observes this parent or its upstream
    /// flags cancelled, later resets of those flags cannot revive the attempt.
    /// Resetting the returned token also leaves that observation latched.
    /// A fresh call on an uncancelled original parent starts a new attempt.
    ///
    /// Cancelling a descendant's own flag remains lane-local: it neither
    /// cancels this parent nor poisons sibling lanes. This is useful when one
    /// solve/recheck batch spans several independently budgeted solver calls.
    /// No monitor thread is started; a cancel/reset pulse that no descendant
    /// observes is not recorded. Link parents before creating the attempt;
    /// later links are not retroactive, as with [`Self::child`].
    pub fn sticky_child(&self) -> Self {
        let mut child = self.child();
        let flags = std::iter::once(&self.cancelled)
            .chain(self.upstream.iter())
            .map(Arc::clone)
            .collect();
        child.sticky_upstream.push(Arc::new(StickyUpstream {
            flags,
            observed: AtomicBool::new(self.is_cancelled()),
        }));
        child
    }
}

#[cfg(test)]
mod tests;
