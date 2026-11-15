// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Snapshot the caller's term-store cap without turning it into an RSS limit.

use super::SmtContext;

#[derive(Clone, Copy)]
pub(super) struct ReplayMemory {
    term_limit: Option<usize>,
}

impl ReplayMemory {
    pub(super) fn capture(explicit: Option<usize>) -> Self {
        Self {
            term_limit: explicit
                .into_iter()
                .chain(SmtContext::current_thread_term_memory_budget())
                .min(),
        }
    }

    pub(super) fn term_limit(self) -> Option<usize> {
        self.term_limit
    }

    pub(super) fn check(self) -> Option<()> {
        if self.term_limit == Some(0) || ay_core::TermStore::global_memory_exceeded() {
            crate::smt::resource_observation::note_memory_refusal(true);
            return None;
        }
        Some(())
    }

    pub(super) fn check_terms(self, terms: &ay_core::TermStore) -> Option<()> {
        self.check()?;
        if self
            .term_limit
            .is_some_and(|limit| terms.true_memory_bytes() > limit)
        {
            crate::smt::resource_observation::note_memory_refusal(true);
            return None;
        }
        Some(())
    }

    pub(super) fn check_executor(self, executor: &ay_dpll::Executor) -> Option<()> {
        crate::smt::resource_observation::note_executor_refusal(executor.unknown_reason());
        let term_refused = executor.term_memory_exceeded();
        crate::smt::resource_observation::note_memory_refusal(term_refused);
        self.check_terms(executor.terms())?;
        (!term_refused).then_some(())
    }

    // Parsing/proof buffers are not term-store allocations. These phase checks
    // observe only zero/global exhaustion; the owning solver enforces its local
    // term cap separately. No reservation or aggregate-allocation claim is made.
    pub(super) fn phase<T>(self, operation: impl FnOnce() -> Option<T>) -> Option<T> {
        self.check()?;
        let proposed = operation();
        self.check()?;
        proposed
    }

    /// #completed-check-accepted: entry admission only, for a phase whose
    /// every `Some` is a completed check (see `ReplayLimit::admit`).
    pub(super) fn admit<T>(self, operation: impl FnOnce() -> Option<T>) -> Option<T> {
        self.check()?;
        operation()
    }
}

#[cfg(test)]
mod tests;
