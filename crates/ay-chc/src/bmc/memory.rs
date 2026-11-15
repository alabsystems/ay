// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Captured direct-BMC ownership of per-context term memory, not process RSS.

use crate::smt::SmtContext;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Budget {
    bytes: Option<usize>,
}

impl Budget {
    /// Capture on the caller thread: thread-local scopes do not cross spawn.
    pub(crate) fn capture(explicit: Option<usize>, adaptive: Option<usize>) -> Self {
        Self {
            bytes: [
                explicit,
                adaptive,
                SmtContext::current_thread_term_memory_budget(),
            ]
            .into_iter()
            .flatten()
            .min(),
        }
    }

    pub(crate) fn term_limit(self) -> Option<usize> {
        self.bytes
    }

    pub(crate) fn open(self) -> bool {
        let exceeded = self.bytes == Some(0) || ay_core::TermStore::global_memory_exceeded();
        crate::smt::resource_observation::note_memory_refusal(exceeded);
        !exceeded
    }

    pub(crate) fn install(self) -> impl Drop {
        let current = Self::capture(self.bytes, None);
        SmtContext::scoped_thread_term_memory_budget(current.bytes)
    }

    /// The worker and spawn-failure fallback use the same captured owner.
    pub(crate) fn run<T>(self, operation: impl FnOnce() -> T) -> Option<T> {
        let current = Self::capture(self.bytes, None);
        if !current.open() {
            return None;
        }
        let _scope = current.install();
        let result = operation();
        Self::capture(current.bytes, None).open().then_some(result)
    }

    /// Tighten a persistent executor before each command/model-observation batch.
    pub(crate) fn constrain(self, executor: &mut ay_dpll::Executor) -> bool {
        let current = Self::capture(self.bytes, executor.term_memory_limit());
        executor.set_term_memory_limit(current.bytes);
        self.executor_open(executor)
    }

    pub(crate) fn executor_open(self, executor: &ay_dpll::Executor) -> bool {
        let current = Self::capture(self.bytes, executor.term_memory_limit());
        crate::smt::resource_observation::note_executor_refusal(executor.unknown_reason());
        let memory_refused = matches!(
            executor.unknown_reason(),
            Some(ay_dpll::UnknownReason::MemoryLimit)
        );
        let open = !memory_refused
            && current.open()
            && current
                .bytes
                .is_none_or(|bytes| executor.terms().true_memory_bytes() <= bytes);
        crate::smt::resource_observation::note_memory_refusal(!open);
        open
    }
}

#[cfg(test)]
mod tests;
