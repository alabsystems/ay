// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Predictive term-clone admission under local and legacy resource limits.

use super::Executor;

impl Executor {
    /// Allow a speculative clone at most half of the tighter term allowance.
    ///
    /// Portfolio workers install their local share on the executor. The legacy
    /// process-wide divisor may impose a tighter bound, but cannot enlarge that
    /// installed share. This is predictive admission, not a memory reservation
    /// or a replacement for the caller's existing stop and RSS checks.
    pub(in crate::executor) fn predictive_term_clone_budget(&self) -> usize {
        let legacy = ay_core::TermStore::per_engine_budget();
        self.term_memory_limit()
            .map_or(legacy, |installed| installed.min(legacy))
            / 2
    }
}

#[cfg(test)]
mod tests;
