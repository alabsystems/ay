// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive complete-value result with one original wall for discovery/replay.

use super::{
    counterexample, solve, QuantifiedChcCompleteTrace, QuantifiedChcProblem, QuantifiedChcSafety,
};
use crate::smt::{ScopedSmtDeadline, SmtContext};
use crate::transform::array_ghost_pairs::source_premises::SourceControl;
use crate::CancellationToken;
use ay_core::time::Instant;
use std::time::Duration;

/// A complete trace requires native SAT of every original premise AND its pins.
/// This is not ordinary ground CHC evidence or MODEL_CHECKER_CONSUMER interpreter playback.
#[derive(Debug)]
#[must_use = "Unknown grants neither safety nor counterexample authority"]
#[expect(
    clippy::large_enum_variant,
    reason = "source-bound safety evidence stays by value without an unmetered allocation or public API change"
)]
pub enum QuantifiedChcCompleteResult {
    /// The existing original-source quantified safety certificate.
    Safe(QuantifiedChcSafety),
    /// One complete, source-bound assignment passed full original pinned SAT.
    Unsafe(QuantifiedChcCompleteTrace),
    /// No complete source-bound credential was admitted.
    Unknown,
}

impl QuantifiedChcProblem {
    /// Search exact array-definition advice, acquire one model, and check the
    /// FULL original derivation with all pins before returning Unsafe.
    ///
    /// Advice SAT is private DATA, never a counterexample. Discovery, acquisition
    /// and fresh native original replay share one captured absolute end, sticky
    /// child token, inherited/requested minimum term cap and SourceControl.
    /// Each native solver retains its existing native work/model allowances;
    /// source accounting is cooperative logical preparation/copy accounting,
    /// not all native work or aggregate RSS. Safety preserves the legacy
    /// certificate's separate native/proof owners. A spent complete-source
    /// ledger forbids that fallback. Local retry slices do not renew the end.
    /// Existing solve/complete_trace/recheck APIs keep their fresh-budget meaning.
    pub fn solve_with_complete_trace(
        &self,
        time_budget: Duration,
        memory_budget: Option<usize>,
        cancellation: &CancellationToken,
    ) -> QuantifiedChcCompleteResult {
        solve::checked_attempt(time_budget, cancellation, |deadline, attempt| {
            let control = SourceControl::new(deadline, attempt);
            let result = {
                let mut context = SmtContext::new();
                let memory = solve::tighter_budget(context.term_memory_budget, memory_budget);
                context.set_term_memory_budget(memory);
                let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
                let _deadline = ScopedSmtDeadline::install_until(deadline);
                if memory == Some(0) || context.exact_term_memory_exceeded() {
                    return None;
                }
                let result = complete_inner(self, deadline, memory, attempt, &control);
                if context.exact_term_memory_exceeded() {
                    return None;
                }
                result
            };
            // Context, local term-cap/deadline guards and native scratch are gone.
            control.poll()?;
            result
        })
        .unwrap_or(QuantifiedChcCompleteResult::Unknown)
    }
}

fn complete_inner(
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<QuantifiedChcCompleteResult> {
    control.poll()?;
    let search_deadline = problem.counterexample_deadline(Instant::now(), deadline)?;
    if let Some(trace) = counterexample::search_complete(
        problem,
        search_deadline,
        deadline,
        memory,
        cancellation,
        control,
    ) {
        control.poll()?;
        return Some(QuantifiedChcCompleteResult::Unsafe(trace));
    }
    // Search slice expiry is retryable; a refused ORIGINAL owner is not.
    control.poll()?;
    let safety = solve::certify_source(problem, deadline, cancellation, memory)?;
    control.poll()?;
    Some(QuantifiedChcCompleteResult::Safe(safety))
}

#[cfg(test)]
mod tests;
