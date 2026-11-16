// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-bound safety and counterexample admission for quantified Horn clauses.

use std::sync::Arc;
use std::time::Duration;

use ay_core::time::Instant;

use crate::smt::{ScopedSmtDeadline, SmtContext};
use crate::transform::array_ghost_pairs::{try_quantified_source, QuantifiedSourceCertificate};
use crate::{CancellationToken, ChcReplayObligation};

use super::{counterexample, QuantifiedChcCounterexample, QuantifiedChcProblem};

/// Result of bounded original-source quantified reachability and synthesis.
///
/// Finite instances overapproximate reachability and cannot establish Unsafe.
/// Counterexamples instead require sealed SAT for a complete original-source
/// derivation, including every universally quantified premise in that tree.
#[derive(Debug)]
#[must_use = "Unknown is neither safety evidence nor a counterexample"]
#[expect(
    clippy::large_enum_variant,
    reason = "source-bound safety evidence stays by value without an unmetered allocation or public API change"
)]
pub enum QuantifiedChcResult {
    /// Every original clause was discharged under the quantified invariant.
    Safe(QuantifiedChcSafety),
    /// A complete original derivation of a query has a validated satisfying model.
    Unsafe(QuantifiedChcCounterexample),
    /// The bounded routes could not produce complete source-bound evidence.
    Unknown,
}

/// Construction-sealed, source-bound quantified safety evidence.
///
/// This is not a quantifier-free invariant artifact or a portable kernel proof.
/// Its replay obligations contain the original universal premises and the
/// synthesized quantified predicate interpretations. Each obligation must be
/// UNSAT. No conversion to the ordinary CHC result/artifact types is provided.
#[derive(Debug)]
pub struct QuantifiedChcSafety {
    source: Arc<str>,
    certificate: QuantifiedSourceCertificate,
    obligations: Vec<ChcReplayObligation>,
}

impl QuantifiedChcSafety {
    /// Exact typed-source serialization to which this evidence is bound.
    pub fn source_smtlib(&self) -> &str {
        &self.source
    }

    /// Immutable standalone UNSAT obligations, in original clause order.
    pub fn replay_obligations(&self) -> &[ChcReplayObligation] {
        &self.obligations
    }

    /// Recheck against the complete original source under a fresh time budget.
    ///
    /// Source changes, cancellation, expiry, unsupported expressions and any
    /// non-UNSAT discharge withhold acceptance. The original certificate's
    /// term-store budget remains applicable; this is not process-RSS isolation.
    pub fn recheck(
        &self,
        problem: &QuantifiedChcProblem,
        time_budget: Duration,
        cancellation: &CancellationToken,
    ) -> bool {
        checked_attempt(time_budget, cancellation, |deadline, attempt| {
            if self.source.as_ref() != problem.source_smtlib() {
                return None;
            }
            let _deadline = ScopedSmtDeadline::install_until(deadline);
            self.certificate
                .recheck(problem, deadline, attempt)
                .then_some(())
        })
        .is_some()
    }
}

impl QuantifiedChcProblem {
    /// Search original quantified derivations and certify array invariants using AY.
    ///
    /// This bounded, sequential route preserves symbolic universal premises;
    /// it does not enumerate the bit-vector domain or fall back to solving a
    /// source with premises removed. Zero/overflowing time budgets decline.
    /// Lazy cost-deepening occurrence-tree search interleaves query discovery
    /// and native SAT retries within the first quarter of the remaining wall;
    /// invariant synthesis keeps the rest. Scalar-only sources with ordinary
    /// functions and no aggregate predicate state keep the full counterexample
    /// wall: the current invariant routes require array observations. Search has no
    /// fixed occurrence or candidate count cutoff, but shared work/copy and
    /// solver controls apply.
    /// `memory_budget` uses the existing per-context term-store byte budget,
    /// tightened by an enclosing budget; it is not an aggregate RSS limit.
    /// Cancellation is cooperative between bounded phases and SMT calls. Once
    /// any descendant observes caller cancellation, resetting that caller token
    /// cannot revive this attempt; a fresh invocation can use the reset token.
    pub fn solve(
        &self,
        time_budget: Duration,
        memory_budget: Option<usize>,
        cancellation: &CancellationToken,
    ) -> QuantifiedChcResult {
        match checked_attempt(time_budget, cancellation, |deadline, attempt| {
            self.solve_inner(deadline, memory_budget, attempt)
        }) {
            Some(result) => result,
            None => QuantifiedChcResult::Unknown,
        }
    }

    fn solve_inner(
        &self,
        deadline: Instant,
        memory_budget: Option<usize>,
        cancellation: &CancellationToken,
    ) -> Option<QuantifiedChcResult> {
        let mut context = SmtContext::new();
        let memory_budget = tighter_budget(context.term_memory_budget, memory_budget);
        context.set_term_memory_budget(memory_budget);
        let _memory = SmtContext::scoped_thread_term_memory_budget(memory_budget);
        let _deadline = ScopedSmtDeadline::install_until(deadline);
        if stopped(deadline, cancellation) || context.exact_term_memory_exceeded() {
            return None;
        }
        let now = Instant::now();
        let search_deadline = self.counterexample_deadline(now, deadline)?;
        let counterexample = {
            let _search_deadline = ScopedSmtDeadline::install_until(search_deadline);
            counterexample::search(self, search_deadline, memory_budget, cancellation)
        };
        if stopped(deadline, cancellation) || context.exact_term_memory_exceeded() {
            return None;
        }
        if let Some(evidence) = counterexample {
            return Some(QuantifiedChcResult::Unsafe(evidence));
        }
        let safety = certify_source(self, deadline, cancellation, memory_budget)?;
        if stopped(deadline, cancellation) || context.exact_term_memory_exceeded() {
            return None;
        }
        Some(QuantifiedChcResult::Safe(safety))
    }

    pub(super) fn counterexample_deadline(
        &self,
        now: Instant,
        deadline: Instant,
    ) -> Option<Instant> {
        let source = self.source_problem();
        if !self.functions.is_empty() && !source.has_array_sorts() && !source.has_datatype_sorts() {
            Some(deadline)
        } else {
            now.checked_add(deadline.saturating_duration_since(now) / 4)
        }
    }
}

/// Keep the existing certificate's native/proof owners and original source gates.
/// Complete-CEX source accounting is separate and must be checked by its caller.
pub(super) fn certify_source(
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    cancellation: &CancellationToken,
    memory_budget: Option<usize>,
) -> Option<QuantifiedChcSafety> {
    let certificate = try_quantified_source(problem, deadline, cancellation, memory_budget)?;
    let obligations = certificate
        .replay_obligations(problem, deadline, cancellation)
        .ok()?;
    let source = Arc::from(problem.source_smtlib());
    if stopped(deadline, cancellation) {
        return None;
    }
    Some(QuantifiedChcSafety {
        source,
        certificate,
        obligations,
    })
}

/// One caller-observation latch spans every nested synthesis/replay phase.
/// The work closure destroys its contexts/guards before terminal admission;
/// cleanup may itself observe cancellation or exhaust the original deadline.
pub(super) fn checked_attempt<T>(
    budget: Duration,
    caller: &CancellationToken,
    work: impl FnOnce(Instant, &CancellationToken) -> Option<T>,
) -> Option<T> {
    let deadline = deadline(budget)?;
    if stopped(deadline, caller) {
        return None;
    }
    let attempt = caller.sticky_child();
    if stopped(deadline, &attempt) {
        return None;
    }
    let result = work(deadline, &attempt);
    if stopped(deadline, &attempt) {
        return None;
    }
    result
}

fn deadline(budget: Duration) -> Option<Instant> {
    if budget.is_zero() {
        return None;
    }
    let deadline = Instant::now().checked_add(budget)?;
    Some(
        crate::smt::deadline::current_smt_deadline()
            .map_or(deadline, |parent| parent.min(deadline)),
    )
}

fn stopped(deadline: Instant, cancellation: &CancellationToken) -> bool {
    cancellation.is_cancelled()
        || Instant::now() >= deadline
        || ay_core::TermStore::global_memory_exceeded()
}

pub(super) fn tighter_budget(parent: Option<usize>, requested: Option<usize>) -> Option<usize> {
    match (parent, requested) {
        (Some(parent), Some(requested)) => Some(parent.min(requested)),
        (Some(parent), None) => Some(parent),
        (None, requested) => requested,
    }
}

#[cfg(test)]
mod attempt_tests;
#[cfg(test)]
mod function_schedule_tests;
#[cfg(test)]
mod grouped_tests;
#[cfg(test)]
mod nested_cell_tests;
#[cfg(test)]
mod tests;
