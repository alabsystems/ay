// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-preserving quantified CHC invocation, separate from QF proof reports.
//!
//! These reports do not implement conversion to `AyVerdict`, `ProofRun`, a
//! quantifier-free invariant, or a Trust-full-verifier-admissible artifact.

use std::time::Duration;

use ay_chc::quantified::{
    QuantifiedChcCounterexample, QuantifiedChcProblem, QuantifiedChcQueryId,
    QuantifiedChcQueryObligation, QuantifiedChcSafety,
};
use ay_chc::CancellationToken;
use ay_core::time::Instant;

mod control;
mod runner;
mod schedule;

/// Safe requires every row; Unsafe requires one original row, freshly replayed.
/// Either definite aggregate also requires live final invocation controls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifiedQueryBatchVerdict {
    Safe,
    Unsafe,
    Unknown,
}

/// Facts observed by this invocation, not inferred internal solver diagnoses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifiedQueryUnknownReason {
    Cancelled,
    BudgetExhausted,
    MemoryExhausted,
    Inconclusive,
    ReplayRejected,
}

/// One complete quantified-source outcome, never an ordinary QF artifact.
#[derive(Debug)]
pub enum QuantifiedQueryOutcome {
    /// A sealed source certificate that also passed this invocation's recheck.
    CheckedSafe(QuantifiedChcSafety),
    /// A full-original-source path that passed fresh validated SAT replay.
    CheckedUnsafe(QuantifiedChcCounterexample),
    Unknown(QuantifiedQueryUnknownReason),
    Error(crate::EncodeError),
}

/// Immutable original-query identity, complete slice and its own outcome.
#[derive(Debug)]
pub struct QuantifiedQueryRowReport {
    obligation: QuantifiedChcQueryObligation,
    outcome: QuantifiedQueryOutcome,
    elapsed: Duration,
}

impl QuantifiedQueryRowReport {
    /// Borrow this row's original sealed source association without cloning or
    /// reslicing. It retains the complete slice and ordered aggregate origins
    /// needed by a concrete trace's explicit aggregate-lifting API.
    /// This accessor itself grants no new replay or aggregate proof authority.
    ///
    /// The obligation cannot outlive its owning report:
    ///
    /// ```compile_fail
    /// use ay_chc::quantified::QuantifiedChcQueryObligation;
    /// use ay_encode::quantified::QuantifiedQueryRowReport;
    /// fn escape(row: QuantifiedQueryRowReport) -> &'static QuantifiedChcQueryObligation {
    ///     row.obligation()
    /// }
    /// ```
    pub fn obligation(&self) -> &QuantifiedChcQueryObligation {
        &self.obligation
    }

    pub fn id(&self) -> &QuantifiedChcQueryId {
        self.obligation.id()
    }

    /// Includes all declarations and the slice's original universal premises.
    pub fn problem(&self) -> &QuantifiedChcProblem {
        self.obligation.problem()
    }

    pub fn outcome(&self) -> &QuantifiedQueryOutcome {
        &self.outcome
    }

    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }
}

/// Construction-sealed membership and outcomes for one complete query batch.
/// Earlier checked rows survive later failures; they never stand for the batch.
#[derive(Debug)]
pub struct QuantifiedQueryBatchReport {
    source: String,
    source_sha256: String,
    rows: Vec<QuantifiedQueryRowReport>,
    verdict: QuantifiedQueryBatchVerdict,
    elapsed: Duration,
}

impl QuantifiedQueryBatchReport {
    pub fn source_smtlib(&self) -> &str {
        &self.source
    }

    pub fn source_sha256(&self) -> &str {
        &self.source_sha256
    }

    pub fn rows(&self) -> &[QuantifiedQueryRowReport] {
        &self.rows
    }

    pub fn verdict(&self) -> QuantifiedQueryBatchVerdict {
        self.verdict
    }

    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }
}

/// Solve all quantified queries sequentially within one total time allowance.
///
/// Source decomposition, solving and fresh replay share the original deadline.
/// Each row receives an equal share of remaining time; half is reserved for
/// replay, with unused solve time available to replay. Later rows inherit unused
/// time. A failed decomposition returns an error, never a partial batch. Once
/// decomposition succeeds every row remains present, even if never started.
///
/// Memory uses AY's per-context term-store limit, not aggregate process RSS.
/// The final gate also samples AY's process/global-term memory refusal signal.
/// Core calls additionally tighten their allowances to any enclosing internal
/// SMT deadline; this facade does not expose or replace that internal scope.
/// Cooperative checkpoints bracket legacy formatting, solving and cleanup;
/// this API does not promise a hard response-time bound. Only AY-classified
/// panics become typed errors; unrelated programmer panics propagate.
pub fn solve_quantified_query_obligations_with_cancellation(
    problem: &QuantifiedChcProblem,
    time_budget: Duration,
    memory_budget: Option<usize>,
    parent: &CancellationToken,
) -> crate::Result<QuantifiedQueryBatchReport> {
    let started = Instant::now();
    let clock = Instant::now;
    let control = control::Control::new(started, time_budget, parent, &clock)?;
    let obligations = runner::caught(|| {
        problem
            .query_obligations(control.remaining()?, control.token())
            .map_err(Into::into)
    })?;
    control.require_live()?;
    let source_sha256 = schedule::digest(problem.source_smtlib());
    schedule::validate_obligations(&source_sha256, &obligations, &control)?;
    let source = problem.source_smtlib().to_owned();
    control.require_live()?;
    let result = schedule::run(obligations, &control, memory_budget, &mut runner::Native);
    let rows = result
        .rows
        .into_iter()
        .map(|row| QuantifiedQueryRowReport {
            obligation: row.obligation,
            outcome: match row.outcome {
                schedule::Outcome::CheckedSafe(runner::NativeEvidence::Safe(evidence)) => {
                    QuantifiedQueryOutcome::CheckedSafe(evidence)
                }
                schedule::Outcome::CheckedUnsafe(runner::NativeEvidence::Unsafe(evidence)) => {
                    QuantifiedQueryOutcome::CheckedUnsafe(evidence)
                }
                schedule::Outcome::CheckedSafe(runner::NativeEvidence::Unsafe(_))
                | schedule::Outcome::CheckedUnsafe(runner::NativeEvidence::Safe(_)) => {
                    QuantifiedQueryOutcome::Error(crate::EncodeError::Chc(
                        ay_chc::ChcError::Verification("quantified evidence kind mismatch".into()),
                    ))
                }
                schedule::Outcome::Unknown(reason) => QuantifiedQueryOutcome::Unknown(reason),
                schedule::Outcome::Error(error) => QuantifiedQueryOutcome::Error(error),
            },
            elapsed: row.elapsed,
        })
        .collect();
    let elapsed = started.elapsed();
    let live = control.reason().is_none();
    let verdict = if result.checked_unsafe && live {
        QuantifiedQueryBatchVerdict::Unsafe
    } else if result.all_checked && live {
        QuantifiedQueryBatchVerdict::Safe
    } else {
        QuantifiedQueryBatchVerdict::Unknown
    };
    Ok(QuantifiedQueryBatchReport {
        source,
        source_sha256,
        rows,
        verdict,
        elapsed,
    })
}

#[cfg(test)]
mod tests;
