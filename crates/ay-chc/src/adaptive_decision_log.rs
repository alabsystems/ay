// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured decision logging for the adaptive portfolio solver.
//!
//! When the decision-log path is configured (CLI-carried trace config),
//! every adaptive strategy decision is written as a JSON line to that file.
//! An invocation-scoped observer can also retain the same decisions in memory
//! without requiring file logging.
//!
//! Part of #7918 - Adaptive portfolio observability.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Duration;

/// Typed outcome reported by one adaptive strategy observation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AdaptiveStrategyOutcome {
    /// The strategy returned a verified-safe candidate to the dispatcher.
    Safe,
    /// The strategy returned a counterexample candidate to the dispatcher.
    Unsafe,
    /// The strategy did not establish a verdict.
    Unknown,
    /// The strategy gate deliberately skipped this attempt.
    Skipped,
    /// The strategy did not apply to the classified problem.
    NotApplicable,
    /// The strategy asked the authoritative solve to make its one escalation retry.
    Retry,
    /// The strategy reached its time limit.
    TimedOut,
    /// A structural or resource cap prevented the strategy from running.
    CapExceeded,
    /// The strategy is intentionally excluded from verdict promotion.
    Quarantined,
    /// The named dispatch point was reached.
    Reached,
    /// A route-specific stable result code not covered by the common variants.
    RouteSpecific(String),
}

impl AdaptiveStrategyOutcome {
    fn from_code(code: &str) -> Self {
        match code {
            "safe" => Self::Safe,
            "unsafe" => Self::Unsafe,
            "unknown" => Self::Unknown,
            "skipped" => Self::Skipped,
            "not_applicable" => Self::NotApplicable,
            "retry" => Self::Retry,
            "timeout" => Self::TimedOut,
            "cap_exceeded" => Self::CapExceeded,
            "quarantined" => Self::Quarantined,
            "reached" => Self::Reached,
            other => Self::RouteSpecific(other.to_string()),
        }
    }
}

/// One observational event emitted by the authoritative adaptive solve.
///
/// Stage names deliberately are not restricted to [`crate::EngineType`]: the
/// adaptive solver dispatches specialized synthesis, transformation, and
/// validation lanes that are not concrete portfolio engines.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct AdaptiveStrategyObservation {
    /// Adaptive stage or lane name.
    pub stage: &'static str,
    /// Whether the stage's admission gate passed.
    pub gate_result: bool,
    /// Human-readable explanation of the gate or route decision.
    pub gate_reason: String,
    /// Budget assigned to this stage, when the stage has an explicit budget.
    pub budget: Duration,
    /// Observed wall-clock duration of the stage.
    pub elapsed: Duration,
    /// The stage's observational outcome.
    pub outcome: AdaptiveStrategyOutcome,
    /// Lemmas learned by the stage, when applicable.
    pub lemmas_learned: usize,
    /// Maximum PDR frame reached by the stage, when applicable.
    pub max_frame: usize,
}

/// Strategy/lane observations from one exact adaptive solve invocation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[must_use = "adaptive traces should be inspected when solver attribution matters"]
pub struct AdaptiveSolveTrace {
    observations: Vec<AdaptiveStrategyObservation>,
}

impl AdaptiveSolveTrace {
    pub(crate) fn direct_pdr_proof(
        budget: Option<Duration>,
        elapsed: Duration,
        result: &crate::VerifiedChcResult,
    ) -> Self {
        let outcome = match result {
            crate::VerifiedChcResult::Safe(_) => AdaptiveStrategyOutcome::Safe,
            crate::VerifiedChcResult::Unsafe(_) => AdaptiveStrategyOutcome::Unsafe,
            crate::VerifiedChcResult::Unknown(_) => AdaptiveStrategyOutcome::Unknown,
        };
        Self {
            observations: vec![AdaptiveStrategyObservation {
                stage: "direct_pdr_proof",
                gate_result: true,
                gate_reason: "ProofMode::Strict authoritative direct PDR invocation".to_string(),
                budget: budget.unwrap_or(Duration::ZERO),
                elapsed,
                outcome,
                lemmas_learned: 0,
                max_frame: 0,
            }],
        }
    }

    /// Ordered observations emitted while the authoritative invocation ran.
    pub fn observations(&self) -> &[AdaptiveStrategyObservation] {
        &self.observations
    }

    /// Consume the trace and return its ordered observations.
    pub fn into_observations(self) -> Vec<AdaptiveStrategyObservation> {
        self.observations
    }

    /// Whether no adaptive dispatch point emitted an observation.
    pub fn is_empty(&self) -> bool {
        self.observations.is_empty()
    }
}

/// Whole-run timing and strategy attribution from one adaptive solve.
///
/// Both fields are collected around the exact invocation that produced the
/// accompanying verdict. No reporting-only portfolio is selected and the
/// solver is not re-run.
#[derive(Debug)]
#[must_use = "adaptive solve reports should be inspected"]
pub struct AdaptiveSolveReport {
    budget_report: crate::BudgetReport,
    strategy_trace: AdaptiveSolveTrace,
}

impl AdaptiveSolveReport {
    pub(crate) fn new(
        budget_report: crate::BudgetReport,
        strategy_trace: AdaptiveSolveTrace,
    ) -> Self {
        Self {
            budget_report,
            strategy_trace,
        }
    }

    /// Whole-run wall-clock accounting for the exact solve invocation.
    pub fn budget_report(&self) -> &crate::BudgetReport {
        &self.budget_report
    }

    /// Ordered adaptive strategy/lane observations from that invocation.
    pub fn strategy_trace(&self) -> &AdaptiveSolveTrace {
        &self.strategy_trace
    }

    /// Consume the report into its timing and strategy-attribution parts.
    pub fn into_parts(self) -> (crate::BudgetReport, AdaptiveSolveTrace) {
        (self.budget_report, self.strategy_trace)
    }
}

/// A single decision entry logged by the adaptive portfolio.
pub(crate) struct DecisionEntry {
    /// The adaptive stage name (e.g., "trivial_synthesis", "non_inlined_pdr").
    pub stage: &'static str,
    /// Whether the gate check passed (true = stage was attempted).
    pub gate_result: bool,
    /// Human-readable reason for the gate decision.
    pub gate_reason: String,
    /// Budget allocated to this stage in seconds.
    pub budget_secs: f64,
    /// Wall-clock time consumed by this stage in seconds.
    pub elapsed_secs: f64,
    /// Outcome of the stage.
    ///
    /// Common values include "safe", "unsafe", "unknown", "skipped", and
    /// "not_applicable". Route-specific stages may emit narrower demotion
    /// reasons such as "transformed_unsafe", "validation_timeout", or
    /// "cap_exceeded".
    pub result: &'static str,
    /// Number of lemmas learned during this stage (0 if not applicable).
    pub lemmas_learned: usize,
    /// Maximum PDR frame reached (0 if not applicable).
    pub max_frame: usize,
}

/// Structured decision logger for the adaptive portfolio.
///
/// Holds an optional writer and invocation-scoped in-memory trace sessions.
/// With neither a configured writer nor an active trace, logging takes only an
/// atomic active-session check plus the existing optional-writer check.
pub(crate) struct DecisionLog {
    writer: Mutex<Option<BufWriter<File>>>,
    trace: Mutex<TraceCapture>,
    active_traces: AtomicUsize,
}

#[derive(Default)]
struct TraceCapture {
    next_session: u64,
    sessions: Vec<(u64, Vec<AdaptiveStrategyObservation>)>,
}

pub(crate) struct DecisionTraceSession<'a> {
    log: &'a DecisionLog,
    id: u64,
    finished: bool,
}

impl DecisionTraceSession<'_> {
    pub(crate) fn finish(mut self) -> AdaptiveSolveTrace {
        self.finished = true;
        self.log.finish_trace(self.id)
    }
}

impl Drop for DecisionTraceSession<'_> {
    fn drop(&mut self) {
        if !self.finished {
            let _ = self.log.finish_trace(self.id);
        }
    }
}

impl DecisionLog {
    /// Create a `DecisionLog` from the configured trace-config path.
    ///
    /// Returns a log that writes JSON lines to the specified path, or a no-op
    /// log if the variable is unset or the file cannot be opened.
    pub(crate) fn from_env() -> Self {
        let writer = ay_core::trace_config()
            .decision_log_path
            .clone()
            .and_then(|path| {
                File::create(&path)
                    .map(|f| BufWriter::new(f))
                    .map_err(|e| {
                        // Use eprintln directly here — this runs once at startup.
                        eprintln!("Warning: decision log {path}: could not open for writing: {e}");
                        e
                    })
                    .ok()
            });
        Self {
            writer: Mutex::new(writer),
            trace: Mutex::new(TraceCapture::default()),
            active_traces: AtomicUsize::new(0),
        }
    }

    #[cfg(test)]
    pub(crate) fn from_path_for_test(path: impl AsRef<std::path::Path>) -> Self {
        let writer = File::create(path).ok().map(BufWriter::new);
        Self {
            writer: Mutex::new(writer),
            trace: Mutex::new(TraceCapture::default()),
            active_traces: AtomicUsize::new(0),
        }
    }

    /// Begin retaining observations for one exact solve invocation.
    pub(crate) fn begin_trace(&self) -> DecisionTraceSession<'_> {
        let id = match self.trace.lock() {
            Ok(mut trace) => {
                let id = trace.next_session;
                trace.next_session = trace.next_session.wrapping_add(1);
                trace.sessions.push((id, Vec::new()));
                self.active_traces.fetch_add(1, Ordering::Release);
                id
            }
            Err(_) => u64::MAX,
        };
        DecisionTraceSession {
            log: self,
            id,
            finished: false,
        }
    }

    fn finish_trace(&self, id: u64) -> AdaptiveSolveTrace {
        let observations = self
            .trace
            .lock()
            .ok()
            .and_then(|mut trace| {
                let index = trace
                    .sessions
                    .iter()
                    .position(|(session, _)| *session == id)?;
                let observations = trace.sessions.swap_remove(index).1;
                self.active_traces.fetch_sub(1, Ordering::Release);
                Some(observations)
            })
            .unwrap_or_default();
        AdaptiveSolveTrace { observations }
    }

    /// Log a decision entry as a JSON line.
    ///
    /// Retained by an active trace and/or written to the configured file.
    pub(crate) fn log_decision(&self, entry: DecisionEntry) {
        self.log_decision_with_details(entry, serde_json::Value::Null);
    }

    /// Log a decision entry with route-specific structured details.
    ///
    /// `details` must be a JSON object to be expanded into the top-level log
    /// row. Non-object values are ignored so caller mistakes cannot corrupt the
    /// base decision schema.
    pub(crate) fn log_decision_with_details(
        &self,
        entry: DecisionEntry,
        details: serde_json::Value,
    ) {
        if self.active_traces.load(Ordering::Acquire) != 0 {
            let Ok(mut trace) = self.trace.lock() else {
                return self.write_decision(entry, details);
            };
            // The overwhelmingly common plain-solve path has no active trace:
            // avoid both this lock and constructing/cloning an observation.
            if !trace.sessions.is_empty() {
                let observation = AdaptiveStrategyObservation {
                    stage: entry.stage,
                    gate_result: entry.gate_result,
                    gate_reason: entry.gate_reason.clone(),
                    budget: Duration::try_from_secs_f64(entry.budget_secs)
                        .unwrap_or(Duration::ZERO),
                    elapsed: Duration::try_from_secs_f64(entry.elapsed_secs)
                        .unwrap_or(Duration::ZERO),
                    outcome: AdaptiveStrategyOutcome::from_code(entry.result),
                    lemmas_learned: entry.lemmas_learned,
                    max_frame: entry.max_frame,
                };
                for (_, observations) in &mut trace.sessions {
                    observations.push(observation.clone());
                }
            }
        }

        self.write_decision(entry, details);
    }

    fn write_decision(&self, entry: DecisionEntry, details: serde_json::Value) {
        let mut guard = match self.writer.lock() {
            Ok(g) => g,
            Err(_) => return, // Mutex poisoned — silently skip.
        };
        let writer = match guard.as_mut() {
            Some(w) => w,
            None => return, // Logging disabled — no-op.
        };

        let mut json = serde_json::json!({
            "stage": entry.stage,
            "gate_result": entry.gate_result,
            "gate_reason": entry.gate_reason,
            "budget_secs": entry.budget_secs,
            "elapsed_secs": entry.elapsed_secs,
            "result": entry.result,
            "lemmas_learned": entry.lemmas_learned,
            "max_frame": entry.max_frame,
        });
        if let (Some(base), serde_json::Value::Object(extra)) = (json.as_object_mut(), details) {
            base.extend(extra);
        }

        // Write JSON line. Ignore write errors — logging must not affect solving.
        let _ = writeln!(writer, "{json}");
        let _ = writer.flush();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trace_captures_decisions_without_file_logging() {
        let log = DecisionLog {
            writer: Mutex::new(None),
            trace: Mutex::new(TraceCapture::default()),
            active_traces: AtomicUsize::new(0),
        };
        let session = log.begin_trace();
        log.log_decision(DecisionEntry {
            stage: "specialized_lane",
            gate_result: true,
            gate_reason: "selected by classification".to_string(),
            budget_secs: 2.0,
            elapsed_secs: 1.25,
            result: "timeout",
            lemmas_learned: 3,
            max_frame: 4,
        });

        let trace = session.finish();
        assert_eq!(trace.observations().len(), 1);
        let observation = &trace.observations()[0];
        assert_eq!(observation.stage, "specialized_lane");
        assert_eq!(observation.budget, Duration::from_secs(2));
        assert_eq!(observation.elapsed, Duration::from_millis(1250));
        assert_eq!(observation.outcome, AdaptiveStrategyOutcome::TimedOut);
        assert_eq!(observation.lemmas_learned, 3);
        assert_eq!(observation.max_frame, 4);
    }

    #[test]
    fn trace_session_excludes_decisions_before_and_after_invocation() {
        let log = DecisionLog {
            writer: Mutex::new(None),
            trace: Mutex::new(TraceCapture::default()),
            active_traces: AtomicUsize::new(0),
        };
        let entry = || DecisionEntry {
            stage: "round",
            gate_result: true,
            gate_reason: String::new(),
            budget_secs: 0.0,
            elapsed_secs: 0.0,
            result: "unknown",
            lemmas_learned: 0,
            max_frame: 0,
        };
        log.log_decision(entry());
        let session = log.begin_trace();
        log.log_decision(entry());
        let trace = session.finish();
        log.log_decision(entry());

        assert_eq!(trace.observations().len(), 1);
    }
}
