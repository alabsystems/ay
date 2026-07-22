// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification envelope types: level, summary, and solve details.

use std::collections::BTreeMap;
use std::time::Duration;

use crate::executor_types::{Statistics, UnknownReason};

use super::{ConsumerAcceptanceError, SolveResult, Term, VerifiedSolveResult};

/// Schema identifier for compact solve decision/profile summaries.
pub const AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA: &str = "ay.solve-decision-profile-summary.v1";

/// Schema version for compact solve decision/profile summaries.
pub const AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for model-consumer decisions derived from solve summaries.
pub const AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA: &str =
    "ay.solve-decision-profile-model-consumer.v1";

/// Schema version for model-consumer decisions derived from solve summaries.
pub const AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for raw SMT solve-profile summaries.
pub const AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA: &str = "ay.raw-smt-solve-profile-summary.v1";

/// Schema version for raw SMT solve-profile summaries.
pub const AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Current producer revision for raw SMT solve-profile summaries.
pub const AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION: &str = "raw-smt-solve-profile.v1";

/// Required key/value row fields for raw SMT solve-profile summaries.
pub const AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS: &[&str] = &[
    "schema",
    "schema_version",
    "producer_revision",
    "source",
    "status",
    "reason",
    "solver_path",
    "logic",
    "decision_code",
    "accepted_for_consumer",
    "fail_closed",
    "typed_consumer",
    "timed_out",
    "deadline_exceeded",
    "process_exit_code",
    "unknown_reason_code",
    "unknown_limit_code",
    "verification_level_code",
    "model_validated",
    "consumer_rejection_code",
    "profile_wall_time_ms",
    "profile_conflicts",
    "profile_decisions",
    "profile_propagations",
    "profile_restarts",
    "profile_learned_clause_count",
    "profile_num_assertions",
    "profile_term_count",
];

/// Stable solve decision for downstream evidence consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolveDecision {
    /// The constraints are satisfiable.
    Sat,
    /// The constraints are unsatisfiable.
    Unsat,
    /// The solver could not determine satisfiability.
    Unknown,
}

impl SolveDecision {
    /// Stable snake_case machine code for evidence and routing consumers.
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }

    /// Short human-readable label for the stable machine [`code`](Self::code).
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Sat => "SAT",
            Self::Unsat => "UNSAT",
            Self::Unknown => "Unknown",
        }
    }

    /// Returns true if the decision is SAT.
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    /// Returns true if the decision is UNSAT.
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    /// Returns true if the decision is Unknown.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl From<&SolveResult> for SolveDecision {
    fn from(result: &SolveResult) -> Self {
        match result {
            SolveResult::Sat => Self::Sat,
            SolveResult::Unsat(_) => Self::Unsat,
            SolveResult::Unknown => Self::Unknown,
        }
    }
}

impl From<&VerifiedSolveResult> for SolveDecision {
    fn from(result: &VerifiedSolveResult) -> Self {
        Self::from(result.result())
    }
}

/// The level of runtime verification applied to a solve result.
///
/// AY performs different levels of verification depending on build mode and
/// configuration. Consumers need to know what level of trust to place in a
/// result without inspecting scattered env vars.
///
/// The levels encode two independent axes: debug assertions (compile-time)
/// and proof production (runtime). `FullyVerified` means both are active.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationLevel {
    /// No runtime verification beyond the solver's own correctness.
    /// This is the default in release builds without proof production.
    Trusted,
    /// Debug-assertion checks ran (structural + semantic theory conflict
    /// verification, EUF re-checking, propagation validation).
    /// Active when `cfg(debug_assertions)` is true.
    DebugChecked,
    /// Proof production was enabled: the solver generated a DRAT/LRAT proof
    /// for UNSAT results or validated the model for SAT results.
    ProofChecked,
    /// Both debug-assertion checks and proof production were active.
    /// Maximum internal verification.
    FullyVerified,
}

impl VerificationLevel {
    /// Compute the verification level from the current runtime state.
    ///
    /// Examines `cfg(debug_assertions)` (compile-time) and whether proof
    /// production is enabled (runtime) to determine the level.
    #[must_use]
    pub fn from_state(proofs_enabled: bool) -> Self {
        let debug = cfg!(debug_assertions);
        match (debug, proofs_enabled) {
            (false, false) => Self::Trusted,
            (true, false) => Self::DebugChecked,
            (false, true) => Self::ProofChecked,
            (true, true) => Self::FullyVerified,
        }
    }

    /// Returns true if debug-assertion checks are active.
    #[must_use]
    pub fn has_debug_checks(&self) -> bool {
        matches!(self, Self::DebugChecked | Self::FullyVerified)
    }

    /// Returns true if proof production is active.
    #[must_use]
    pub fn has_proof_checking(&self) -> bool {
        matches!(self, Self::ProofChecked | Self::FullyVerified)
    }

    /// Returns true if this is the minimum trust level (no extra verification).
    #[must_use]
    pub fn is_trusted_only(&self) -> bool {
        matches!(self, Self::Trusted)
    }

    /// Stable snake_case machine code for evidence and routing consumers.
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            Self::Trusted => "trusted",
            Self::DebugChecked => "debug_checked",
            Self::ProofChecked => "proof_checked",
            Self::FullyVerified => "fully_verified",
        }
    }

    /// Short human-readable label for the stable machine [`code`](Self::code).
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Trusted => "Trusted",
            Self::DebugChecked => "Debug checked",
            Self::ProofChecked => "Proof checked",
            Self::FullyVerified => "Fully verified",
        }
    }
}

impl std::fmt::Display for VerificationLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Trusted => write!(f, "trusted"),
            Self::DebugChecked => write!(f, "debug-checked"),
            Self::ProofChecked => write!(f, "proof-checked"),
            Self::FullyVerified => write!(f, "fully-verified"),
        }
    }
}

/// Verification metadata attached to a solve result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct VerificationSummary {
    /// True when `validate_model()` actually ran and passed on this solve call.
    /// False when validation was skipped (deferred, or result was UNSAT/Unknown).
    pub sat_model_validated: bool,
    /// True when an UNSAT result has a proof artifact available.
    pub unsat_proof_available: bool,
    /// Number of internal proof-checker failures recorded for the solve call.
    pub unsat_proof_checker_failures: u64,
    /// Number of assertions independently verified by the model evaluator.
    /// Excludes theory-delegated checks counted in `sat_delegated_checks`.
    pub sat_independent_checks: u64,
    /// Number of assertions accepted via theory-solver delegation
    /// (the theory solver verified consistency during solving).
    pub sat_delegated_checks: u64,
    /// Number of assertions where verification was incomplete or skipped
    /// (SAT fallback, evaluator incompleteness, or uncheckable categories such
    /// as internal helper assertions / quantified assertions).
    /// When > 0 and `sat_model_validated` is false, the result was
    /// degraded from SAT to Unknown due to incomplete evidence.
    pub sat_incomplete_checks: u64,
}

/// Resource consumption from the last solve call.
///
/// Provides memory, term store, and timing metrics captured atomically
/// with the solve result. Callers can use this to monitor solver resource
/// usage without querying separate APIs.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ResourceUsage {
    /// Process RSS (resident set size) in bytes at the time of the solve.
    pub rss_bytes: usize,
    /// Per-instance term memory usage in bytes.
    pub term_bytes: usize,
    /// Number of terms interned in this solver's term store.
    pub term_count: usize,
    /// Number of learned clauses retained at the end of the solve.
    pub learned_clause_count: usize,
    /// Wall-clock time spent in this solve call.
    pub wall_time: Duration,
    /// Which caller-set limit (if any) caused an Unknown result.
    pub limit_hit: Option<LimitKind>,
}

/// Which caller-set limit caused an Unknown result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LimitKind {
    /// Timeout limit was hit.
    Timeout,
    /// Process memory (RSS) limit was hit.
    MemoryLimit,
    /// Per-instance term memory limit was hit.
    TermMemoryLimit,
    /// Learned clause count limit was hit.
    LearnedClauseLimit,
    /// Clause database bytes limit was hit.
    ClauseDbBytesLimit,
    /// Solver was interrupted by another thread.
    Interrupted,
}

impl LimitKind {
    /// Stable snake_case machine code for evidence and routing consumers.
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            Self::Timeout => "timeout",
            Self::MemoryLimit => "memory_limit",
            Self::TermMemoryLimit => "term_memory_limit",
            Self::LearnedClauseLimit => "learned_clause_limit",
            Self::ClauseDbBytesLimit => "clause_db_bytes_limit",
            Self::Interrupted => "interrupted",
        }
    }

    /// Short human-readable label for the stable machine [`code`](Self::code).
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Timeout => "Timeout",
            Self::MemoryLimit => "Memory limit",
            Self::TermMemoryLimit => "Term memory limit",
            Self::LearnedClauseLimit => "Learned clause limit",
            Self::ClauseDbBytesLimit => "Clause DB bytes limit",
            Self::Interrupted => "Interrupted",
        }
    }
}

/// Actionable attribution for an `Unknown` result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct UnknownDiagnostic {
    /// Structured Unknown reason.
    pub reason: UnknownReason,
    /// Broad solver phase responsible for the Unknown, when known.
    pub phase: Option<String>,
    /// Narrow cost center inside the responsible phase, when known.
    pub cost_center: Option<String>,
    /// Human-readable detail suitable for downstream timeout/error messages.
    pub detail: Option<String>,
}

/// Stable Unknown attribution extracted from an atomic solve envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveUnknownSummary {
    /// Structured Unknown reason.
    pub reason: UnknownReason,
    /// Stable reason code from [`UnknownReason::code`].
    pub reason_code: &'static str,
    /// Human-readable reason label from [`UnknownReason::name`].
    pub reason_name: &'static str,
    /// Broad solver phase responsible for Unknown, when known.
    pub phase: Option<String>,
    /// Narrow cost center inside the responsible phase, when known.
    pub cost_center: Option<String>,
    /// Human-readable detail suitable for downstream messages.
    pub detail: Option<String>,
    /// Caller-set limit that caused Unknown, when known.
    pub limit_hit: Option<LimitKind>,
    /// Stable limit code from [`LimitKind::code`], when a limit was hit.
    pub limit_code: Option<&'static str>,
}

/// Compact profile counters extracted from an atomic solve envelope.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveProfileSummary {
    /// Wall-clock solve time in milliseconds.
    pub wall_time_ms: u128,
    /// SAT conflicts.
    pub conflicts: u64,
    /// SAT decisions.
    pub decisions: u64,
    /// SAT propagations.
    pub propagations: u64,
    /// SAT restarts.
    pub restarts: u64,
    /// Learned clauses retained.
    pub learned_clauses: u64,
    /// Theory conflicts.
    pub theory_conflicts: u64,
    /// Theory propagations.
    pub theory_propagations: u64,
    /// Theory Unknown returns.
    pub theory_unknown_count: u64,
    /// Partial clause events.
    pub partial_clause_count: u64,
    /// E-matching rounds completed.
    pub ematching_rounds_completed: u64,
    /// E-matching instances created.
    pub ematching_instances_created: u64,
    /// CEGQI/theory refinement rounds.
    pub refinement_count: u64,
    /// Deterministic solver-work counter exposed under Z3's rlimit-count key.
    pub rlimit_count: u64,
    /// Number of top-level assertions.
    pub num_assertions: u64,
    /// Process RSS bytes at solve completion.
    pub rss_bytes: usize,
    /// Per-solver term-store bytes.
    pub term_bytes: usize,
    /// Number of interned terms.
    pub term_count: usize,
    /// Learned clauses retained at solve completion.
    pub learned_clause_count: usize,
}

/// Compact typed summary for solve decision, Unknown attribution, and profile evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveDecisionProfileSummary {
    /// Summary schema identifier.
    pub schema: &'static str,
    /// Summary schema version.
    pub schema_version: u32,
    /// Stable solve decision.
    pub decision: SolveDecision,
    /// Stable decision code from [`SolveDecision::code`].
    pub decision_code: &'static str,
    /// Human-readable decision label from [`SolveDecision::name`].
    pub decision_name: &'static str,
    /// True when the result passed AY's public consumer acceptance boundary.
    pub accepted_for_consumer: bool,
    /// Stable rejection code when the consumer acceptance boundary rejected.
    pub consumer_rejection_code: Option<&'static str>,
    /// True when SAT model validation ran and passed for this solve.
    pub model_validated: bool,
    /// Runtime verification level applied to this solve.
    pub verification_level: VerificationLevel,
    /// Stable verification level code from [`VerificationLevel::code`].
    pub verification_level_code: &'static str,
    /// Verification/provenance counters for the solve call.
    pub verification: VerificationSummary,
    /// Unknown attribution, populated only for Unknown results with a reason.
    pub unknown: Option<SolveUnknownSummary>,
    /// Stable profile counters for the solve call.
    pub profile: SolveProfileSummary,
}

/// Producer path for a raw SMT solve-profile summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RawSmtSolveProfileSource {
    /// Summary was derived from typed in-process AY solve details.
    TypedAYInternals,
    /// Summary was derived by AY-owned process-output classification.
    RawProcessExecution,
}

impl RawSmtSolveProfileSource {
    /// Return the stable lower-snake-case source code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::TypedAYInternals => "typed_ay_internals",
            Self::RawProcessExecution => "raw_process_execution",
        }
    }
}

/// Availability status for a raw SMT solve-profile summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RawSmtSolveProfileStatus {
    /// The summary is complete and accepted for downstream report use.
    Available,
    /// The summary is present only as a fail-closed rejection.
    Rejected,
}

impl RawSmtSolveProfileStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Available => "available",
            Self::Rejected => "rejected",
        }
    }
}

/// Reason code for a raw SMT solve-profile summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RawSmtSolveProfileReason {
    /// Summary was produced from typed AY internals.
    TypedAYInternals,
    /// Raw process execution produced a SAT/UNSAT solver status.
    RawProcessStatus,
    /// Raw process execution produced Unknown without a caller deadline.
    RawProcessUnknown,
    /// Raw process execution timed out or exceeded its caller deadline.
    RawProcessTimeout,
    /// Raw process execution failed before a trustworthy solver status.
    RawProcessError,
    /// Raw process output did not contain a solver status.
    MissingSolverStatus,
    /// Raw process output was malformed for this summary contract.
    MalformedProcessOutput,
    /// Typed AY internals rejected an unvalidated SAT result.
    RejectedSatConsumerBoundary,
}

impl RawSmtSolveProfileReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::TypedAYInternals => "typed_ay_internals",
            Self::RawProcessStatus => "raw_process_status",
            Self::RawProcessUnknown => "raw_process_unknown",
            Self::RawProcessTimeout => "raw_process_timeout",
            Self::RawProcessError => "raw_process_error",
            Self::MissingSolverStatus => "missing_solver_status",
            Self::MalformedProcessOutput => "malformed_process_output",
            Self::RejectedSatConsumerBoundary => "rejected_sat_consumer_boundary",
        }
    }
}

/// Owned metadata captured from an external raw SMT process invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct RawSmtProcessSolveProfileInput {
    /// Path or command label used to invoke the solver.
    pub solver_path: String,
    /// SMT-LIB logic, when known.
    pub logic: Option<String>,
    /// Captured process stdout.
    pub stdout: String,
    /// Captured process stderr.
    pub stderr: String,
    /// Process exit code, or `None` when the process was killed or timed out.
    pub exit_code: Option<i32>,
    /// Wall-clock process time in milliseconds.
    pub wall_time_ms: u128,
    /// Whether the process-level timeout fired.
    pub timed_out: bool,
    /// Whether an outer caller deadline was exceeded.
    pub deadline_exceeded: bool,
}

impl RawSmtProcessSolveProfileInput {
    /// Build raw process metadata with no timeout/deadline flags set.
    #[must_use]
    pub fn new(
        solver_path: &str,
        logic: Option<&str>,
        stdout: &str,
        stderr: &str,
        exit_code: Option<i32>,
    ) -> Self {
        Self {
            solver_path: solver_path.to_string(),
            logic: logic.map(str::to_string),
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
            exit_code,
            wall_time_ms: 0,
            timed_out: false,
            deadline_exceeded: false,
        }
    }

    /// Attach wall-clock process time in milliseconds.
    #[must_use]
    pub fn with_wall_time_ms(mut self, wall_time_ms: u128) -> Self {
        self.wall_time_ms = wall_time_ms;
        self
    }

    /// Attach the process-timeout flag.
    #[must_use]
    pub fn with_timed_out(mut self, timed_out: bool) -> Self {
        self.timed_out = timed_out;
        self
    }

    /// Attach the outer-deadline flag.
    #[must_use]
    pub fn with_deadline_exceeded(mut self, deadline_exceeded: bool) -> Self {
        self.deadline_exceeded = deadline_exceeded;
        self
    }
}

/// AY-owned raw SMT solve-profile summary for downstream process reports.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct RawSmtSolveProfileSummary {
    /// Summary schema identifier.
    pub schema: &'static str,
    /// Summary schema version.
    pub schema_version: u32,
    /// Producer revision that validators use to reject stale rows.
    pub producer_revision: &'static str,
    /// Producer path for this summary.
    pub source: RawSmtSolveProfileSource,
    /// Stable source code.
    pub source_code: &'static str,
    /// Summary availability status.
    pub status: RawSmtSolveProfileStatus,
    /// Stable status code.
    pub status_code: &'static str,
    /// Summary reason.
    pub reason: RawSmtSolveProfileReason,
    /// Stable reason code.
    pub reason_code: &'static str,
    /// Path or command label used to invoke the solver.
    pub solver_path: String,
    /// SMT-LIB logic, when known.
    pub logic: Option<String>,
    /// Stable solve decision, when trustworthy.
    pub decision: Option<SolveDecision>,
    /// Stable solve decision code, or `none` when absent.
    pub decision_code: &'static str,
    /// Whether downstream report consumers may use this summary.
    pub accepted_for_consumer: bool,
    /// Whether rejection is fail-closed.
    pub fail_closed: bool,
    /// Whether the summary came from typed in-process AY internals.
    pub typed_consumer: bool,
    /// Whether a process or solver timeout was observed.
    pub timed_out: bool,
    /// Whether an outer caller deadline was exceeded.
    pub deadline_exceeded: bool,
    /// Raw process exit code, when available.
    pub process_exit_code: Option<i32>,
    /// Stable Unknown reason code, when present.
    pub unknown_reason_code: Option<&'static str>,
    /// Stable limit code, when present.
    pub unknown_limit_code: Option<&'static str>,
    /// Stable verification level code, when typed internals are available.
    pub verification_level_code: Option<&'static str>,
    /// Whether SAT model validation ran and passed.
    pub model_validated: bool,
    /// Stable consumer rejection code, when present.
    pub consumer_rejection_code: Option<&'static str>,
    /// Stable profile counters for the solve or process call.
    pub profile: SolveProfileSummary,
}

/// Validation status for forwarded raw SMT solve-profile rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RawSmtSolveProfileValidationStatus {
    /// Rows are accepted for downstream report use.
    Accepted,
    /// Rows are rejected and must fail closed.
    Rejected,
}

impl RawSmtSolveProfileValidationStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
        }
    }
}

/// Validation reason for forwarded raw SMT solve-profile rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RawSmtSolveProfileValidationReason {
    /// Rows are accepted.
    Accepted,
    /// One or more required rows are missing.
    MissingRequiredRow,
    /// One or more keys are duplicated.
    DuplicateRow,
    /// One or more rows are malformed.
    MalformedRow,
    /// The schema identifier is not current.
    SchemaMismatch,
    /// The schema version is not current.
    SchemaVersionMismatch,
    /// The producer revision is stale.
    StaleRows,
    /// Rejected rows attempted to remain fail-open.
    FailOpenRows,
}

impl RawSmtSolveProfileValidationReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::MissingRequiredRow => "missing_required_row",
            Self::DuplicateRow => "duplicate_row",
            Self::MalformedRow => "malformed_row",
            Self::SchemaMismatch => "schema_mismatch",
            Self::SchemaVersionMismatch => "schema_version_mismatch",
            Self::StaleRows => "stale_rows",
            Self::FailOpenRows => "fail_open_rows",
        }
    }
}

/// One validation issue for forwarded raw SMT solve-profile rows.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct RawSmtSolveProfileValidationIssue {
    /// Validation reason.
    pub reason: RawSmtSolveProfileValidationReason,
    /// Stable validation reason code.
    pub reason_code: &'static str,
    /// Field or row key involved in the issue.
    pub field: String,
    /// Expected value, when applicable.
    pub expected: Option<String>,
    /// Actual value, when applicable.
    pub actual: Option<String>,
}

impl RawSmtSolveProfileValidationIssue {
    fn new(
        reason: RawSmtSolveProfileValidationReason,
        field: impl Into<String>,
        expected: Option<String>,
        actual: Option<String>,
    ) -> Self {
        Self {
            reason,
            reason_code: reason.code(),
            field: field.into(),
            expected,
            actual,
        }
    }
}

/// Fail-closed validation report for forwarded raw SMT solve-profile rows.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct RawSmtSolveProfileValidationReport {
    /// Validation report schema identifier.
    pub schema: &'static str,
    /// Validation report schema version.
    pub schema_version: u32,
    /// Validation status.
    pub status: RawSmtSolveProfileValidationStatus,
    /// Stable validation status code.
    pub status_code: &'static str,
    /// Validation reason.
    pub reason: RawSmtSolveProfileValidationReason,
    /// Stable validation reason code.
    pub reason_code: &'static str,
    /// Whether rows are accepted for downstream report use.
    pub accepted_for_consumer: bool,
    /// Whether rejection is fail-closed.
    pub fail_closed: bool,
    /// Validation issues. Empty when accepted.
    pub issues: Vec<RawSmtSolveProfileValidationIssue>,
}

impl RawSmtSolveProfileValidationReport {
    /// Return true when the forwarded rows are accepted.
    #[must_use]
    pub fn accepted(&self) -> bool {
        self.accepted_for_consumer
    }

    /// Render this validation report as stable JSON.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "issues": self.issues.iter().map(|issue| serde_json::json!({
                "reason": issue.reason_code,
                "field": issue.field,
                "expected": issue.expected.as_deref(),
                "actual": issue.actual.as_deref(),
            })).collect::<Vec<_>>(),
        })
    }
}

/// Typed model-consumer status derived from a solve decision/profile summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolveDecisionProfileModelConsumerStatus {
    /// The summary admits model consumption by downstream callers.
    Accepted,
    /// The summary must not be used for model consumption.
    Rejected,
}

impl SolveDecisionProfileModelConsumerStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
        }
    }
}

/// Typed model-consumer reason derived from a solve decision/profile summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolveDecisionProfileModelConsumerReason {
    /// The SAT result passed the consumer boundary and has a validated model.
    Accepted,
    /// The solve decision is not SAT, so there is no model to consume.
    NonSatDecision,
    /// The SAT result failed AY's public consumer boundary.
    ConsumerRejected,
    /// The summary did not report a validated SAT model.
    ModelNotValidated,
}

impl SolveDecisionProfileModelConsumerReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::NonSatDecision => "non_sat_decision",
            Self::ConsumerRejected => "consumer_rejected",
            Self::ModelNotValidated => "model_not_validated",
        }
    }
}

/// AY-owned model-consumer decision for downstream model enumeration/extraction.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolveDecisionProfileModelConsumerDecision {
    /// Decision schema identifier.
    pub schema: &'static str,
    /// Decision schema version.
    pub schema_version: u32,
    /// Typed model-consumer status.
    pub status: SolveDecisionProfileModelConsumerStatus,
    /// Stable model-consumer status code.
    pub status_code: &'static str,
    /// Typed model-consumer reason.
    pub reason: SolveDecisionProfileModelConsumerReason,
    /// Stable model-consumer reason code.
    pub reason_code: &'static str,
    /// Whether downstream callers may consume the model for this solve.
    pub accepted_for_consumer: bool,
    /// Whether rejection remains fail-closed.
    pub fail_closed: bool,
    /// Stable solve decision.
    pub decision: SolveDecision,
    /// Stable solve decision code.
    pub decision_code: &'static str,
    /// Whether the solve summary passed AY's public consumer boundary.
    pub solve_accepted_for_consumer: bool,
    /// Stable rejection code from the solve consumer boundary, when present.
    pub solve_consumer_rejection_code: Option<&'static str>,
    /// Whether SAT model validation ran and passed for this solve.
    pub model_validated: bool,
    /// Stable verification level code from the source summary.
    pub verification_level_code: &'static str,
}

impl SolveDecisionProfileModelConsumerDecision {
    fn from_summary(summary: &SolveDecisionProfileSummary) -> Self {
        let reason = if !summary.decision.is_sat() {
            SolveDecisionProfileModelConsumerReason::NonSatDecision
        } else if !summary.accepted_for_consumer {
            SolveDecisionProfileModelConsumerReason::ConsumerRejected
        } else if !summary.model_validated {
            SolveDecisionProfileModelConsumerReason::ModelNotValidated
        } else {
            SolveDecisionProfileModelConsumerReason::Accepted
        };
        let accepted_for_consumer =
            matches!(reason, SolveDecisionProfileModelConsumerReason::Accepted);
        let status = if accepted_for_consumer {
            SolveDecisionProfileModelConsumerStatus::Accepted
        } else {
            SolveDecisionProfileModelConsumerStatus::Rejected
        };

        Self {
            schema: AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
            schema_version: AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
            status,
            status_code: status.code(),
            reason,
            reason_code: reason.code(),
            accepted_for_consumer,
            fail_closed: !accepted_for_consumer,
            decision: summary.decision,
            decision_code: summary.decision_code,
            solve_accepted_for_consumer: summary.accepted_for_consumer,
            solve_consumer_rejection_code: summary.consumer_rejection_code,
            model_validated: summary.model_validated,
            verification_level_code: summary.verification_level_code,
        }
    }

    /// Render this decision as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "decision": self.decision_code,
            "solve_accepted_for_consumer": self.solve_accepted_for_consumer,
            "solve_consumer_rejection_code": self.solve_consumer_rejection_code,
            "model_validated": self.model_validated,
            "verification_level_code": self.verification_level_code,
        })
    }
}

/// Atomic solve envelope containing result, diagnostics, and verification provenance.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use]
pub struct SolveDetails {
    /// SAT/UNSAT/UNKNOWN result — carries verification provenance.
    /// Part of #5750: Phase 5 escape hatch sealing.
    pub result: VerifiedSolveResult,
    /// Solver statistics captured from the same solve call.
    pub statistics: Statistics,
    /// Structured reason for Unknown, when available.
    pub unknown_reason: Option<UnknownReason>,
    /// Responsible phase/cost-center attribution for Unknown, when available.
    pub unknown_diagnostic: Option<UnknownDiagnostic>,
    /// Executor error detail when `unknown_reason` is `InternalError`.
    ///
    /// Captures the underlying error message from the same solve call,
    /// eliminating the need for a follow-up `get_executor_error()` call.
    pub executor_error: Option<String>,
    /// Verification/provenance summary for the solve call.
    pub verification: VerificationSummary,
    /// Level of runtime verification applied to this solve result.
    pub verification_level: VerificationLevel,
    /// Resource consumption from this solve call.
    pub resource_usage: ResourceUsage,
}

impl SolveDetails {
    /// Accept this solve envelope at a consumer-facing boundary.
    ///
    /// This keeps the low-level diagnostic result intact while centralizing the
    /// public policy for when SAT may be surfaced as a trusted success.
    #[must_use = "consumer boundaries must check whether SAT is acceptable before surfacing a model"]
    pub fn accept_for_consumer(&self) -> Result<&SolveResult, ConsumerAcceptanceError> {
        self.result.accept_for_consumer()
    }

    /// Return compact profile counters from this solve envelope.
    #[must_use]
    pub fn profile_summary(&self) -> SolveProfileSummary {
        SolveProfileSummary::from_details(self)
    }

    /// Return stable Unknown attribution from this solve envelope, when present.
    #[must_use]
    pub fn unknown_summary(&self) -> Option<SolveUnknownSummary> {
        SolveUnknownSummary::from_details(self)
    }

    /// Return compact typed decision, Unknown, and profile evidence.
    #[must_use]
    pub fn decision_profile_summary(&self) -> SolveDecisionProfileSummary {
        SolveDecisionProfileSummary::from_details(self)
    }
}

/// Atomic solve envelope for assumption-based solving.
///
/// Wraps `SolveDetails` with the unsat-assumption subset from the same solve
/// call, eliminating the split contract of solving first then reading
/// `get_unsat_assumptions()` separately.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AssumptionSolveDetails {
    /// The base solve envelope (result, statistics, verification, etc.).
    pub solve: SolveDetails,
    /// The subset of assumptions that caused UNSAT, captured from the same
    /// solve call. `None` when the result is not UNSAT or when no assumptions
    /// were provided.
    pub unsat_assumptions: Option<Vec<Term>>,
}

impl AssumptionSolveDetails {
    /// Accept this solve envelope at a consumer-facing boundary.
    #[must_use = "consumer boundaries must check whether SAT is acceptable before surfacing a model"]
    pub fn accept_for_consumer(&self) -> Result<&SolveResult, ConsumerAcceptanceError> {
        self.solve.accept_for_consumer()
    }

    /// Return compact profile counters from this assumption solve envelope.
    #[must_use]
    pub fn profile_summary(&self) -> SolveProfileSummary {
        self.solve.profile_summary()
    }

    /// Return stable Unknown attribution from this assumption solve envelope, when present.
    #[must_use]
    pub fn unknown_summary(&self) -> Option<SolveUnknownSummary> {
        self.solve.unknown_summary()
    }

    /// Return compact typed decision, Unknown, and profile evidence.
    #[must_use]
    pub fn decision_profile_summary(&self) -> SolveDecisionProfileSummary {
        self.solve.decision_profile_summary()
    }
}

impl SolveUnknownSummary {
    /// Build stable Unknown attribution from an atomic solve envelope.
    #[must_use]
    pub fn from_details(details: &SolveDetails) -> Option<Self> {
        let diagnostic = details.unknown_diagnostic.as_ref();
        let reason = details
            .unknown_reason
            .or_else(|| diagnostic.map(|diagnostic| diagnostic.reason))?;
        let limit_hit = details.resource_usage.limit_hit;

        Some(Self {
            reason,
            reason_code: reason.code(),
            reason_name: reason.name(),
            phase: diagnostic.and_then(|diagnostic| diagnostic.phase.clone()),
            cost_center: diagnostic.and_then(|diagnostic| diagnostic.cost_center.clone()),
            detail: diagnostic.and_then(|diagnostic| diagnostic.detail.clone()),
            limit_hit,
            limit_code: limit_hit.map(|limit| limit.code()),
        })
    }
}

impl SolveProfileSummary {
    /// Build stable profile counters from an atomic solve envelope.
    #[must_use]
    pub fn from_details(details: &SolveDetails) -> Self {
        let statistics = &details.statistics;
        let resource = &details.resource_usage;

        Self {
            wall_time_ms: resource.wall_time.as_millis(),
            conflicts: statistics.conflicts,
            decisions: statistics.decisions,
            propagations: statistics.propagations,
            restarts: statistics.restarts,
            learned_clauses: statistics.learned_clauses,
            theory_conflicts: statistics.theory_conflicts,
            theory_propagations: statistics.theory_propagations,
            theory_unknown_count: statistics.theory_unknown_count,
            partial_clause_count: statistics.partial_clause_count,
            ematching_rounds_completed: statistics.ematching_rounds_completed,
            ematching_instances_created: statistics.ematching_instances_created,
            refinement_count: statistics.refinement_count,
            rlimit_count: statistics.rlimit_count,
            num_assertions: statistics.num_assertions,
            rss_bytes: resource.rss_bytes,
            term_bytes: resource.term_bytes,
            term_count: resource.term_count,
            learned_clause_count: resource.learned_clause_count,
        }
    }
}

impl SolveDecisionProfileSummary {
    /// Build compact typed decision, Unknown, and profile evidence from a solve envelope.
    #[must_use]
    pub fn from_details(details: &SolveDetails) -> Self {
        let decision = SolveDecision::from(&details.result);
        let consumer_acceptance = details.accept_for_consumer();
        let (accepted_for_consumer, consumer_rejection_code) = match consumer_acceptance {
            Ok(_) => (true, None),
            Err(error) => (false, Some(consumer_acceptance_error_code(error))),
        };

        Self {
            schema: AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA,
            schema_version: AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION,
            decision,
            decision_code: decision.code(),
            decision_name: decision.name(),
            accepted_for_consumer,
            consumer_rejection_code,
            model_validated: details.result.was_model_validated(),
            verification_level: details.verification_level,
            verification_level_code: details.verification_level.code(),
            verification: details.verification,
            unknown: details.unknown_summary(),
            profile: details.profile_summary(),
        }
    }

    /// Return the AY-owned model-consumer decision for this solve summary.
    ///
    /// Downstream model enumeration/extraction paths should use this helper
    /// instead of reimplementing the policy from summary fields. A model is
    /// accepted only for SAT decisions that passed the public consumer boundary
    /// and report a validated model.
    #[must_use]
    pub fn model_consumer_decision(&self) -> SolveDecisionProfileModelConsumerDecision {
        SolveDecisionProfileModelConsumerDecision::from_summary(self)
    }

    /// Return true when this summary admits downstream model consumption.
    #[must_use]
    pub fn accepts_model_for_consumer(&self) -> bool {
        self.model_consumer_decision().accepted_for_consumer
    }

    /// Render the model-consumer decision as stable JSON for evidence sinks.
    #[must_use]
    pub fn model_consumer_decision_json(&self) -> serde_json::Value {
        self.model_consumer_decision().to_json_value()
    }
}

impl RawSmtSolveProfileSummary {
    /// Build a raw SMT solve-profile summary from typed AY solve details.
    #[must_use]
    pub fn from_typed_details(
        solver_path: &str,
        logic: Option<&str>,
        details: &SolveDetails,
    ) -> Self {
        Self::from_typed_summary(solver_path, logic, &details.decision_profile_summary())
    }

    /// Build a raw SMT solve-profile summary from a typed AY solve summary.
    #[must_use]
    pub fn from_typed_summary(
        solver_path: &str,
        logic: Option<&str>,
        summary: &SolveDecisionProfileSummary,
    ) -> Self {
        let rejected_sat = summary.decision.is_sat() && !summary.accepted_for_consumer;
        let status = if rejected_sat {
            RawSmtSolveProfileStatus::Rejected
        } else {
            RawSmtSolveProfileStatus::Available
        };
        let reason = if rejected_sat {
            RawSmtSolveProfileReason::RejectedSatConsumerBoundary
        } else {
            RawSmtSolveProfileReason::TypedAYInternals
        };
        let unknown = summary.unknown.as_ref();

        Self {
            schema: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
            schema_version: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
            producer_revision: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
            source: RawSmtSolveProfileSource::TypedAYInternals,
            source_code: RawSmtSolveProfileSource::TypedAYInternals.code(),
            status,
            status_code: status.code(),
            reason,
            reason_code: reason.code(),
            solver_path: solver_path.to_string(),
            logic: logic.map(str::to_string),
            decision: Some(summary.decision),
            decision_code: summary.decision_code,
            accepted_for_consumer: summary.accepted_for_consumer && !rejected_sat,
            fail_closed: rejected_sat,
            typed_consumer: true,
            timed_out: unknown
                .and_then(|unknown| unknown.limit_hit)
                .is_some_and(|limit| limit == LimitKind::Timeout),
            deadline_exceeded: false,
            process_exit_code: None,
            unknown_reason_code: unknown.map(|unknown| unknown.reason_code),
            unknown_limit_code: unknown.and_then(|unknown| unknown.limit_code),
            verification_level_code: Some(summary.verification_level_code),
            model_validated: summary.model_validated,
            consumer_rejection_code: summary.consumer_rejection_code,
            profile: summary.profile,
        }
    }

    /// Build a raw SMT solve-profile summary from external process metadata.
    #[must_use]
    pub fn from_process(input: RawSmtProcessSolveProfileInput) -> Self {
        let decision = raw_smt_process_decision(&input.stdout);
        let process_ok = input.exit_code == Some(0);
        let timed_out_or_deadline = input.timed_out || input.deadline_exceeded;
        let (status, reason, accepted_for_consumer, fail_closed) =
            if timed_out_or_deadline && !matches!(decision, Some(SolveDecision::Unknown)) {
                (
                    RawSmtSolveProfileStatus::Rejected,
                    RawSmtSolveProfileReason::RawProcessTimeout,
                    false,
                    true,
                )
            } else if !process_ok {
                (
                    RawSmtSolveProfileStatus::Rejected,
                    if timed_out_or_deadline {
                        RawSmtSolveProfileReason::RawProcessTimeout
                    } else {
                        RawSmtSolveProfileReason::RawProcessError
                    },
                    false,
                    true,
                )
            } else if let Some(decision) = decision {
                (
                    RawSmtSolveProfileStatus::Available,
                    if decision.is_unknown() {
                        if timed_out_or_deadline {
                            RawSmtSolveProfileReason::RawProcessTimeout
                        } else {
                            RawSmtSolveProfileReason::RawProcessUnknown
                        }
                    } else {
                        RawSmtSolveProfileReason::RawProcessStatus
                    },
                    true,
                    false,
                )
            } else {
                (
                    RawSmtSolveProfileStatus::Rejected,
                    RawSmtSolveProfileReason::MissingSolverStatus,
                    false,
                    true,
                )
            };
        let decision_code = decision.map_or("none", |decision| decision.code());
        let unknown_reason_code = decision
            .is_some_and(|decision| decision.is_unknown())
            .then_some(if timed_out_or_deadline {
                UnknownReason::Timeout.code()
            } else {
                UnknownReason::Unknown.code()
            });
        let unknown_limit_code = timed_out_or_deadline.then_some(LimitKind::Timeout.code());
        let profile = SolveProfileSummary {
            wall_time_ms: input.wall_time_ms,
            ..SolveProfileSummary::default()
        };

        Self {
            schema: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
            schema_version: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
            producer_revision: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
            source: RawSmtSolveProfileSource::RawProcessExecution,
            source_code: RawSmtSolveProfileSource::RawProcessExecution.code(),
            status,
            status_code: status.code(),
            reason,
            reason_code: reason.code(),
            solver_path: input.solver_path,
            logic: input.logic,
            decision,
            decision_code,
            accepted_for_consumer,
            fail_closed,
            typed_consumer: false,
            timed_out: input.timed_out,
            deadline_exceeded: input.deadline_exceeded,
            process_exit_code: input.exit_code,
            unknown_reason_code,
            unknown_limit_code,
            verification_level_code: None,
            model_validated: false,
            consumer_rejection_code: None,
            profile,
        }
    }

    /// Render this summary as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "producer_revision": self.producer_revision,
            "source": self.source_code,
            "status": self.status_code,
            "reason": self.reason_code,
            "solver_path": self.solver_path,
            "logic": self.logic,
            "decision": self.decision_code,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "typed_consumer": self.typed_consumer,
            "timed_out": self.timed_out,
            "deadline_exceeded": self.deadline_exceeded,
            "process_exit_code": self.process_exit_code,
            "unknown_reason_code": self.unknown_reason_code,
            "unknown_limit_code": self.unknown_limit_code,
            "verification_level_code": self.verification_level_code,
            "model_validated": self.model_validated,
            "consumer_rejection_code": self.consumer_rejection_code,
            "profile": {
                "wall_time_ms": u128_to_json(self.profile.wall_time_ms),
                "conflicts": self.profile.conflicts,
                "decisions": self.profile.decisions,
                "propagations": self.profile.propagations,
                "restarts": self.profile.restarts,
                "learned_clause_count": self.profile.learned_clause_count,
                "num_assertions": self.profile.num_assertions,
                "term_count": self.profile.term_count,
            },
        })
    }

    /// Render this summary as deterministic key/value rows.
    #[must_use]
    pub fn to_key_value_rows(&self) -> Vec<(String, String)> {
        vec![
            ("schema".to_string(), self.schema.to_string()),
            (
                "schema_version".to_string(),
                self.schema_version.to_string(),
            ),
            (
                "producer_revision".to_string(),
                self.producer_revision.to_string(),
            ),
            ("source".to_string(), self.source_code.to_string()),
            ("status".to_string(), self.status_code.to_string()),
            ("reason".to_string(), self.reason_code.to_string()),
            ("solver_path".to_string(), self.solver_path.clone()),
            (
                "logic".to_string(),
                self.logic.as_deref().unwrap_or("none").to_string(),
            ),
            ("decision_code".to_string(), self.decision_code.to_string()),
            (
                "accepted_for_consumer".to_string(),
                self.accepted_for_consumer.to_string(),
            ),
            ("fail_closed".to_string(), self.fail_closed.to_string()),
            (
                "typed_consumer".to_string(),
                self.typed_consumer.to_string(),
            ),
            ("timed_out".to_string(), self.timed_out.to_string()),
            (
                "deadline_exceeded".to_string(),
                self.deadline_exceeded.to_string(),
            ),
            (
                "process_exit_code".to_string(),
                self.process_exit_code
                    .map_or_else(|| "none".to_string(), |code| code.to_string()),
            ),
            (
                "unknown_reason_code".to_string(),
                self.unknown_reason_code.unwrap_or("none").to_string(),
            ),
            (
                "unknown_limit_code".to_string(),
                self.unknown_limit_code.unwrap_or("none").to_string(),
            ),
            (
                "verification_level_code".to_string(),
                self.verification_level_code.unwrap_or("none").to_string(),
            ),
            (
                "model_validated".to_string(),
                self.model_validated.to_string(),
            ),
            (
                "consumer_rejection_code".to_string(),
                self.consumer_rejection_code.unwrap_or("none").to_string(),
            ),
            (
                "profile_wall_time_ms".to_string(),
                self.profile.wall_time_ms.to_string(),
            ),
            (
                "profile_conflicts".to_string(),
                self.profile.conflicts.to_string(),
            ),
            (
                "profile_decisions".to_string(),
                self.profile.decisions.to_string(),
            ),
            (
                "profile_propagations".to_string(),
                self.profile.propagations.to_string(),
            ),
            (
                "profile_restarts".to_string(),
                self.profile.restarts.to_string(),
            ),
            (
                "profile_learned_clause_count".to_string(),
                self.profile.learned_clause_count.to_string(),
            ),
            (
                "profile_num_assertions".to_string(),
                self.profile.num_assertions.to_string(),
            ),
            (
                "profile_term_count".to_string(),
                self.profile.term_count.to_string(),
            ),
        ]
    }

    /// Render this summary as stable line-oriented diagnostics.
    #[must_use]
    pub fn to_text_lines(&self) -> Vec<String> {
        self.to_key_value_rows()
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }
}

/// Build a raw SMT solve-profile summary from typed AY solve details.
#[must_use]
pub fn raw_smt_solve_profile_summary_from_typed_details(
    solver_path: &str,
    logic: Option<&str>,
    details: &SolveDetails,
) -> RawSmtSolveProfileSummary {
    RawSmtSolveProfileSummary::from_typed_details(solver_path, logic, details)
}

/// Build a raw SMT solve-profile summary from a typed AY solve summary.
#[must_use]
pub fn raw_smt_solve_profile_summary_from_typed_summary(
    solver_path: &str,
    logic: Option<&str>,
    summary: &SolveDecisionProfileSummary,
) -> RawSmtSolveProfileSummary {
    RawSmtSolveProfileSummary::from_typed_summary(solver_path, logic, summary)
}

/// Build a raw SMT solve-profile summary from external process metadata.
#[must_use]
pub fn raw_smt_solve_profile_summary_from_process(
    input: RawSmtProcessSolveProfileInput,
) -> RawSmtSolveProfileSummary {
    RawSmtSolveProfileSummary::from_process(input)
}

/// Validate a raw SMT solve-profile summary by round-tripping its key/value rows.
#[must_use]
pub fn validate_raw_smt_solve_profile_summary(
    summary: &RawSmtSolveProfileSummary,
) -> RawSmtSolveProfileValidationReport {
    validate_raw_smt_solve_profile_summary_key_value_rows(&summary.to_key_value_rows())
}

/// Validate forwarded raw SMT solve-profile key/value rows.
#[must_use]
pub fn validate_raw_smt_solve_profile_summary_key_value_rows(
    rows: &[(String, String)],
) -> RawSmtSolveProfileValidationReport {
    validate_raw_smt_solve_profile_rows(rows, Vec::new())
}

/// Validate forwarded raw SMT solve-profile text lines.
#[must_use]
pub fn validate_raw_smt_solve_profile_summary_text_lines(
    lines: &[String],
) -> RawSmtSolveProfileValidationReport {
    let mut rows = Vec::with_capacity(lines.len());
    let mut issues = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        match line.split_once('=') {
            Some((key, value)) if !key.trim().is_empty() => {
                rows.push((key.to_string(), value.to_string()));
            }
            _ => issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MalformedRow,
                format!("line_{index}"),
                Some("key=value".to_string()),
                Some(line.clone()),
            )),
        }
    }
    validate_raw_smt_solve_profile_rows(&rows, issues)
}

fn consumer_acceptance_error_code(error: ConsumerAcceptanceError) -> &'static str {
    match error {
        ConsumerAcceptanceError::SatModelNotValidated => "sat_model_not_validated",
    }
}

fn raw_smt_process_decision(stdout: &str) -> Option<SolveDecision> {
    stdout.lines().find_map(|line| match line.trim() {
        "sat" => Some(SolveDecision::Sat),
        "unsat" => Some(SolveDecision::Unsat),
        "unknown" => Some(SolveDecision::Unknown),
        _ => None,
    })
}

fn validate_raw_smt_solve_profile_rows(
    rows: &[(String, String)],
    mut issues: Vec<RawSmtSolveProfileValidationIssue>,
) -> RawSmtSolveProfileValidationReport {
    let mut by_key = BTreeMap::new();
    for (key, value) in rows {
        if key.trim().is_empty() || key.chars().any(char::is_whitespace) {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MalformedRow,
                key.clone(),
                Some("non-empty key without whitespace".to_string()),
                Some(key.clone()),
            ));
            continue;
        }
        if by_key.insert(key.as_str(), value.as_str()).is_some() {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::DuplicateRow,
                key.clone(),
                None,
                Some(value.clone()),
            ));
        }
    }

    for required in AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS {
        if !by_key.contains_key(required) {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MissingRequiredRow,
                *required,
                Some("present".to_string()),
                None,
            ));
        }
    }

    validate_expected_row(
        &by_key,
        &mut issues,
        "schema",
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
        RawSmtSolveProfileValidationReason::SchemaMismatch,
    );
    validate_expected_row(
        &by_key,
        &mut issues,
        "schema_version",
        &AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION.to_string(),
        RawSmtSolveProfileValidationReason::SchemaVersionMismatch,
    );
    validate_expected_row(
        &by_key,
        &mut issues,
        "producer_revision",
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
        RawSmtSolveProfileValidationReason::StaleRows,
    );

    for field in [
        "accepted_for_consumer",
        "fail_closed",
        "typed_consumer",
        "timed_out",
        "deadline_exceeded",
        "model_validated",
    ] {
        let _ = parse_bool_row(&by_key, &mut issues, field);
    }
    for field in [
        "profile_wall_time_ms",
        "profile_conflicts",
        "profile_decisions",
        "profile_propagations",
        "profile_restarts",
        "profile_learned_clause_count",
        "profile_num_assertions",
        "profile_term_count",
    ] {
        let _ = parse_u128_row(&by_key, &mut issues, field);
    }
    if let Some(value) = by_key.get("process_exit_code") {
        if *value != "none" && value.parse::<i32>().is_err() {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MalformedRow,
                "process_exit_code",
                Some("integer or none".to_string()),
                Some((*value).to_string()),
            ));
        }
    }

    validate_known_code(
        &by_key,
        &mut issues,
        "source",
        &[
            RawSmtSolveProfileSource::TypedAYInternals.code(),
            RawSmtSolveProfileSource::RawProcessExecution.code(),
        ],
    );
    validate_known_code(
        &by_key,
        &mut issues,
        "status",
        &[
            RawSmtSolveProfileStatus::Available.code(),
            RawSmtSolveProfileStatus::Rejected.code(),
        ],
    );
    validate_known_code(
        &by_key,
        &mut issues,
        "reason",
        &[
            RawSmtSolveProfileReason::TypedAYInternals.code(),
            RawSmtSolveProfileReason::RawProcessStatus.code(),
            RawSmtSolveProfileReason::RawProcessUnknown.code(),
            RawSmtSolveProfileReason::RawProcessTimeout.code(),
            RawSmtSolveProfileReason::RawProcessError.code(),
            RawSmtSolveProfileReason::MissingSolverStatus.code(),
            RawSmtSolveProfileReason::MalformedProcessOutput.code(),
            RawSmtSolveProfileReason::RejectedSatConsumerBoundary.code(),
        ],
    );
    validate_known_code(
        &by_key,
        &mut issues,
        "decision_code",
        &["sat", "unsat", "unknown", "none"],
    );

    validate_raw_smt_fail_closed_policy(&by_key, &mut issues);
    raw_smt_validation_report(issues)
}

fn validate_expected_row(
    rows: &BTreeMap<&str, &str>,
    issues: &mut Vec<RawSmtSolveProfileValidationIssue>,
    field: &'static str,
    expected: &str,
    reason: RawSmtSolveProfileValidationReason,
) {
    if let Some(actual) = rows.get(field) {
        if *actual != expected {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                reason,
                field,
                Some(expected.to_string()),
                Some((*actual).to_string()),
            ));
        }
    }
}

fn validate_known_code(
    rows: &BTreeMap<&str, &str>,
    issues: &mut Vec<RawSmtSolveProfileValidationIssue>,
    field: &'static str,
    accepted: &[&str],
) {
    if let Some(actual) = rows.get(field) {
        if !accepted.contains(actual) {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MalformedRow,
                field,
                Some(accepted.join(",")),
                Some((*actual).to_string()),
            ));
        }
    }
}

fn parse_bool_row(
    rows: &BTreeMap<&str, &str>,
    issues: &mut Vec<RawSmtSolveProfileValidationIssue>,
    field: &'static str,
) -> Option<bool> {
    let value = *rows.get(field)?;
    match value {
        "true" => Some(true),
        "false" => Some(false),
        _ => {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MalformedRow,
                field,
                Some("true or false".to_string()),
                Some(value.to_string()),
            ));
            None
        }
    }
}

fn parse_u128_row(
    rows: &BTreeMap<&str, &str>,
    issues: &mut Vec<RawSmtSolveProfileValidationIssue>,
    field: &'static str,
) -> Option<u128> {
    let value = *rows.get(field)?;
    match value.parse::<u128>() {
        Ok(value) => Some(value),
        Err(_) => {
            issues.push(RawSmtSolveProfileValidationIssue::new(
                RawSmtSolveProfileValidationReason::MalformedRow,
                field,
                Some("unsigned integer".to_string()),
                Some(value.to_string()),
            ));
            None
        }
    }
}

fn validate_raw_smt_fail_closed_policy(
    rows: &BTreeMap<&str, &str>,
    issues: &mut Vec<RawSmtSolveProfileValidationIssue>,
) {
    let status = rows.get("status").copied();
    let decision_code = rows.get("decision_code").copied();
    let reason = rows.get("reason").copied();
    let accepted = parse_bool_value(rows.get("accepted_for_consumer").copied());
    let fail_closed = parse_bool_value(rows.get("fail_closed").copied());
    let timed_out = parse_bool_value(rows.get("timed_out").copied()).unwrap_or(false);
    let deadline = parse_bool_value(rows.get("deadline_exceeded").copied()).unwrap_or(false);

    match (status, accepted, fail_closed) {
        (Some("available"), Some(true), Some(false))
        | (Some("rejected"), Some(false), Some(true)) => {}
        (Some(status), _, _) => issues.push(RawSmtSolveProfileValidationIssue::new(
            RawSmtSolveProfileValidationReason::FailOpenRows,
            "fail_closed",
            Some("available=>accepted=true/fail_closed=false, rejected=>accepted=false/fail_closed=true".to_string()),
            Some(format!(
                "status={status},accepted_for_consumer={},fail_closed={}",
                rows.get("accepted_for_consumer").copied().unwrap_or("missing"),
                rows.get("fail_closed").copied().unwrap_or("missing")
            )),
        )),
        _ => {}
    }

    if status == Some("available") && decision_code == Some("none") {
        issues.push(RawSmtSolveProfileValidationIssue::new(
            RawSmtSolveProfileValidationReason::FailOpenRows,
            "decision_code",
            Some("sat,unsat,unknown".to_string()),
            Some("none".to_string()),
        ));
    }
    if (timed_out || deadline) && status == Some("available") && decision_code != Some("unknown") {
        issues.push(RawSmtSolveProfileValidationIssue::new(
            RawSmtSolveProfileValidationReason::FailOpenRows,
            "decision_code",
            Some("unknown when timeout/deadline is true".to_string()),
            decision_code.map(str::to_string),
        ));
    }
    if reason == Some(RawSmtSolveProfileReason::RawProcessTimeout.code())
        && !(timed_out || deadline || decision_code == Some("unknown"))
    {
        issues.push(RawSmtSolveProfileValidationIssue::new(
            RawSmtSolveProfileValidationReason::MalformedRow,
            "reason",
            Some("timeout/deadline flag or unknown decision".to_string()),
            Some(
                RawSmtSolveProfileReason::RawProcessTimeout
                    .code()
                    .to_string(),
            ),
        ));
    }
}

fn parse_bool_value(value: Option<&str>) -> Option<bool> {
    match value {
        Some("true") => Some(true),
        Some("false") => Some(false),
        _ => None,
    }
}

fn raw_smt_validation_report(
    issues: Vec<RawSmtSolveProfileValidationIssue>,
) -> RawSmtSolveProfileValidationReport {
    let (status, reason, accepted_for_consumer, fail_closed) = if let Some(issue) = issues.first() {
        (
            RawSmtSolveProfileValidationStatus::Rejected,
            issue.reason,
            false,
            true,
        )
    } else {
        (
            RawSmtSolveProfileValidationStatus::Accepted,
            RawSmtSolveProfileValidationReason::Accepted,
            true,
            false,
        )
    };

    RawSmtSolveProfileValidationReport {
        schema: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
        schema_version: AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
        status,
        status_code: status.code(),
        reason,
        reason_code: reason.code(),
        accepted_for_consumer,
        fail_closed,
        issues,
    }
}

fn u128_to_json(value: u128) -> serde_json::Value {
    match u64::try_from(value) {
        Ok(value) => serde_json::json!(value),
        Err(_) => serde_json::json!(value.to_string()),
    }
}
