// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay solve and evidence summary types.

use super::NativeReplaySolverIdentity;

/// Proof evidence summarized into the native replay artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayProofSummary {
    /// Whether an UNSAT proof artifact was available.
    pub available: bool,
    /// Number of retained proof clauses/steps reported in statistics.
    pub clause_count: u64,
    /// Whether proof statistics claim completeness.
    pub complete: bool,
    /// Whether the exact replayed UNSAT query consumed a strict
    /// checker-accepted publication certificate.
    pub strictly_verified: bool,
    /// Number of internal proof-checker failures.
    pub checker_failures: u64,
    /// Number of proof trust fallback steps, when proof quality was available.
    pub trust_fallbacks: u64,
}

/// Model-validation evidence summarized into the native replay artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayModelSummary {
    /// Whether model validation ran and passed for this SAT result.
    pub validated: bool,
    /// Number of independent assertion checks.
    pub independent_checks: u64,
    /// Number of delegated theory checks.
    pub delegated_checks: u64,
    /// Number of incomplete or skipped checks.
    pub incomplete_checks: u64,
    /// Number of model validation failures reported in statistics.
    pub validation_failures: u64,
    /// Number of model validation skips reported in statistics.
    pub validation_skips: u64,
}

/// Solve envelope attached to a native replay artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplaySolveSummary {
    /// Raw solver result as SMT-LIB text: `sat`, `unsat`, or `unknown`.
    pub result: String,
    /// Structured Unknown reason.
    pub unknown_reason: Option<String>,
    /// Responsible phase for Unknown, when known.
    pub unknown_phase: Option<String>,
    /// Self-contained progress evidence for Unknown results.
    pub unknown_progress: Option<NativeReplayUnknownProgress>,
    /// Executor error detail, if any.
    pub executor_error: Option<String>,
    /// Wall-clock solve time in milliseconds.
    pub elapsed_ms: u128,
    /// Verification level text.
    pub verification_level: String,
    /// Proof evidence.
    pub proof: NativeReplayProofSummary,
    /// Model-validation evidence.
    pub model: NativeReplayModelSummary,
    /// Solver statistic snapshot used by reducer triage.
    pub statistics: NativeReplayStatistics,
    /// Resource snapshot used by reducer triage.
    pub resources: NativeReplayResourceUsage,
}

/// Progress evidence for an Unknown result in a native replay artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayUnknownProgress {
    /// Structured Unknown reason.
    pub reason: String,
    /// Broad solve phase responsible for the Unknown.
    pub responsible_phase: Option<String>,
    /// Configured wall-clock budget in milliseconds.
    pub wall_time_budget_ms: Option<u128>,
    /// Elapsed wall time in milliseconds.
    pub wall_time_elapsed_ms: u128,
}

/// Stable subset of solver statistics for replay triage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayStatistics {
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
    /// Partial clauses.
    pub partial_clause_count: u64,
    /// E-matching rounds completed.
    pub ematching_rounds_completed: u64,
    /// E-matching instances created.
    pub ematching_instances_created: u64,
    /// Refinement rounds.
    pub refinement_count: u64,
}

/// Stable subset of solve resources for replay triage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayResourceUsage {
    /// Process RSS bytes.
    pub rss_bytes: usize,
    /// Per-solver term-store bytes.
    pub term_bytes: usize,
    /// Number of interned terms.
    pub term_count: usize,
    /// Learned clauses retained.
    pub learned_clause_count: usize,
    /// Limit hit text, if any.
    pub limit_hit: Option<String>,
}

/// Result of replaying a native replay artifact and comparing the new solve
/// envelope with the original captured solve envelope.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayCheckedReplaySummary {
    /// Whether original and replay raw SAT results match.
    pub result_matches: bool,
    /// Whether original and replay UNSAT proof evidence statuses match.
    pub proof_status_matches: bool,
    /// Whether original and replay SAT model evidence statuses match.
    pub model_status_matches: bool,
    /// Original raw result, when the source artifact included solve details.
    pub original_result: Option<String>,
    /// Replay raw result.
    pub replay_result: String,
    /// Original Unknown reason, when present.
    pub original_unknown_reason: Option<String>,
    /// Replay Unknown reason, when present.
    pub replay_unknown_reason: Option<String>,
    /// Original proof evidence status, when present.
    pub original_proof_status: Option<String>,
    /// Replay proof evidence status.
    pub replay_proof_status: String,
    /// Original model evidence status, when present.
    pub original_model_status: Option<String>,
    /// Replay model evidence status.
    pub replay_model_status: String,
    /// Replay executor error detail, when present.
    pub replay_executor_error: Option<String>,
}

/// In-memory authority minted only by the strict native replay workflow.
///
/// This token is deliberately crate-private and is never represented in the
/// diagnostic JSON schema.  Its digests bind the exact post-replay artifact,
/// checked summary, execution options, problem, and current solver identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeReplayAdmissionToken {
    pub(crate) solver_identity: NativeReplaySolverIdentity,
    pub(crate) solver_identity_sha256: String,
    pub(crate) problem_sha256: String,
    pub(crate) options_sha256: String,
    pub(crate) checked_summary_sha256: String,
    pub(crate) replay_artifact_sha256: String,
}

/// Content-addressed evidence manifest for native API replay artifacts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayEvidenceManifest {
    /// Manifest schema.
    pub schema: String,
    /// Solver identity bound into this manifest.
    pub solver_identity: NativeReplaySolverIdentity,
    /// SHA-256 of the normalized solver identity JSON.
    pub solver_identity_sha256: String,
    /// SHA-256 of the replayable problem binding.
    pub problem_sha256: String,
    /// SHA-256 of options and resource limits.
    pub options_sha256: String,
    /// SHA-256 of the full native replay artifact JSON.
    pub replay_artifact_sha256: String,
    /// Checked result class. Unknown, unchecked, and demoted statuses are explicit.
    pub checked_result: String,
    /// Original result from the source artifact, when present.
    pub original_result: Option<String>,
    /// Result from checked replay, when present.
    pub replay_result: Option<String>,
    /// Replay proof-evidence status, when present.
    pub proof_status: Option<String>,
    /// Replay model-evidence status, when present.
    pub model_status: Option<String>,
    /// Unknown reason from original or replay result, when present.
    pub unknown_reason: Option<String>,
    /// Unsupported atoms or route diagnostics captured by the artifact.
    pub unsupported_atoms: Vec<String>,
    /// Known replay gaps captured by the artifact.
    pub replay_gaps: Vec<String>,
    /// Reasons this manifest cannot be admitted by a compiler verifier backend.
    pub admission_rejection_reasons: Vec<String>,
    /// SHA-256 of the manifest body excluding this field.
    pub manifest_sha256: String,
    /// Private in-memory seal over an authority-bearing manifest body.
    ///
    /// This is deliberately absent from manifest JSON. It prevents callers
    /// from manufacturing admission by mutating the public diagnostic fields
    /// after manifest construction.
    pub(crate) admission_seal_sha256: Option<String>,
}
