// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native API replay artifact types for downstream reducer/debugger handoff.

use ay_core::term::TermData;
use ay_core::{DatatypeSort, Sort, TermId};
use ay_frontend::PublicSort;

/// Schema identifier for native API replay artifacts.
pub const NATIVE_REPLAY_SCHEMA: &str = "ay.native-replay.v1";

/// Schema identifier for content-addressed native replay evidence manifests.
pub const NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA: &str = "ay.native-replay-evidence-manifest.v1";

/// Solver identity bound into a native replay evidence manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplaySolverIdentity {
    /// Solver engine or route name, for example `native-api:QF_LIA`.
    pub engine: String,
    /// AY build revision used to produce the replay artifact.
    pub ay_revision: String,
    /// AY crate version used to produce the replay artifact.
    pub ay_version: String,
    /// Optional backend-measured SHA-256 claim for the executable or owning
    /// solver package. Native replay binds and validates the spelling of this
    /// claim; it does not itself read or measure the backend executable.
    pub solver_binary_sha256: Option<String>,
}

/// Consumer-supplied provenance for a native replay artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayMetadata {
    /// Downstream consumer name, for example `verification-consumer`.
    pub consumer: Option<String>,
    /// Downstream consumer revision, for example the QuantifierConsumer git SHA.
    pub consumer_revision: Option<String>,
    /// Source fixture or test path.
    pub fixture_path: Option<String>,
    /// Function or verification-condition name within the fixture.
    pub function_path: Option<String>,
    /// Source span associated with the obligation.
    pub source_span: Option<String>,
    /// Obligation kind, for example `requires`, `ensures`, or `invariant`.
    pub obligation_kind: Option<String>,
    /// Free-form note for CI/reducer context.
    pub notes: Option<String>,
}

/// A declared native constant captured for replay.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayDeclaration {
    /// User-facing symbol name.
    pub name: String,
    /// Exact core variable identity in the exported term DAG.
    ///
    /// This can differ from [`Self::name`] when the frontend must protect a
    /// builtin or previously used spelling with an allocator-private identity.
    /// Replay reconstructs the declaration from the public name, then
    /// authenticates the reconstructed core identity against live frontend
    /// metadata; the allocator suffix itself is intentionally not stable.
    pub core_name: String,
    /// Term id in the original solver term store.
    pub term: TermId,
    /// Declared sort.
    pub sort: Sort,
}

/// A declared native function captured for replay.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayFunctionDeclaration {
    /// User-facing function symbol.
    pub name: String,
    /// Exact core application identity in the exported term DAG.
    pub core_name: String,
    /// Domain sorts.
    pub domain: Vec<Sort>,
    /// Range sort.
    pub range: Sort,
}

/// Closed semantic class for an authenticated replay symbol identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NativeReplaySymbolKind {
    /// Ordinary free constant or uninterpreted function.
    Uninterpreted,
    /// Declaration-activated theory function.
    Theory,
    /// Datatype constructor.
    DatatypeConstructor,
    /// Datatype selector.
    DatatypeSelector,
    /// Datatype tester.
    DatatypeTester,
}

/// Authenticated bridge from an exported core spelling to a stable declaration.
///
/// Replay never treats `core_name` as authority by itself. It reconstructs the
/// declaration from its stable surface/public data, proves the exact live
/// engine signature and kind, and only then maps this old core spelling to the
/// freshly allocated core identity.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplaySymbolIdentity {
    /// Stable user-facing declaration name.
    pub surface_name: String,
    /// Exact core identity used by the exported term DAG.
    pub core_name: String,
    /// Exact native API argument sorts before frontend lowering.
    pub api_domain: Vec<Sort>,
    /// Exact native API result sort before frontend lowering.
    pub api_range: Sort,
    /// Public argument sorts retained by the frontend.
    pub public_domain: Vec<PublicSort>,
    /// Public result sort retained by the frontend.
    pub public_range: PublicSort,
    /// Exact engine argument sorts in the exported context.
    pub engine_domain: Vec<Sort>,
    /// Exact engine result sort in the exported context.
    pub engine_range: Sort,
    /// Positive declaration semantics.
    pub kind: NativeReplaySymbolKind,
    /// Public datatype carrier owning a datatype member.
    pub datatype_surface: Option<String>,
    /// Exact exported engine carrier owning a datatype member.
    pub datatype_core: Option<String>,
}

/// A top-level assertion in the active solver context.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayAssertion {
    /// Assertion order within the active context.
    pub index: usize,
    /// Original solver term id.
    pub term: TermId,
    /// Optional assertion/core name, when asserted through `try_assert_named`.
    pub name: Option<String>,
    /// Minimum active push/pop scope depth for this assertion.
    pub scope_depth: usize,
}

/// A single term-store node in the native replay artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayTermNode {
    /// Original solver term id.
    pub id: TermId,
    /// Sort recorded with the term.
    pub sort: Sort,
    /// Native term data.
    pub data: TermData,
    /// This node is the exact bound term of a replayed nullary datatype
    /// constructor. Name equality alone is insufficient because a fresh or
    /// quantified variable may shadow the constructor's surface name.
    pub is_datatype_constructor: bool,
}

/// Replay-relevant native API events.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeReplayEvent {
    /// Monotonic event index.
    pub index: usize,
    /// Event kind and payload.
    pub kind: NativeReplayEventKind,
    /// Solver scope depth immediately after the event.
    pub scope_depth: u32,
}

impl NativeReplayEvent {
    pub(crate) fn new(index: usize, kind: NativeReplayEventKind, scope_depth: u32) -> Self {
        Self {
            index,
            kind,
            scope_depth,
        }
    }
}

/// Native API event payload.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeReplayEventKind {
    /// Solver construction set a logic.
    SetLogic {
        /// SMT-LIB logic name.
        logic: String,
    },
    /// A constant declaration was registered.
    DeclareConst {
        /// Symbol name.
        name: String,
        /// Original term id.
        term: TermId,
        /// Declared sort.
        sort: Sort,
    },
    /// A function declaration was registered.
    DeclareFun {
        /// Function name.
        name: String,
        /// Domain sorts.
        domain: Vec<Sort>,
        /// Range sort.
        range: Sort,
    },
    /// An algebraic datatype declaration was registered.
    DeclareDatatype {
        /// Complete datatype definition, including constructors and fields.
        datatype: DatatypeSort,
    },
    /// A top-level assertion was added.
    Assert {
        /// Asserted term id.
        term: TermId,
        /// Optional assertion/core name.
        name: Option<String>,
    },
    /// A push command completed.
    Push,
    /// A pop command completed.
    Pop,
    /// A full reset completed.
    Reset,
    /// A reset-assertions command completed.
    ResetAssertions,
    /// A check-sat call started.
    CheckSat,
    /// A check-sat-assuming call started.
    CheckSatAssuming {
        /// Assumption term ids.
        assumptions: Vec<TermId>,
    },
}

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

/// Complete native API reducer/replay artifact.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct NativeReplayArtifact {
    /// Artifact schema.
    pub schema: String,
    /// AY build revision, if the build supplied one.
    pub ay_revision: String,
    /// AY crate version.
    pub ay_version: String,
    /// Creation timestamp in Unix milliseconds.
    pub created_unix_ms: u128,
    /// Consumer and source provenance.
    pub metadata: NativeReplayMetadata,
    /// Active solver logic.
    pub logic: Option<String>,
    /// Selected native route summary.
    pub selected_route: Option<String>,
    /// Active push/pop scope depth.
    pub scope_depth: u32,
    /// Solver timeout budget in milliseconds.
    pub timeout_ms: Option<u128>,
    /// Native API event trace.
    pub events: Vec<NativeReplayEvent>,
    /// Declared constants.
    pub declarations: Vec<NativeReplayDeclaration>,
    /// Declared functions.
    pub function_declarations: Vec<NativeReplayFunctionDeclaration>,
    /// Authenticated declaration/core identity bridges used by replay.
    pub symbol_identities: Vec<NativeReplaySymbolIdentity>,
    /// Active assertions in assertion order.
    pub assertions: Vec<NativeReplayAssertion>,
    /// Complete native term DAG.
    pub terms: Vec<NativeReplayTermNode>,
    /// Solve details captured from the same solve call.
    pub solve: Option<NativeReplaySolveSummary>,
    /// Checked replay comparison captured after replaying this artifact.
    pub checked_replay: Option<NativeReplayCheckedReplaySummary>,
    /// Non-serialized authority from the strict in-process replay workflow.
    ///
    /// Diagnostic summaries and parsed JSON never populate this field.
    pub(crate) admission_token: Option<NativeReplayAdmissionToken>,
    /// Panic payload when capture used a panic-safe boundary.
    pub panic_payload: Option<String>,
    /// Unsupported atom or route diagnostics, when known.
    pub unsupported_atoms: Vec<String>,
    /// Known replay gaps in this artifact.
    pub replay_gaps: Vec<String>,
}
