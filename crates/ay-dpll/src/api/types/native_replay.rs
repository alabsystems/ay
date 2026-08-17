// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native API replay artifact types for downstream reducer/debugger handoff.

use ay_core::term::TermData;
use ay_core::{DatatypeSort, Sort, TermId};
use ay_frontend::PublicSort;

mod evidence;

pub(crate) use evidence::NativeReplayAdmissionToken;
pub use evidence::{
    NativeReplayCheckedReplaySummary, NativeReplayEvidenceManifest, NativeReplayModelSummary,
    NativeReplayProofSummary, NativeReplayResourceUsage, NativeReplaySolveSummary,
    NativeReplayStatistics, NativeReplayUnknownProgress,
};

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
