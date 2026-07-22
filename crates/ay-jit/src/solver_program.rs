// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backend-neutral artifact model for solver-program JIT (#8874).
//!
//! Solver-program artifacts are larger compiled regions than the current
//! row-local sparse-substitute kernels. This module defines the contract that
//! external code generation and future backends must satisfy before the solver can install,
//! observe, invalidate, or deopt compiled code.

use serde::{Deserialize, Serialize};
use std::collections::VecDeque;

/// Current serialized metadata schema version for solver-program artifacts.
pub(crate) const SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION: u32 = 1;
/// Current serialized lifecycle snapshot schema version.
pub(crate) const SOLVER_PROGRAM_LIFECYCLE_SNAPSHOT_SCHEMA_VERSION: u32 = 2;

/// Stable identity assigned by the artifact producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct SolverProgramArtifactId(pub u64);

/// Code generator that produced an artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramBackend {
    /// Active verified compiler path: ay emits ExternalCodegenIr and EXTERNAL_CODEGEN lowers it.
    ExternalCodegenBackend,
    /// Hand-written native assembler path used by older local kernels.
    NativeAssembler,
    /// Interpreter fallback. This is not installable as native code.
    Interpreter,
}

impl SolverProgramBackend {
    /// Whether this backend is the strategic production compiler.
    #[must_use]
    pub(crate) fn is_active_compiler(self) -> bool {
        matches!(self, Self::ExternalCodegenBackend)
    }

    /// Whether artifacts from this backend may ever be installed as native code.
    #[must_use]
    pub(crate) fn is_native_installable(self) -> bool {
        !matches!(self, Self::Interpreter)
    }
}

/// Solver region represented by an artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramKind {
    /// Current EXTERNAL_CODEGEN sparse substitute kernel.
    LraSparseSubstitute,
    /// Future basis-local LRA compiled region.
    LraBasisRegion,
    /// Future LIA/bounds propagation region.
    LiaBoundRegion,
    /// CHC/PDR expression evaluator.
    ChcExpression,
    /// SAT conflict-analysis kernel.
    SatConflict,
    /// SAT subsumption or BCE scanning kernel.
    SatInprocess,
    /// Whole CDCL loop specialized for one static SAT formula.
    SatWholeLoop,
    /// PB propagation or cut kernel. Not production today.
    PbKernel,
}

/// Source-level provenance used to reconstruct or audit an artifact request.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramProvenance {
    /// Sparse substitute compiled from one LRA pivot row.
    LraSparseSubstitute {
        /// Variable eliminated from the target row.
        entering_var: u32,
        /// Non-zero pivot terms captured by the artifact.
        pivot_terms: u32,
    },
    /// Future basis-local LRA region.
    LraBasisRegion {
        /// Basis generation captured at request time.
        basis_generation: u64,
    },
    /// Future CHC expression artifact.
    ChcExpression {
        /// Stable expression hash.
        expr_hash: u64,
    },
    /// Future whole-loop SAT artifact.
    SatWholeLoop {
        /// SAT variables captured in the static formula profile.
        num_vars: u32,
        /// Irredundant clauses captured at compile-request time.
        irredundant_clauses: u32,
        /// Stable hash of static clause-length and literal-shape metadata.
        clause_shape_hash: u64,
    },
    /// Placeholder for tests or migration scaffolding.
    Unknown,
}

impl SolverProgramProvenance {
    /// Whether this provenance is precise enough for the artifact kind.
    #[must_use]
    pub(crate) fn matches_kind(&self, kind: SolverProgramKind) -> bool {
        matches!(
            (kind, self),
            (
                SolverProgramKind::LraSparseSubstitute,
                Self::LraSparseSubstitute { .. }
            ) | (
                SolverProgramKind::LraBasisRegion,
                Self::LraBasisRegion { .. }
            ) | (SolverProgramKind::ChcExpression, Self::ChcExpression { .. })
                | (SolverProgramKind::SatWholeLoop, Self::SatWholeLoop { .. },)
        )
    }
}

/// Guard/oracle requirements that must hold before applying compiled code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct GuardRequirements {
    /// Runtime generations must match the artifact invalidation key.
    pub(crate) require_generation_match: bool,
    /// The caller must be able to fall back to the generic solver path.
    pub(crate) require_interpreter_fallback: bool,
    /// Applications require an oracle/differential check before default-on use.
    pub(crate) require_oracle_check: bool,
}

impl GuardRequirements {
    /// Conservative requirements for pre-production solver-program artifacts.
    #[must_use]
    pub(crate) fn conservative() -> Self {
        Self {
            require_generation_match: true,
            require_interpreter_fallback: true,
            require_oracle_check: true,
        }
    }

    /// Whether these guards satisfy the current installable-artifact contract.
    #[must_use]
    pub(crate) fn is_installable_contract(self) -> bool {
        self.require_generation_match
            && self.require_interpreter_fallback
            && self.require_oracle_check
    }
}

/// Install boundaries allowed by a specific artifact.
#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub(crate) struct InstallBoundarySet {
    /// Solver-start install is allowed.
    pub(crate) solver_start: bool,
    /// Restart/checkpoint install is allowed.
    pub(crate) restart: bool,
    /// Theory synchronization install is allowed.
    pub(crate) theory_sync: bool,
    /// Incremental-boundary install is allowed.
    pub(crate) incremental_boundary: bool,
}

impl InstallBoundarySet {
    /// Allow only solver-start installation.
    #[must_use]
    pub(crate) fn solver_start_only() -> Self {
        Self {
            solver_start: true,
            ..Self::default()
        }
    }

    /// Allow only restart-boundary installation.
    #[must_use]
    pub(crate) fn restart_only() -> Self {
        Self {
            restart: true,
            ..Self::default()
        }
    }

    /// Whether this artifact allows installation at `boundary`.
    #[must_use]
    pub(crate) fn allows(self, boundary: InstallBoundary) -> bool {
        match boundary {
            InstallBoundary::SolverStart => self.solver_start,
            InstallBoundary::Restart => self.restart,
            InstallBoundary::TheorySync => self.theory_sync,
            InstallBoundary::IncrementalBoundary => self.incremental_boundary,
        }
    }
}

/// Target machine assumptions baked into generated code.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct TargetFeatures {
    /// Rust target architecture, for example `aarch64` or `x86_64`.
    pub(crate) arch: String,
    /// Rust target operating system, for example `macos` or `linux`.
    pub(crate) os: String,
    /// Required CPU feature strings, sorted by the caller for stable metadata.
    pub(crate) cpu_features: Vec<String>,
}

impl TargetFeatures {
    /// Create target metadata with stable CPU feature ordering.
    #[must_use]
    pub(crate) fn new(
        arch: impl Into<String>,
        os: impl Into<String>,
        mut cpu_features: Vec<String>,
    ) -> Self {
        cpu_features.sort();
        cpu_features.dedup();
        Self {
            arch: arch.into(),
            os: os.into(),
            cpu_features,
        }
    }

    /// Feature set for the current compile target.
    #[must_use]
    pub(crate) fn current() -> Self {
        Self::new(std::env::consts::ARCH, std::env::consts::OS, Vec::new())
    }

    /// Whether required CPU features are serialized in canonical order.
    #[must_use]
    pub(crate) fn has_stable_cpu_feature_metadata(&self) -> bool {
        self.cpu_features.windows(2).all(|pair| pair[0] < pair[1])
    }

    /// Returns true when an artifact compiled for `self` may run on `runtime`.
    #[must_use]
    pub(crate) fn is_compatible_with(&self, runtime: &Self) -> bool {
        self.arch == runtime.arch
            && self.os == runtime.os
            && self
                .cpu_features
                .iter()
                .all(|required| runtime.cpu_features.contains(required))
    }
}

/// Generation tags for mutable solver state referenced by compiled code.
#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub(crate) struct SolverProgramGenerations {
    /// Clause/constraint arena generation.
    pub(crate) constraints: u64,
    /// Theory atom table generation.
    pub(crate) theory_atoms: u64,
    /// Simplex/LRA basis generation.
    pub(crate) basis: u64,
    /// Trail or assignment generation.
    pub(crate) trail: u64,
    /// Runtime policy/configuration generation.
    pub(crate) config: u64,
}

impl SolverProgramGenerations {
    /// Whether every referenced generation still matches the runtime state.
    #[must_use]
    pub(crate) fn matches(self, runtime: Self) -> bool {
        self == runtime
    }
}

/// Hashes and generation tags used to detect stale solver-program artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct InvalidationKey {
    /// Mutable state generations captured at compile time.
    pub(crate) generations: SolverProgramGenerations,
    /// Shape hash for the compiled region: row pattern, basis shape, or AST.
    pub(crate) shape_hash: u64,
    /// Semantic hash for symbols, operators, and normalization policy.
    pub(crate) semantic_hash: u64,
}

impl InvalidationKey {
    /// Whether this key is still valid for the runtime key.
    #[must_use]
    pub(crate) fn is_valid_for(self, runtime: Self) -> bool {
        self == runtime
    }
}

/// Safe boundary where compiled code may be installed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum InstallBoundary {
    /// Solver start or top-level reset before hot propagation begins.
    SolverStart,
    /// Restart/checkpoint boundary with no compiled frame currently executing.
    Restart,
    /// Theory synchronization point after mutable tables are quiescent.
    TheorySync,
    /// Incremental push/pop boundary after invalidation has been applied.
    IncrementalBoundary,
}

/// Reason a compiled artifact must not be installed or applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DeoptReason {
    /// Runtime disable flag or competition profile disabled this backend.
    DisabledByPolicy,
    /// The artifact was produced by a backend that is not allowed here.
    BackendRejected,
    /// Target architecture, OS, or CPU feature mismatch.
    TargetMismatch,
    /// Solver generations or region hashes no longer match.
    StaleInvalidationKey,
    /// Runtime guard/oracle check failed before compiled code could apply.
    GuardFailed,
    /// Install was attempted from an unsafe boundary.
    UnsafeInstallBoundary,
    /// Artifact exceeded a code-cache or per-artifact memory budget.
    CodeSizeBudgetExceeded,
    /// Compiler timed out or exhausted its compilation budget.
    CompileBudgetExceeded,
    /// Artifact uses unsupported result or guard semantics.
    UnsupportedContract,
}

/// Install validation result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum InstallDecision {
    /// Artifact may be installed at the requested boundary.
    Install,
    /// Artifact must deopt to the generic solver path.
    Deopt(DeoptReason),
}

impl InstallDecision {
    /// Whether the decision permits installing native code.
    #[must_use]
    pub(crate) fn is_install(self) -> bool {
        matches!(self, Self::Install)
    }
}

/// Apply-time validation result for an already-installed artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ApplyDecision {
    /// Artifact guards passed and native code may run.
    Apply,
    /// Artifact must deopt to the generic solver path.
    Deopt(DeoptReason),
}

impl ApplyDecision {
    /// Whether the decision permits applying native code.
    #[must_use]
    pub(crate) fn is_apply(self) -> bool {
        matches!(self, Self::Apply)
    }
}

/// Observable metadata for a compiled solver-program artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramArtifactMeta {
    /// Serialized metadata schema version.
    pub(crate) schema_version: u32,
    /// Stable artifact identity.
    pub(crate) id: SolverProgramArtifactId,
    /// Solver region represented by this artifact.
    pub(crate) kind: SolverProgramKind,
    /// Backend that produced this artifact.
    pub(crate) backend: SolverProgramBackend,
    /// Compiler/producer version captured by the backend.
    pub(crate) producer_version: u32,
    /// Semantic version/hash for normalization and lowering policy.
    pub(crate) semantic_version: u64,
    /// Source-level provenance for audit and rebuild.
    pub(crate) provenance: SolverProgramProvenance,
    /// Invalidation key captured at compile time.
    pub(crate) invalidation_key: InvalidationKey,
    /// Guard/oracle requirements for safe application.
    pub(crate) guard_requirements: GuardRequirements,
    /// Boundaries where this artifact may be installed.
    pub(crate) install_boundaries: InstallBoundarySet,
    /// Target features required by the generated code.
    pub(crate) target: TargetFeatures,
    /// Native code size in bytes.
    pub(crate) code_size_bytes: u64,
    /// Compile latency in microseconds.
    pub(crate) compile_latency_us: u64,
    /// Stable stats prefix for counters emitted by this artifact family.
    pub(crate) stats_prefix: String,
    /// Optional request ID from an async compiler service.
    pub(crate) request_id: Option<u64>,
}

impl SolverProgramArtifactMeta {
    /// Validate whether this artifact may be installed now.
    #[must_use]
    pub(crate) fn validate_install(
        &self,
        runtime_key: InvalidationKey,
        runtime_target: &TargetFeatures,
        boundary: InstallBoundary,
        policy: InstallPolicy,
    ) -> InstallDecision {
        if !policy.compiled_solver_programs_enabled {
            return InstallDecision::Deopt(DeoptReason::DisabledByPolicy);
        }
        if self.schema_version != SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION {
            return InstallDecision::Deopt(DeoptReason::UnsupportedContract);
        }
        if !self.provenance.matches_kind(self.kind)
            || !self.guard_requirements.is_installable_contract()
        {
            return InstallDecision::Deopt(DeoptReason::UnsupportedContract);
        }
        if !self.target.has_stable_cpu_feature_metadata() {
            return InstallDecision::Deopt(DeoptReason::UnsupportedContract);
        }
        if !self.backend.is_native_installable()
            || self.backend != SolverProgramBackend::ExternalCodegenBackend
        {
            return InstallDecision::Deopt(DeoptReason::BackendRejected);
        }
        if policy.require_external_codegen
            && self.backend != SolverProgramBackend::ExternalCodegenBackend
        {
            return InstallDecision::Deopt(DeoptReason::BackendRejected);
        }
        if !self.target.is_compatible_with(runtime_target) {
            return InstallDecision::Deopt(DeoptReason::TargetMismatch);
        }
        if !self.invalidation_key.is_valid_for(runtime_key) {
            return InstallDecision::Deopt(DeoptReason::StaleInvalidationKey);
        }
        if !self.install_boundaries.allows(boundary) || !policy.boundary_allowed(boundary) {
            return InstallDecision::Deopt(DeoptReason::UnsafeInstallBoundary);
        }
        if self.code_size_bytes > policy.max_code_size_bytes {
            return InstallDecision::Deopt(DeoptReason::CodeSizeBudgetExceeded);
        }
        if self.compile_latency_us > policy.max_compile_latency_us {
            return InstallDecision::Deopt(DeoptReason::CompileBudgetExceeded);
        }
        InstallDecision::Install
    }

    /// Validate guards that must still hold immediately before native apply.
    #[must_use]
    pub(crate) fn validate_apply(
        &self,
        runtime_key: InvalidationKey,
        runtime_target: &TargetFeatures,
        oracle_check_passed: bool,
    ) -> ApplyDecision {
        if self.schema_version != SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION {
            return ApplyDecision::Deopt(DeoptReason::UnsupportedContract);
        }
        if !self.provenance.matches_kind(self.kind)
            || !self.guard_requirements.is_installable_contract()
            || !self.target.has_stable_cpu_feature_metadata()
        {
            return ApplyDecision::Deopt(DeoptReason::UnsupportedContract);
        }
        if !self.target.is_compatible_with(runtime_target) {
            return ApplyDecision::Deopt(DeoptReason::TargetMismatch);
        }
        if !self.invalidation_key.is_valid_for(runtime_key) {
            return ApplyDecision::Deopt(DeoptReason::StaleInvalidationKey);
        }
        if self.guard_requirements.require_oracle_check && !oracle_check_passed {
            return ApplyDecision::Deopt(DeoptReason::GuardFailed);
        }
        ApplyDecision::Apply
    }
}

/// Runtime policy for installing solver-program artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct InstallPolicy {
    /// Global enable bit for compiled solver programs.
    pub(crate) compiled_solver_programs_enabled: bool,
    /// Reject non-external code generation artifacts.
    pub(crate) require_external_codegen: bool,
    /// Maximum native code size for a single artifact.
    pub(crate) max_code_size_bytes: u64,
    /// Maximum compile latency charged to a single artifact.
    pub(crate) max_compile_latency_us: u64,
    /// Whether solver-start installs are allowed.
    pub(crate) allow_solver_start_install: bool,
    /// Whether restart-boundary installs are allowed.
    pub(crate) allow_restart_install: bool,
    /// Whether theory-sync installs are allowed.
    pub(crate) allow_theory_sync_install: bool,
    /// Whether incremental-boundary installs are allowed.
    pub(crate) allow_incremental_install: bool,
}

impl Default for InstallPolicy {
    fn default() -> Self {
        Self {
            compiled_solver_programs_enabled: false,
            require_external_codegen: true,
            max_code_size_bytes: 1 << 20,
            max_compile_latency_us: 50_000,
            allow_solver_start_install: false,
            allow_restart_install: false,
            allow_theory_sync_install: false,
            allow_incremental_install: false,
        }
    }
}

impl InstallPolicy {
    /// Opt-in policy used by tests and future integration call sites.
    #[must_use]
    pub(crate) fn allow_external_codegen_for_testing() -> Self {
        Self {
            compiled_solver_programs_enabled: true,
            allow_solver_start_install: true,
            allow_restart_install: true,
            allow_theory_sync_install: true,
            allow_incremental_install: true,
            ..Self::default()
        }
    }

    /// Whether installation may occur at `boundary`.
    #[must_use]
    pub(crate) fn boundary_allowed(self, boundary: InstallBoundary) -> bool {
        match boundary {
            InstallBoundary::SolverStart => self.allow_solver_start_install,
            InstallBoundary::Restart => self.allow_restart_install,
            InstallBoundary::TheorySync => self.allow_theory_sync_install,
            InstallBoundary::IncrementalBoundary => self.allow_incremental_install,
        }
    }
}

/// Typed compiler result for future async external code generation services.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramCompileResult {
    /// Compilation produced installable native code metadata.
    Compiled(Box<SolverProgramArtifactMeta>),
    /// Region is valid but should stay on the generic path.
    Unsupported {
        /// Solver region that was considered.
        kind: SolverProgramKind,
        /// Reason the contract could not be satisfied.
        reason: DeoptReason,
    },
}

/// Runtime accounting policy for solver-program lifecycle observations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramLifecyclePolicy {
    /// Maximum recent lifecycle samples retained in snapshots.
    pub(crate) max_samples: usize,
}

impl Default for SolverProgramLifecyclePolicy {
    fn default() -> Self {
        Self { max_samples: 32 }
    }
}

/// Stable per-reason deopt counters for solver-program lifecycle snapshots.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DeoptReasonCounters {
    /// Disabled by runtime policy.
    pub(crate) disabled_by_policy: u64,
    /// Backend rejected by the solver-program contract.
    pub(crate) backend_rejected: u64,
    /// Target machine mismatch.
    pub(crate) target_mismatch: u64,
    /// Stale invalidation key.
    pub(crate) stale_invalidation_key: u64,
    /// Runtime guard/oracle failure.
    pub(crate) guard_failed: u64,
    /// Unsafe install boundary.
    pub(crate) unsafe_install_boundary: u64,
    /// Code-size budget exceeded.
    pub(crate) code_size_budget_exceeded: u64,
    /// Compile-time budget exceeded.
    pub(crate) compile_budget_exceeded: u64,
    /// Unsupported artifact contract.
    pub(crate) unsupported_contract: u64,
}

impl DeoptReasonCounters {
    fn record(&mut self, reason: DeoptReason) {
        match reason {
            DeoptReason::DisabledByPolicy => saturating_inc(&mut self.disabled_by_policy),
            DeoptReason::BackendRejected => saturating_inc(&mut self.backend_rejected),
            DeoptReason::TargetMismatch => saturating_inc(&mut self.target_mismatch),
            DeoptReason::StaleInvalidationKey => saturating_inc(&mut self.stale_invalidation_key),
            DeoptReason::GuardFailed => saturating_inc(&mut self.guard_failed),
            DeoptReason::UnsafeInstallBoundary => {
                saturating_inc(&mut self.unsafe_install_boundary);
            }
            DeoptReason::CodeSizeBudgetExceeded => {
                saturating_inc(&mut self.code_size_budget_exceeded);
            }
            DeoptReason::CompileBudgetExceeded => {
                saturating_inc(&mut self.compile_budget_exceeded);
            }
            DeoptReason::UnsupportedContract => saturating_inc(&mut self.unsupported_contract),
        }
    }

    /// Total deopts represented by the per-reason counters.
    #[must_use]
    pub(crate) fn total(self) -> u64 {
        self.disabled_by_policy
            .saturating_add(self.backend_rejected)
            .saturating_add(self.target_mismatch)
            .saturating_add(self.stale_invalidation_key)
            .saturating_add(self.guard_failed)
            .saturating_add(self.unsafe_install_boundary)
            .saturating_add(self.code_size_budget_exceeded)
            .saturating_add(self.compile_budget_exceeded)
            .saturating_add(self.unsupported_contract)
    }
}

/// Aggregate solver-program lifecycle counters.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramLifecycleCounters {
    /// Queue decisions considered by the solver-program tier.
    pub(crate) queue_attempts: u64,
    /// Queue submissions accepted for compilation.
    pub(crate) queue_accepted: u64,
    /// Queue submissions rejected before compilation.
    pub(crate) queue_rejected: u64,
    /// Successful compiler results reported to the lifecycle accountant.
    pub(crate) compile_successes: u64,
    /// Failed or unsupported compiler results reported to the lifecycle accountant.
    pub(crate) compile_failures: u64,
    /// Total compile latency for successful artifacts, in microseconds.
    pub(crate) compile_latency_us_total: u64,
    /// Maximum observed compile latency for one artifact, in microseconds.
    pub(crate) compile_latency_us_max: u64,
    /// Total native code bytes for successful artifacts.
    pub(crate) code_size_bytes_total: u64,
    /// Maximum native code bytes for one artifact.
    pub(crate) code_size_bytes_max: u64,
    /// Install decisions attempted at solver-safe boundaries.
    pub(crate) install_attempts: u64,
    /// Artifacts installed after passing the solver-program contract.
    pub(crate) installs: u64,
    /// Attempts to run installed solver-program code.
    pub(crate) apply_attempts: u64,
    /// Successful applications of installed solver-program code.
    pub(crate) applies: u64,
    /// Runtime guard/oracle failures before compiled code could apply.
    pub(crate) guard_fails: u64,
    /// Transitions back to the generic solver path.
    pub(crate) deopts: u64,
    /// Deopt reasons, kept separate for future CLI surfacing.
    pub(crate) deopt_reasons: DeoptReasonCounters,
    /// Lifecycle samples omitted because recent-sample retention was bounded.
    pub(crate) samples_dropped: u64,
}

impl SolverProgramLifecycleCounters {
    fn record_compile_success(&mut self, meta: &SolverProgramArtifactMeta) {
        saturating_inc(&mut self.compile_successes);
        self.compile_latency_us_total = self
            .compile_latency_us_total
            .saturating_add(meta.compile_latency_us);
        self.compile_latency_us_max = self.compile_latency_us_max.max(meta.compile_latency_us);
        self.code_size_bytes_total = self
            .code_size_bytes_total
            .saturating_add(meta.code_size_bytes);
        self.code_size_bytes_max = self.code_size_bytes_max.max(meta.code_size_bytes);
    }

    fn record_deopt(&mut self, reason: DeoptReason) {
        saturating_inc(&mut self.deopts);
        self.deopt_reasons.record(reason);
    }
}

/// Recent lifecycle event kind retained in solver-program snapshots.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramLifecycleEvent {
    /// Queue accept/reject decision.
    Queue,
    /// Compiler result and artifact-size observation.
    Compile,
    /// Install decision accepted native code.
    Install,
    /// Installed code applied successfully.
    Apply,
    /// Runtime guard/oracle failed before compiled code could apply.
    GuardFail,
    /// The lifecycle moved back to the generic solver path.
    Deopt,
}

/// Bounded sample retained for future CLI stats and issue evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramLifecycleSample {
    /// Monotonic sample sequence assigned by the local accountant.
    pub(crate) sequence: u64,
    /// Lifecycle event represented by the sample.
    pub(crate) event: SolverProgramLifecycleEvent,
    /// Artifact ID when an artifact was available.
    pub(crate) artifact_id: Option<SolverProgramArtifactId>,
    /// Solver-program kind involved in the event.
    pub(crate) kind: SolverProgramKind,
    /// Producing backend when known.
    pub(crate) backend: Option<SolverProgramBackend>,
    /// Async compiler request ID when known.
    pub(crate) request_id: Option<u64>,
    /// Install boundary when the event is tied to installation.
    pub(crate) boundary: Option<InstallBoundary>,
    /// Deopt or rejection reason when the event fell back to generic solving.
    pub(crate) deopt_reason: Option<DeoptReason>,
    /// Native code size in bytes when a compiled artifact was available.
    pub(crate) code_size_bytes: Option<u64>,
    /// Compile latency in microseconds when a compiled artifact was available.
    pub(crate) compile_latency_us: Option<u64>,
}

impl SolverProgramLifecycleSample {
    fn new(
        event: SolverProgramLifecycleEvent,
        kind: SolverProgramKind,
        backend: Option<SolverProgramBackend>,
        artifact_id: Option<SolverProgramArtifactId>,
        request_id: Option<u64>,
    ) -> Self {
        Self {
            sequence: 0,
            event,
            artifact_id,
            kind,
            backend,
            request_id,
            boundary: None,
            deopt_reason: None,
            code_size_bytes: None,
            compile_latency_us: None,
        }
    }

    fn from_meta(event: SolverProgramLifecycleEvent, meta: &SolverProgramArtifactMeta) -> Self {
        Self::new(
            event,
            meta.kind,
            Some(meta.backend),
            Some(meta.id),
            meta.request_id,
        )
    }

    fn with_boundary(mut self, boundary: InstallBoundary) -> Self {
        self.boundary = Some(boundary);
        self
    }

    fn with_deopt_reason(mut self, reason: DeoptReason) -> Self {
        self.deopt_reason = Some(reason);
        self
    }

    fn with_compile_metrics(mut self, meta: &SolverProgramArtifactMeta) -> Self {
        self.code_size_bytes = Some(meta.code_size_bytes);
        self.compile_latency_us = Some(meta.compile_latency_us);
        self
    }
}

/// Versioned snapshot for future solver-program CLI stats.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramLifecycleSnapshot {
    /// Serialized snapshot schema version.
    pub(crate) schema_version: u32,
    /// Aggregate lifecycle counters.
    pub(crate) counters: SolverProgramLifecycleCounters,
    /// Bounded recent lifecycle samples.
    pub(crate) samples: Vec<SolverProgramLifecycleSample>,
}

/// Current stable flat-stats schema for solver-program observability.
pub const SOLVER_PROGRAM_STABLE_STATS_SCHEMA_VERSION: u64 = 1;

/// Stable artifact-kind profile toggles surfaced through stats JSON.
///
/// These toggles describe solver-program families, not implementation modules:
/// consumers should not need to know which external code generation service or queue produced
/// an artifact to understand whether a family was enabled for this solve.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProgramProfileToggles {
    /// external code generation sparse-substitute solver-programs may be requested.
    pub lra_sparse_substitute_enabled: bool,
    /// Basis-local LRA region solver-programs may be requested.
    pub lra_basis_region_enabled: bool,
    /// LIA/bounds region solver-programs may be requested.
    pub lia_bound_region_enabled: bool,
    /// CHC expression solver-programs may be requested.
    pub chc_expression_enabled: bool,
    /// SAT conflict-analysis solver-programs may be requested.
    pub sat_conflict_enabled: bool,
    /// SAT inprocessing solver-programs may be requested.
    pub sat_inprocess_enabled: bool,
    /// PB solver-programs may be requested.
    pub pb_kernel_enabled: bool,
}

impl SolverProgramProfileToggles {
    /// Profile toggles for the current LRA solver-program families.
    #[must_use]
    pub const fn lra(lra_sparse_substitute_enabled: bool, lra_basis_region_enabled: bool) -> Self {
        Self {
            lra_sparse_substitute_enabled,
            lra_basis_region_enabled,
            lia_bound_region_enabled: false,
            chc_expression_enabled: false,
            sat_conflict_enabled: false,
            sat_inprocess_enabled: false,
            pb_kernel_enabled: false,
        }
    }

    /// Whether any solver-program family is enabled.
    #[must_use]
    pub const fn any_enabled(self) -> bool {
        self.lra_sparse_substitute_enabled
            || self.lra_basis_region_enabled
            || self.lia_bound_region_enabled
            || self.chc_expression_enabled
            || self.sat_conflict_enabled
            || self.sat_inprocess_enabled
            || self.pb_kernel_enabled
    }

    fn visit_stable_stats(self, mut visit: impl FnMut(&'static str, u64)) {
        visit(
            "solver_program.profile.enabled",
            u64::from(self.any_enabled()),
        );
        visit(
            "solver_program.profile.lra_sparse_substitute.enabled",
            u64::from(self.lra_sparse_substitute_enabled),
        );
        visit(
            "solver_program.profile.lra_basis_region.enabled",
            u64::from(self.lra_basis_region_enabled),
        );
        visit(
            "solver_program.profile.lia_bound_region.enabled",
            u64::from(self.lia_bound_region_enabled),
        );
        visit(
            "solver_program.profile.chc_expression.enabled",
            u64::from(self.chc_expression_enabled),
        );
        visit(
            "solver_program.profile.sat_conflict.enabled",
            u64::from(self.sat_conflict_enabled),
        );
        visit(
            "solver_program.profile.sat_inprocess.enabled",
            u64::from(self.sat_inprocess_enabled),
        );
        visit(
            "solver_program.profile.pb_kernel.enabled",
            u64::from(self.pb_kernel_enabled),
        );
    }
}

/// Stable flat counters for the external code generation LRA sparse-substitute family.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProgramLraSparseSubstituteStats {
    /// Compilation attempts considered by the sparse-substitute tier.
    pub compile_attempts: u64,
    /// Successful external code generation sparse-substitute compilations.
    pub compile_successes: u64,
    /// Failed, timed out, or unsupported sparse-substitute compilations.
    pub compile_failures: u64,
    /// Repeated compile attempts skipped by per-row backoff.
    pub compile_backoff_skips: u64,
    /// Runtime/profile disabled skips that kept execution on the generic path.
    pub disabled_skips: u64,
    /// Successful sparse-substitute applications served by the external code generation function.
    pub applies: u64,
    /// Successful compiled sparse-substitute wrapper applications.
    pub wrapper_applies: u64,
    /// Successful sparse-substitute applications served by the external code generation function.
    pub native_applies: u64,
    /// Successful empty-target applications served by the external code generation function.
    pub native_empty_target_applies: u64,
    /// Successful non-empty applications served by the external code generation function.
    pub native_non_empty_target_applies: u64,
    /// Successful applications served by the runtime wrapper.
    pub runtime_applies: u64,
    /// Sparse-substitute applications served by the generic solver path.
    pub fallback_applies: u64,
    /// Compiled applications that overflowed and used the generic path.
    pub overflow_fallbacks: u64,
    /// Background compile queue submissions.
    pub queue_submissions: u64,
    /// Background queue artifacts installed into the metadata cache.
    pub queue_installs: u64,
    /// Queue submissions rejected for exhausted compile budget.
    pub queue_budget_rejects: u64,
    /// Queue results dropped as stale or invalidated.
    pub stale_drops: u64,
    /// Total background compile latency in microseconds.
    pub queue_compile_us_total: u64,
    /// Maximum single background compile latency in microseconds.
    pub queue_compile_us_max: u64,
    /// Total submit-to-install latency in microseconds.
    pub queue_submit_to_install_us_total: u64,
    /// Maximum submit-to-install latency in microseconds.
    pub queue_submit_to_install_us_max: u64,
}

impl SolverProgramLraSparseSubstituteStats {
    #[must_use]
    fn fallbacks(self) -> u64 {
        self.fallback_applies.saturating_add(self.disabled_skips)
    }

    #[must_use]
    fn deopts(self) -> u64 {
        self.disabled_skips
            .saturating_add(self.compile_failures)
            .saturating_add(self.queue_budget_rejects)
            .saturating_add(self.stale_drops)
    }

    fn visit_stable_stats(self, mut visit: impl FnMut(&'static str, u64)) {
        visit(
            "solver_program.lra_sparse_substitute.compile_attempts",
            self.compile_attempts,
        );
        visit(
            "solver_program.lra_sparse_substitute.compile_successes",
            self.compile_successes,
        );
        visit(
            "solver_program.lra_sparse_substitute.compile_failures",
            self.compile_failures,
        );
        visit(
            "solver_program.lra_sparse_substitute.compile_backoff_skips",
            self.compile_backoff_skips,
        );
        visit(
            "solver_program.lra_sparse_substitute.disabled_fallbacks",
            self.disabled_skips,
        );
        visit("solver_program.lra_sparse_substitute.applies", self.applies);
        visit(
            "solver_program.lra_sparse_substitute.wrapper_applies",
            self.wrapper_applies,
        );
        visit(
            "solver_program.lra_sparse_substitute.native_applies",
            self.native_applies,
        );
        visit(
            "solver_program.lra_sparse_substitute.native_empty_target_applies",
            self.native_empty_target_applies,
        );
        visit(
            "solver_program.lra_sparse_substitute.native_non_empty_target_applies",
            self.native_non_empty_target_applies,
        );
        visit(
            "solver_program.lra_sparse_substitute.runtime_applies",
            self.runtime_applies,
        );
        visit(
            "solver_program.lra_sparse_substitute.fallback_applies",
            self.fallback_applies,
        );
        visit(
            "solver_program.lra_sparse_substitute.overflow_fallbacks",
            self.overflow_fallbacks,
        );
        visit(
            "solver_program.lra_sparse_substitute.fallbacks",
            self.fallbacks(),
        );
        visit(
            "solver_program.lra_sparse_substitute.queue_submissions",
            self.queue_submissions,
        );
        visit(
            "solver_program.lra_sparse_substitute.installs",
            self.queue_installs,
        );
        visit(
            "solver_program.lra_sparse_substitute.queue_budget_rejects",
            self.queue_budget_rejects,
        );
        visit(
            "solver_program.lra_sparse_substitute.stale_drops",
            self.stale_drops,
        );
        visit(
            "solver_program.lra_sparse_substitute.queue_compile_us_total",
            self.queue_compile_us_total,
        );
        visit(
            "solver_program.lra_sparse_substitute.queue_compile_us_max",
            self.queue_compile_us_max,
        );
        visit(
            "solver_program.lra_sparse_substitute.queue_submit_to_install_us_total",
            self.queue_submit_to_install_us_total,
        );
        visit(
            "solver_program.lra_sparse_substitute.queue_submit_to_install_us_max",
            self.queue_submit_to_install_us_max,
        );
        visit("solver_program.lra_sparse_substitute.deopts", self.deopts());
        visit(
            "solver_program.lra_sparse_substitute.deopts.disabled_by_policy",
            self.disabled_skips,
        );
        visit(
            "solver_program.lra_sparse_substitute.deopts.compile_budget_exceeded",
            self.queue_budget_rejects,
        );
        visit(
            "solver_program.lra_sparse_substitute.deopts.stale_invalidation_key",
            self.stale_drops,
        );
    }
}

/// Stable flat counters for the metadata-only LRA basis-region family.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProgramLraBasisRegionStats {
    /// Safe boundaries that considered a basis-region candidate.
    pub boundary_checks: u64,
    /// Metadata-only basis-region requests queued.
    pub requests_queued: u64,
    /// Runtime/profile disabled skips.
    pub disabled_skips: u64,
    /// Candidates rejected by conservative eligibility validation.
    pub ineligible_skips: u64,
    /// Candidates dropped because the metadata queue was full.
    pub queue_full_skips: u64,
    /// Background compile queue submissions.
    pub queue_submissions: u64,
    /// Background queue artifacts installed into the sparse-substitute cache.
    pub queue_installs: u64,
    /// Queue submissions rejected for exhausted compile budget.
    pub queue_budget_rejects: u64,
    /// Queue results dropped as stale or invalidated.
    pub stale_drops: u64,
    /// Basis-region lowering/runtime unsupported fallbacks.
    pub unsupported_fallbacks: u64,
    /// Basis-region compile failures.
    pub compile_failures: u64,
    /// Native sparse-substitute applies attributed to basis-region leaves.
    pub native_applies: u64,
    /// Batch sparse-substitute native applies attributed to basis-region leaves.
    pub batch_native_applies: u64,
    /// Total background compile latency in microseconds.
    pub queue_compile_us_total: u64,
    /// Maximum single background compile latency in microseconds.
    pub queue_compile_us_max: u64,
    /// Bounded evidence waits attempted after accepted submits.
    pub evidence_wait_attempts: u64,
    /// Evidence waits that installed an artifact inside the configured budget.
    pub evidence_wait_hits: u64,
    /// Evidence waits that reached the configured budget before install.
    pub evidence_wait_timeouts: u64,
    /// Total install polls performed by evidence waits.
    pub evidence_wait_polls: u64,
    /// Total evidence-wait wall time in microseconds.
    pub evidence_wait_us_total: u64,
}

impl SolverProgramLraBasisRegionStats {
    #[must_use]
    fn fallbacks(self) -> u64 {
        self.disabled_skips
            .saturating_add(self.ineligible_skips)
            .saturating_add(self.queue_full_skips)
    }

    fn visit_stable_stats(self, mut visit: impl FnMut(&'static str, u64)) {
        visit(
            "solver_program.lra_basis_region.boundary_checks",
            self.boundary_checks,
        );
        visit(
            "solver_program.lra_basis_region.requests_queued",
            self.requests_queued,
        );
        visit(
            "solver_program.lra_basis_region.disabled_fallbacks",
            self.disabled_skips,
        );
        visit(
            "solver_program.lra_basis_region.ineligible_fallbacks",
            self.ineligible_skips,
        );
        visit(
            "solver_program.lra_basis_region.queue_full_fallbacks",
            self.queue_full_skips,
        );
        visit(
            "solver_program.lra_basis_region.fallbacks",
            self.fallbacks(),
        );
        visit(
            "solver_program.lra_basis_region.queue_submissions",
            self.queue_submissions,
        );
        visit(
            "solver_program.lra_basis_region.installs",
            self.queue_installs,
        );
        visit(
            "solver_program.lra_basis_region.queue_budget_rejects",
            self.queue_budget_rejects,
        );
        visit(
            "solver_program.lra_basis_region.stale_drops",
            self.stale_drops,
        );
        visit(
            "solver_program.lra_basis_region.unsupported_fallbacks",
            self.unsupported_fallbacks,
        );
        visit(
            "solver_program.lra_basis_region.compile_failures",
            self.compile_failures,
        );
        visit(
            "solver_program.lra_basis_region.native_applies",
            self.native_applies,
        );
        visit(
            "solver_program.lra_basis_region.batch_native_applies",
            self.batch_native_applies,
        );
        visit(
            "solver_program.lra_basis_region.queue_compile_us_total",
            self.queue_compile_us_total,
        );
        visit(
            "solver_program.lra_basis_region.queue_compile_us_max",
            self.queue_compile_us_max,
        );
        visit(
            "solver_program.lra_basis_region.evidence_wait_attempts",
            self.evidence_wait_attempts,
        );
        visit(
            "solver_program.lra_basis_region.evidence_wait_hits",
            self.evidence_wait_hits,
        );
        visit(
            "solver_program.lra_basis_region.evidence_wait_timeouts",
            self.evidence_wait_timeouts,
        );
        visit(
            "solver_program.lra_basis_region.evidence_wait_polls",
            self.evidence_wait_polls,
        );
        visit(
            "solver_program.lra_basis_region.evidence_wait_us_total",
            self.evidence_wait_us_total,
        );
        visit(
            "solver_program.lra_basis_region.deopts.disabled_by_policy",
            self.disabled_skips,
        );
        visit(
            "solver_program.lra_basis_region.deopts.unsupported_contract",
            self.ineligible_skips,
        );
        visit(
            "solver_program.lra_basis_region.deopts.compile_budget_exceeded",
            self.queue_budget_rejects,
        );
        visit(
            "solver_program.lra_basis_region.deopts.stale_invalidation_key",
            self.stale_drops,
        );
        visit(
            "solver_program.lra_basis_region.deopts.compile_failure",
            self.compile_failures,
        );
    }
}

/// Stable flat stats bundle consumed by CLI stats JSON.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProgramStableStats {
    /// Artifact-kind profile toggles active for this solve.
    pub profile: SolverProgramProfileToggles,
    /// LRA sparse-substitute family counters.
    pub lra_sparse_substitute: SolverProgramLraSparseSubstituteStats,
    /// LRA basis-region family counters.
    pub lra_basis_region: SolverProgramLraBasisRegionStats,
}

impl SolverProgramStableStats {
    /// Build stable stats for the current LRA solver-program families.
    #[must_use]
    pub const fn lra(
        profile: SolverProgramProfileToggles,
        lra_sparse_substitute: SolverProgramLraSparseSubstituteStats,
        lra_basis_region: SolverProgramLraBasisRegionStats,
    ) -> Self {
        Self {
            profile,
            lra_sparse_substitute,
            lra_basis_region,
        }
    }

    /// Visit stable flat key/value pairs.
    pub fn visit_stable_stats(self, mut visit: impl FnMut(&'static str, u64)) {
        visit(
            "solver_program.schema_version",
            SOLVER_PROGRAM_STABLE_STATS_SCHEMA_VERSION,
        );
        self.profile.visit_stable_stats(&mut visit);
        self.lra_sparse_substitute.visit_stable_stats(&mut visit);
        self.lra_basis_region.visit_stable_stats(&mut visit);
    }

    /// Return stable flat key/value pairs suitable for `collect_statistics()`.
    #[must_use]
    pub fn rows(self) -> Vec<(&'static str, u64)> {
        let mut rows = Vec::new();
        self.visit_stable_stats(|key, value| rows.push((key, value)));
        rows
    }
}

impl SolverProgramLifecycleSnapshot {
    fn visit_stable_stats(&self, mut visit: impl FnMut(&'static str, u64)) {
        let counters = self.counters;
        visit(
            "solver_program.lifecycle.schema_version",
            u64::from(self.schema_version),
        );
        visit(
            "solver_program.lifecycle.queue_attempts",
            counters.queue_attempts,
        );
        visit(
            "solver_program.lifecycle.queue_accepted",
            counters.queue_accepted,
        );
        visit(
            "solver_program.lifecycle.queue_rejected",
            counters.queue_rejected,
        );
        visit(
            "solver_program.lifecycle.compile_successes",
            counters.compile_successes,
        );
        visit(
            "solver_program.lifecycle.compile_failures",
            counters.compile_failures,
        );
        visit(
            "solver_program.lifecycle.compile_latency_us_total",
            counters.compile_latency_us_total,
        );
        visit(
            "solver_program.lifecycle.compile_latency_us_max",
            counters.compile_latency_us_max,
        );
        visit(
            "solver_program.lifecycle.code_size_bytes_total",
            counters.code_size_bytes_total,
        );
        visit(
            "solver_program.lifecycle.code_size_bytes_max",
            counters.code_size_bytes_max,
        );
        visit(
            "solver_program.lifecycle.install_attempts",
            counters.install_attempts,
        );
        visit("solver_program.lifecycle.installs", counters.installs);
        visit(
            "solver_program.lifecycle.apply_attempts",
            counters.apply_attempts,
        );
        visit("solver_program.lifecycle.applies", counters.applies);
        visit("solver_program.lifecycle.guard_fails", counters.guard_fails);
        visit("solver_program.lifecycle.deopts", counters.deopts);
        visit("solver_program.lifecycle.fallbacks", counters.deopts);
        visit(
            "solver_program.lifecycle.samples_retained",
            usize_to_u64(self.samples.len()),
        );
        visit(
            "solver_program.lifecycle.samples_dropped",
            counters.samples_dropped,
        );
        visit(
            "solver_program.lifecycle.deopt.disabled_by_policy",
            counters.deopt_reasons.disabled_by_policy,
        );
        visit(
            "solver_program.lifecycle.deopt.backend_rejected",
            counters.deopt_reasons.backend_rejected,
        );
        visit(
            "solver_program.lifecycle.deopt.target_mismatch",
            counters.deopt_reasons.target_mismatch,
        );
        visit(
            "solver_program.lifecycle.deopt.stale_invalidation_key",
            counters.deopt_reasons.stale_invalidation_key,
        );
        visit(
            "solver_program.lifecycle.deopt.guard_failed",
            counters.deopt_reasons.guard_failed,
        );
        visit(
            "solver_program.lifecycle.deopt.unsafe_install_boundary",
            counters.deopt_reasons.unsafe_install_boundary,
        );
        visit(
            "solver_program.lifecycle.deopt.code_size_budget_exceeded",
            counters.deopt_reasons.code_size_budget_exceeded,
        );
        visit(
            "solver_program.lifecycle.deopt.compile_budget_exceeded",
            counters.deopt_reasons.compile_budget_exceeded,
        );
        visit(
            "solver_program.lifecycle.deopt.unsupported_contract",
            counters.deopt_reasons.unsupported_contract,
        );
    }

    #[cfg(test)]
    fn stable_stats_rows(&self) -> Vec<(&'static str, u64)> {
        let mut rows = Vec::new();
        self.visit_stable_stats(|key, value| rows.push((key, value)));
        rows
    }
}

/// Mutable lifecycle accountant for solver-program queue/install/apply events.
#[derive(Debug, Clone)]
pub(crate) struct SolverProgramLifecycleAccounting {
    policy: SolverProgramLifecyclePolicy,
    counters: SolverProgramLifecycleCounters,
    samples: VecDeque<SolverProgramLifecycleSample>,
    next_sequence: u64,
}

impl Default for SolverProgramLifecycleAccounting {
    fn default() -> Self {
        Self::new(SolverProgramLifecyclePolicy::default())
    }
}

impl SolverProgramLifecycleAccounting {
    /// Create lifecycle accounting with an explicit sample-retention policy.
    #[must_use]
    pub(crate) fn new(policy: SolverProgramLifecyclePolicy) -> Self {
        Self {
            policy,
            counters: SolverProgramLifecycleCounters::default(),
            samples: VecDeque::new(),
            next_sequence: 0,
        }
    }

    /// Current aggregate counters.
    #[must_use]
    pub(crate) fn counters(&self) -> &SolverProgramLifecycleCounters {
        &self.counters
    }

    /// Record a queue submission accepted for compilation.
    pub(crate) fn record_queue_accepted(
        &mut self,
        kind: SolverProgramKind,
        backend: SolverProgramBackend,
        request_id: Option<u64>,
    ) {
        saturating_inc(&mut self.counters.queue_attempts);
        saturating_inc(&mut self.counters.queue_accepted);
        self.push_sample(SolverProgramLifecycleSample::new(
            SolverProgramLifecycleEvent::Queue,
            kind,
            Some(backend),
            None,
            request_id,
        ));
    }

    /// Record a queue submission rejected before compilation.
    pub(crate) fn record_queue_rejected(
        &mut self,
        kind: SolverProgramKind,
        backend: SolverProgramBackend,
        request_id: Option<u64>,
        reason: DeoptReason,
    ) {
        saturating_inc(&mut self.counters.queue_attempts);
        saturating_inc(&mut self.counters.queue_rejected);
        self.counters.record_deopt(reason);
        self.push_sample(
            SolverProgramLifecycleSample::new(
                SolverProgramLifecycleEvent::Queue,
                kind,
                Some(backend),
                None,
                request_id,
            )
            .with_deopt_reason(reason),
        );
    }

    /// Record a successful compiler result and its latency/size metrics.
    pub(crate) fn record_compile_success(&mut self, meta: &SolverProgramArtifactMeta) {
        self.counters.record_compile_success(meta);
        self.push_sample(
            SolverProgramLifecycleSample::from_meta(SolverProgramLifecycleEvent::Compile, meta)
                .with_compile_metrics(meta),
        );
    }

    /// Record a compiler failure or unsupported result.
    pub(crate) fn record_compile_failure(
        &mut self,
        kind: SolverProgramKind,
        backend: SolverProgramBackend,
        request_id: Option<u64>,
        reason: DeoptReason,
    ) {
        saturating_inc(&mut self.counters.compile_failures);
        self.counters.record_deopt(reason);
        self.push_sample(
            SolverProgramLifecycleSample::new(
                SolverProgramLifecycleEvent::Compile,
                kind,
                Some(backend),
                None,
                request_id,
            )
            .with_deopt_reason(reason),
        );
    }

    /// Validate an install attempt and record the unchanged decision.
    pub(crate) fn validate_install_and_record(
        &mut self,
        meta: &SolverProgramArtifactMeta,
        runtime_key: InvalidationKey,
        runtime_target: &TargetFeatures,
        boundary: InstallBoundary,
        policy: InstallPolicy,
    ) -> InstallDecision {
        let decision = meta.validate_install(runtime_key, runtime_target, boundary, policy);
        self.record_install_decision(meta, boundary, decision);
        decision
    }

    /// Record an already-computed install decision.
    pub(crate) fn record_install_decision(
        &mut self,
        meta: &SolverProgramArtifactMeta,
        boundary: InstallBoundary,
        decision: InstallDecision,
    ) {
        saturating_inc(&mut self.counters.install_attempts);
        match decision {
            InstallDecision::Install => {
                saturating_inc(&mut self.counters.installs);
                self.push_sample(
                    SolverProgramLifecycleSample::from_meta(
                        SolverProgramLifecycleEvent::Install,
                        meta,
                    )
                    .with_boundary(boundary)
                    .with_compile_metrics(meta),
                );
            }
            InstallDecision::Deopt(reason) => {
                self.record_deopt_from_meta(meta, Some(boundary), reason);
            }
        }
    }

    /// Record a successful application of installed solver-program code.
    pub(crate) fn record_apply_success(&mut self, meta: &SolverProgramArtifactMeta) {
        saturating_inc(&mut self.counters.apply_attempts);
        saturating_inc(&mut self.counters.applies);
        self.push_sample(SolverProgramLifecycleSample::from_meta(
            SolverProgramLifecycleEvent::Apply,
            meta,
        ));
    }

    /// Validate apply-time guards and record the unchanged decision.
    pub(crate) fn validate_apply_and_record(
        &mut self,
        meta: &SolverProgramArtifactMeta,
        runtime_key: InvalidationKey,
        runtime_target: &TargetFeatures,
        oracle_check_passed: bool,
    ) -> ApplyDecision {
        let decision = meta.validate_apply(runtime_key, runtime_target, oracle_check_passed);
        self.record_apply_decision(meta, decision);
        decision
    }

    /// Record an already-computed apply decision.
    pub(crate) fn record_apply_decision(
        &mut self,
        meta: &SolverProgramArtifactMeta,
        decision: ApplyDecision,
    ) {
        match decision {
            ApplyDecision::Apply => self.record_apply_success(meta),
            ApplyDecision::Deopt(reason) => self.record_apply_deopt(meta, reason),
        }
    }

    /// Record a runtime guard/oracle failure before compiled code could apply.
    pub(crate) fn record_guard_fail(&mut self, meta: &SolverProgramArtifactMeta) {
        saturating_inc(&mut self.counters.apply_attempts);
        saturating_inc(&mut self.counters.guard_fails);
        self.counters.record_deopt(DeoptReason::GuardFailed);
        self.push_sample(
            SolverProgramLifecycleSample::from_meta(SolverProgramLifecycleEvent::GuardFail, meta)
                .with_deopt_reason(DeoptReason::GuardFailed),
        );
    }

    /// Record an apply attempt that deopted before native code ran.
    pub(crate) fn record_apply_deopt(
        &mut self,
        meta: &SolverProgramArtifactMeta,
        reason: DeoptReason,
    ) {
        saturating_inc(&mut self.counters.apply_attempts);
        if reason == DeoptReason::GuardFailed {
            saturating_inc(&mut self.counters.guard_fails);
        }
        self.record_deopt_from_meta(meta, None, reason);
    }

    /// Stable snapshot for stats surfaces.
    #[must_use]
    pub(crate) fn snapshot(&self) -> SolverProgramLifecycleSnapshot {
        SolverProgramLifecycleSnapshot {
            schema_version: SOLVER_PROGRAM_LIFECYCLE_SNAPSHOT_SCHEMA_VERSION,
            counters: self.counters,
            samples: self.samples.iter().cloned().collect(),
        }
    }

    fn record_deopt_from_meta(
        &mut self,
        meta: &SolverProgramArtifactMeta,
        boundary: Option<InstallBoundary>,
        reason: DeoptReason,
    ) {
        self.counters.record_deopt(reason);
        let mut sample =
            SolverProgramLifecycleSample::from_meta(SolverProgramLifecycleEvent::Deopt, meta)
                .with_deopt_reason(reason)
                .with_compile_metrics(meta);
        sample.boundary = boundary;
        self.push_sample(sample);
    }

    fn push_sample(&mut self, mut sample: SolverProgramLifecycleSample) {
        sample.sequence = self.next_sequence;
        self.next_sequence = self.next_sequence.saturating_add(1);
        if self.policy.max_samples == 0 {
            saturating_inc(&mut self.counters.samples_dropped);
            return;
        }
        while self.samples.len() >= self.policy.max_samples {
            if self.samples.pop_front().is_some() {
                saturating_inc(&mut self.counters.samples_dropped);
            }
        }
        self.samples.push_back(sample);
    }
}

fn saturating_inc(value: &mut u64) {
    *value = value.saturating_add(1);
}

fn usize_to_u64(value: usize) -> u64 {
    value.try_into().unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{de::DeserializeOwned, Serialize};
    use std::collections::BTreeMap;
    use std::fmt::Debug;

    fn assert_json_round_trip<T>(value: &T)
    where
        T: Serialize + DeserializeOwned + PartialEq + Debug,
    {
        let encoded = serde_json::to_string(value).expect("serialize value");
        let decoded: T = serde_json::from_str(&encoded).expect("deserialize value");
        assert_eq!(&decoded, value);
    }

    fn key() -> InvalidationKey {
        InvalidationKey {
            generations: SolverProgramGenerations {
                constraints: 1,
                theory_atoms: 2,
                basis: 3,
                trail: 4,
                config: 5,
            },
            shape_hash: 0x1234,
            semantic_hash: 0x5678,
        }
    }

    fn meta() -> SolverProgramArtifactMeta {
        SolverProgramArtifactMeta {
            schema_version: SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION,
            id: SolverProgramArtifactId(42),
            kind: SolverProgramKind::LraBasisRegion,
            backend: SolverProgramBackend::ExternalCodegenBackend,
            producer_version: 1,
            semantic_version: 0xfeed_beef,
            provenance: SolverProgramProvenance::LraBasisRegion {
                basis_generation: 3,
            },
            invalidation_key: key(),
            guard_requirements: GuardRequirements::conservative(),
            install_boundaries: InstallBoundarySet::restart_only(),
            target: TargetFeatures::current(),
            code_size_bytes: 4096,
            compile_latency_us: 1_000,
            stats_prefix: "solver_program.lra_basis".to_string(),
            request_id: Some(7),
        }
    }

    fn policy() -> InstallPolicy {
        InstallPolicy::allow_external_codegen_for_testing()
    }

    #[test]
    fn external_codegen_is_the_only_active_compiler_backend() {
        assert!(SolverProgramBackend::ExternalCodegenBackend.is_active_compiler());
        assert!(!SolverProgramBackend::NativeAssembler.is_active_compiler());
        assert!(!SolverProgramBackend::Interpreter.is_active_compiler());
    }

    #[test]
    fn default_install_policy_fails_closed() {
        let policy = InstallPolicy::default();
        assert!(!policy.compiled_solver_programs_enabled);
        assert!(policy.require_external_codegen);
        assert!(!policy.boundary_allowed(InstallBoundary::SolverStart));
        assert!(!policy.boundary_allowed(InstallBoundary::Restart));
        assert!(!policy.boundary_allowed(InstallBoundary::TheorySync));
        assert!(!policy.boundary_allowed(InstallBoundary::IncrementalBoundary));

        let decision = meta().validate_install(
            key(),
            &TargetFeatures::current(),
            InstallBoundary::Restart,
            policy,
        );
        assert_eq!(
            decision,
            InstallDecision::Deopt(DeoptReason::DisabledByPolicy)
        );
        assert!(!decision.is_install());
    }

    #[test]
    fn install_accepts_matching_external_codegen_artifact_when_policy_opts_in() {
        let meta = meta();
        let decision = meta.validate_install(
            key(),
            &TargetFeatures::current(),
            InstallBoundary::Restart,
            policy(),
        );
        assert_eq!(decision, InstallDecision::Install);
        assert!(decision.is_install());
    }

    #[test]
    fn install_rejects_non_external_codegen_native_backends_even_when_external_codegen_not_required(
    ) {
        let meta = SolverProgramArtifactMeta {
            backend: SolverProgramBackend::NativeAssembler,
            ..meta()
        };
        let policy = InstallPolicy {
            require_external_codegen: false,
            ..policy()
        };
        assert_eq!(
            meta.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                policy,
            ),
            InstallDecision::Deopt(DeoptReason::BackendRejected)
        );
    }

    #[test]
    fn install_rejects_interpreter_backend_even_when_external_codegen_not_required() {
        assert!(!SolverProgramBackend::Interpreter.is_native_installable());

        let meta = SolverProgramArtifactMeta {
            backend: SolverProgramBackend::Interpreter,
            ..meta()
        };
        let policy = InstallPolicy {
            require_external_codegen: false,
            ..policy()
        };
        assert_eq!(
            meta.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                policy,
            ),
            InstallDecision::Deopt(DeoptReason::BackendRejected)
        );
    }

    #[test]
    fn install_rejects_schema_mismatch() {
        let meta = SolverProgramArtifactMeta {
            schema_version: SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION + 1,
            ..meta()
        };
        assert_eq!(
            meta.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                policy(),
            ),
            InstallDecision::Deopt(DeoptReason::UnsupportedContract)
        );
    }

    #[test]
    fn install_rejects_incomplete_guard_contracts() {
        let guard_variants = [
            GuardRequirements {
                require_generation_match: false,
                ..GuardRequirements::conservative()
            },
            GuardRequirements {
                require_interpreter_fallback: false,
                ..GuardRequirements::conservative()
            },
            GuardRequirements {
                require_oracle_check: false,
                ..GuardRequirements::conservative()
            },
        ];

        for guard_requirements in guard_variants {
            let meta = SolverProgramArtifactMeta {
                guard_requirements,
                ..meta()
            };
            assert_eq!(
                meta.validate_install(
                    key(),
                    &TargetFeatures::current(),
                    InstallBoundary::Restart,
                    policy(),
                ),
                InstallDecision::Deopt(DeoptReason::UnsupportedContract)
            );
        }
    }

    #[test]
    fn install_rejects_mismatched_or_unknown_provenance() {
        let cases = [
            SolverProgramArtifactMeta {
                kind: SolverProgramKind::LraSparseSubstitute,
                provenance: SolverProgramProvenance::LraBasisRegion {
                    basis_generation: 3,
                },
                ..meta()
            },
            SolverProgramArtifactMeta {
                provenance: SolverProgramProvenance::Unknown,
                ..meta()
            },
        ];

        for meta in cases {
            assert_eq!(
                meta.validate_install(
                    key(),
                    &TargetFeatures::current(),
                    InstallBoundary::Restart,
                    policy(),
                ),
                InstallDecision::Deopt(DeoptReason::UnsupportedContract)
            );
        }
    }

    #[test]
    fn install_rejects_stale_invalidation_key() {
        let stale_runtime_keys = [
            InvalidationKey {
                generations: SolverProgramGenerations {
                    constraints: 99,
                    ..key().generations
                },
                ..key()
            },
            InvalidationKey {
                generations: SolverProgramGenerations {
                    theory_atoms: 99,
                    ..key().generations
                },
                ..key()
            },
            InvalidationKey {
                generations: SolverProgramGenerations {
                    basis: 99,
                    ..key().generations
                },
                ..key()
            },
            InvalidationKey {
                generations: SolverProgramGenerations {
                    trail: 99,
                    ..key().generations
                },
                ..key()
            },
            InvalidationKey {
                generations: SolverProgramGenerations {
                    config: 99,
                    ..key().generations
                },
                ..key()
            },
            InvalidationKey {
                shape_hash: 0xabcd,
                ..key()
            },
            InvalidationKey {
                semantic_hash: 0xabcd,
                ..key()
            },
        ];

        for stale_runtime_key in stale_runtime_keys {
            assert_eq!(
                meta().validate_install(
                    stale_runtime_key,
                    &TargetFeatures::current(),
                    InstallBoundary::Restart,
                    policy(),
                ),
                InstallDecision::Deopt(DeoptReason::StaleInvalidationKey)
            );
        }
    }

    #[test]
    fn target_feature_compatibility_is_exact_for_os_and_arch_with_feature_superset() {
        let arch_mismatch =
            TargetFeatures::new("unsupported-test-arch", std::env::consts::OS, Vec::new());
        assert_eq!(
            meta().validate_install(key(), &arch_mismatch, InstallBoundary::Restart, policy(),),
            InstallDecision::Deopt(DeoptReason::TargetMismatch)
        );

        let os_mismatch =
            TargetFeatures::new(std::env::consts::ARCH, "unsupported-test-os", Vec::new());
        assert_eq!(
            meta().validate_install(key(), &os_mismatch, InstallBoundary::Restart, policy(),),
            InstallDecision::Deopt(DeoptReason::TargetMismatch)
        );

        let meta_requires_feature = SolverProgramArtifactMeta {
            target: TargetFeatures {
                cpu_features: vec!["ay_test_feature".to_string()],
                ..TargetFeatures::current()
            },
            ..meta()
        };
        assert_eq!(
            meta_requires_feature.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                policy(),
            ),
            InstallDecision::Deopt(DeoptReason::TargetMismatch)
        );

        let runtime_superset = TargetFeatures {
            cpu_features: vec![
                "ay_test_feature".to_string(),
                "ay_test_extra_feature".to_string(),
            ],
            ..TargetFeatures::current()
        };
        assert_eq!(
            meta_requires_feature.validate_install(
                key(),
                &runtime_superset,
                InstallBoundary::Restart,
                policy(),
            ),
            InstallDecision::Install
        );
    }

    #[test]
    fn target_feature_metadata_must_be_canonical() {
        let unsorted = SolverProgramArtifactMeta {
            target: TargetFeatures {
                arch: std::env::consts::ARCH.to_string(),
                os: std::env::consts::OS.to_string(),
                cpu_features: vec!["ay_test_z".to_string(), "ay_test_a".to_string()],
            },
            ..meta()
        };
        assert_eq!(
            unsorted.validate_install(
                key(),
                &TargetFeatures::new(
                    std::env::consts::ARCH,
                    std::env::consts::OS,
                    vec!["ay_test_a".to_string(), "ay_test_z".to_string()]
                ),
                InstallBoundary::Restart,
                policy(),
            ),
            InstallDecision::Deopt(DeoptReason::UnsupportedContract)
        );

        let duplicate = SolverProgramArtifactMeta {
            target: TargetFeatures {
                arch: std::env::consts::ARCH.to_string(),
                os: std::env::consts::OS.to_string(),
                cpu_features: vec!["ay_test_a".to_string(), "ay_test_a".to_string()],
            },
            ..meta()
        };
        assert_eq!(
            duplicate.validate_install(
                key(),
                &TargetFeatures::new(
                    std::env::consts::ARCH,
                    std::env::consts::OS,
                    vec!["ay_test_a".to_string()]
                ),
                InstallBoundary::Restart,
                policy(),
            ),
            InstallDecision::Deopt(DeoptReason::UnsupportedContract)
        );

        assert_eq!(
            TargetFeatures::new(
                "ay_test_arch",
                "ay_test_os",
                vec![
                    "ay_test_z".to_string(),
                    "ay_test_a".to_string(),
                    "ay_test_a".to_string()
                ],
            )
            .cpu_features,
            vec!["ay_test_a".to_string(), "ay_test_z".to_string()]
        );
    }

    #[test]
    fn install_policy_controls_boundaries_and_budgets() {
        let reject_restart_policy = InstallPolicy {
            allow_restart_install: false,
            ..policy()
        };
        assert_eq!(
            meta().validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                reject_restart_policy,
            ),
            InstallDecision::Deopt(DeoptReason::UnsafeInstallBoundary)
        );

        let small_budget_policy = InstallPolicy {
            max_code_size_bytes: 128,
            ..policy()
        };
        assert_eq!(
            meta().validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                small_budget_policy,
            ),
            InstallDecision::Deopt(DeoptReason::CodeSizeBudgetExceeded)
        );
    }

    #[test]
    fn install_boundary_set_is_fail_closed_and_exact() {
        let default_boundaries = InstallBoundarySet::default();
        assert!(!default_boundaries.allows(InstallBoundary::SolverStart));
        assert!(!default_boundaries.allows(InstallBoundary::Restart));
        assert!(!default_boundaries.allows(InstallBoundary::TheorySync));
        assert!(!default_boundaries.allows(InstallBoundary::IncrementalBoundary));

        let restart_only = InstallBoundarySet::restart_only();
        assert!(!restart_only.allows(InstallBoundary::SolverStart));
        assert!(restart_only.allows(InstallBoundary::Restart));
        assert!(!restart_only.allows(InstallBoundary::TheorySync));
        assert!(!restart_only.allows(InstallBoundary::IncrementalBoundary));

        let meta = meta();
        assert_eq!(
            meta.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::SolverStart,
                policy(),
            ),
            InstallDecision::Deopt(DeoptReason::UnsafeInstallBoundary)
        );
    }

    #[test]
    fn lifecycle_accounting_records_queue_compile_install_and_apply() {
        let meta = meta();
        let mut lifecycle =
            SolverProgramLifecycleAccounting::new(SolverProgramLifecyclePolicy { max_samples: 8 });

        lifecycle.record_queue_accepted(meta.kind, meta.backend, meta.request_id);
        lifecycle.record_compile_success(&meta);
        lifecycle.record_install_decision(
            &meta,
            InstallBoundary::Restart,
            InstallDecision::Install,
        );
        lifecycle.record_apply_success(&meta);

        let snapshot = lifecycle.snapshot();
        assert_eq!(
            snapshot.schema_version,
            SOLVER_PROGRAM_LIFECYCLE_SNAPSHOT_SCHEMA_VERSION
        );
        assert_eq!(snapshot.counters.queue_attempts, 1);
        assert_eq!(snapshot.counters.queue_accepted, 1);
        assert_eq!(snapshot.counters.queue_rejected, 0);
        assert_eq!(snapshot.counters.compile_successes, 1);
        assert_eq!(snapshot.counters.compile_failures, 0);
        assert_eq!(snapshot.counters.compile_latency_us_total, 1_000);
        assert_eq!(snapshot.counters.compile_latency_us_max, 1_000);
        assert_eq!(snapshot.counters.code_size_bytes_total, 4096);
        assert_eq!(snapshot.counters.code_size_bytes_max, 4096);
        assert_eq!(snapshot.counters.install_attempts, 1);
        assert_eq!(snapshot.counters.installs, 1);
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 1);
        assert_eq!(snapshot.counters.deopts, 0);
        assert_eq!(snapshot.counters.deopt_reasons.total(), 0);
        assert_eq!(snapshot.counters.samples_dropped, 0);
        assert_eq!(
            lifecycle.counters().compile_latency_us_total,
            meta.compile_latency_us
        );

        let events: Vec<_> = snapshot.samples.iter().map(|sample| sample.event).collect();
        assert_eq!(
            events,
            vec![
                SolverProgramLifecycleEvent::Queue,
                SolverProgramLifecycleEvent::Compile,
                SolverProgramLifecycleEvent::Install,
                SolverProgramLifecycleEvent::Apply,
            ]
        );
        assert_eq!(snapshot.samples[0].sequence, 0);
        assert_eq!(snapshot.samples[1].sequence, 1);
        assert_eq!(snapshot.samples[1].code_size_bytes, Some(4096));
        assert_eq!(snapshot.samples[1].compile_latency_us, Some(1_000));
        assert_eq!(snapshot.samples[2].boundary, Some(InstallBoundary::Restart));
        assert_json_round_trip(&snapshot);
    }

    #[test]
    fn lifecycle_validate_install_preserves_default_fail_closed_policy() {
        let meta = meta();
        let mut lifecycle = SolverProgramLifecycleAccounting::default();
        let decision = lifecycle.validate_install_and_record(
            &meta,
            key(),
            &TargetFeatures::current(),
            InstallBoundary::Restart,
            InstallPolicy::default(),
        );

        assert_eq!(
            decision,
            InstallDecision::Deopt(DeoptReason::DisabledByPolicy)
        );
        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.install_attempts, 1);
        assert_eq!(snapshot.counters.installs, 0);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.disabled_by_policy, 1);
        assert_eq!(snapshot.counters.deopt_reasons.total(), 1);
        assert_eq!(snapshot.samples.len(), 1);
        assert_eq!(
            snapshot.samples[0].event,
            SolverProgramLifecycleEvent::Deopt
        );
        assert_eq!(
            snapshot.samples[0].deopt_reason,
            Some(DeoptReason::DisabledByPolicy)
        );
    }

    #[test]
    fn lifecycle_guard_fail_counts_as_apply_attempt_and_deopt() {
        let meta = meta();
        let mut lifecycle = SolverProgramLifecycleAccounting::default();

        lifecycle.record_guard_fail(&meta);

        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 0);
        assert_eq!(snapshot.counters.guard_fails, 1);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.guard_failed, 1);
        assert_eq!(snapshot.counters.deopt_reasons.total(), 1);
        assert_eq!(snapshot.samples.len(), 1);
        assert_eq!(
            snapshot.samples[0].event,
            SolverProgramLifecycleEvent::GuardFail
        );
        assert_eq!(
            snapshot.samples[0].deopt_reason,
            Some(DeoptReason::GuardFailed)
        );
    }

    #[test]
    fn apply_validation_rechecks_runtime_guards_before_native_dispatch() {
        let meta = meta();
        assert_eq!(
            meta.validate_apply(key(), &TargetFeatures::current(), true),
            ApplyDecision::Apply
        );
        assert!(meta
            .validate_apply(key(), &TargetFeatures::current(), true)
            .is_apply());

        let stale_key = InvalidationKey {
            generations: SolverProgramGenerations {
                basis: 99,
                ..key().generations
            },
            ..key()
        };
        assert_eq!(
            meta.validate_apply(stale_key, &TargetFeatures::current(), true),
            ApplyDecision::Deopt(DeoptReason::StaleInvalidationKey)
        );

        let mismatched_target =
            TargetFeatures::new("unsupported-test-arch", std::env::consts::OS, Vec::new());
        assert_eq!(
            meta.validate_apply(key(), &mismatched_target, true),
            ApplyDecision::Deopt(DeoptReason::TargetMismatch)
        );

        assert_eq!(
            meta.validate_apply(key(), &TargetFeatures::current(), false),
            ApplyDecision::Deopt(DeoptReason::GuardFailed)
        );
    }

    #[test]
    fn lifecycle_apply_validation_counts_guard_failure_without_counting_apply() {
        let meta = meta();
        let mut lifecycle = SolverProgramLifecycleAccounting::default();

        let decision =
            lifecycle.validate_apply_and_record(&meta, key(), &TargetFeatures::current(), false);

        assert_eq!(decision, ApplyDecision::Deopt(DeoptReason::GuardFailed));
        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 0);
        assert_eq!(snapshot.counters.guard_fails, 1);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.guard_failed, 1);
        assert_eq!(snapshot.counters.deopt_reasons.total(), 1);
        assert_eq!(snapshot.samples.len(), 1);
        assert_eq!(
            snapshot.samples[0].event,
            SolverProgramLifecycleEvent::Deopt
        );
        assert_eq!(
            snapshot.samples[0].deopt_reason,
            Some(DeoptReason::GuardFailed)
        );
    }

    #[test]
    fn lifecycle_apply_validation_keeps_stale_key_separate_from_guard_failure() {
        let meta = meta();
        let stale_key = InvalidationKey {
            shape_hash: 0xabcd,
            ..key()
        };
        let mut lifecycle = SolverProgramLifecycleAccounting::default();

        let decision =
            lifecycle.validate_apply_and_record(&meta, stale_key, &TargetFeatures::current(), true);

        assert_eq!(
            decision,
            ApplyDecision::Deopt(DeoptReason::StaleInvalidationKey)
        );
        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 0);
        assert_eq!(snapshot.counters.guard_fails, 0);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.stale_invalidation_key, 1);
        assert_eq!(snapshot.counters.deopt_reasons.guard_failed, 0);
    }

    #[test]
    fn lifecycle_apply_validation_counts_successful_native_apply() {
        let meta = meta();
        let mut lifecycle = SolverProgramLifecycleAccounting::default();

        let decision =
            lifecycle.validate_apply_and_record(&meta, key(), &TargetFeatures::current(), true);

        assert_eq!(decision, ApplyDecision::Apply);
        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 1);
        assert_eq!(snapshot.counters.guard_fails, 0);
        assert_eq!(snapshot.counters.deopts, 0);
        assert_eq!(snapshot.samples.len(), 1);
        assert_eq!(
            snapshot.samples[0].event,
            SolverProgramLifecycleEvent::Apply
        );
    }

    #[test]
    fn lifecycle_samples_are_bounded_without_losing_counters() {
        let mut lifecycle =
            SolverProgramLifecycleAccounting::new(SolverProgramLifecyclePolicy { max_samples: 2 });

        lifecycle.record_queue_accepted(
            SolverProgramKind::LraSparseSubstitute,
            SolverProgramBackend::ExternalCodegenBackend,
            Some(1),
        );
        lifecycle.record_queue_accepted(
            SolverProgramKind::LraBasisRegion,
            SolverProgramBackend::ExternalCodegenBackend,
            Some(2),
        );
        lifecycle.record_queue_rejected(
            SolverProgramKind::ChcExpression,
            SolverProgramBackend::ExternalCodegenBackend,
            Some(3),
            DeoptReason::CompileBudgetExceeded,
        );

        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.queue_attempts, 3);
        assert_eq!(snapshot.counters.queue_accepted, 2);
        assert_eq!(snapshot.counters.queue_rejected, 1);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.compile_budget_exceeded, 1);
        assert_eq!(snapshot.counters.samples_dropped, 1);
        assert_eq!(snapshot.samples.len(), 2);
        assert_eq!(snapshot.samples[0].sequence, 1);
        assert_eq!(snapshot.samples[1].sequence, 2);
        assert_eq!(snapshot.samples[1].request_id, Some(3));
        assert_eq!(
            snapshot.samples[1].deopt_reason,
            Some(DeoptReason::CompileBudgetExceeded)
        );
    }

    #[test]
    fn lifecycle_backend_rejection_keeps_backend_evidence() {
        let meta = SolverProgramArtifactMeta {
            backend: SolverProgramBackend::NativeAssembler,
            ..meta()
        };
        let mut lifecycle = SolverProgramLifecycleAccounting::default();
        let decision = lifecycle.validate_install_and_record(
            &meta,
            key(),
            &TargetFeatures::current(),
            InstallBoundary::Restart,
            policy(),
        );

        assert_eq!(
            decision,
            InstallDecision::Deopt(DeoptReason::BackendRejected)
        );
        let snapshot = lifecycle.snapshot();
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.backend_rejected, 1);
        assert_eq!(
            snapshot.samples[0].backend,
            Some(SolverProgramBackend::NativeAssembler)
        );
        assert_eq!(
            snapshot.samples[0].deopt_reason,
            Some(DeoptReason::BackendRejected)
        );
    }

    #[test]
    fn stable_lra_stats_rows_use_solver_program_namespace() {
        let stats = SolverProgramStableStats::lra(
            SolverProgramProfileToggles::lra(false, true),
            SolverProgramLraSparseSubstituteStats {
                compile_attempts: 11,
                compile_successes: 5,
                compile_failures: 2,
                compile_backoff_skips: 1,
                disabled_skips: 3,
                applies: 7,
                wrapper_applies: 8,
                native_applies: 7,
                native_empty_target_applies: 6,
                native_non_empty_target_applies: 1,
                runtime_applies: 9,
                fallback_applies: 13,
                overflow_fallbacks: 17,
                queue_submissions: 19,
                queue_installs: 23,
                queue_budget_rejects: 29,
                stale_drops: 31,
                queue_compile_us_total: 37,
                queue_compile_us_max: 41,
                queue_submit_to_install_us_total: 43,
                queue_submit_to_install_us_max: 47,
            },
            SolverProgramLraBasisRegionStats {
                boundary_checks: 53,
                requests_queued: 59,
                disabled_skips: 61,
                ineligible_skips: 67,
                queue_full_skips: 71,
                queue_submissions: 73,
                queue_installs: 79,
                queue_budget_rejects: 83,
                stale_drops: 89,
                unsupported_fallbacks: 97,
                compile_failures: 101,
                native_applies: 103,
                batch_native_applies: 105,
                queue_compile_us_total: 107,
                queue_compile_us_max: 109,
                evidence_wait_attempts: 113,
                evidence_wait_hits: 127,
                evidence_wait_timeouts: 131,
                evidence_wait_polls: 137,
                evidence_wait_us_total: 139,
            },
        );
        let rows: BTreeMap<_, _> = stats.rows().into_iter().collect();

        assert_eq!(
            rows["solver_program.schema_version"],
            SOLVER_PROGRAM_STABLE_STATS_SCHEMA_VERSION
        );
        assert_eq!(rows["solver_program.profile.enabled"], 1);
        assert_eq!(
            rows["solver_program.profile.lra_sparse_substitute.enabled"],
            0
        );
        assert_eq!(rows["solver_program.profile.lra_basis_region.enabled"], 1);
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.compile_attempts"],
            11
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.disabled_fallbacks"],
            3
        );
        assert_eq!(rows["solver_program.lra_sparse_substitute.applies"], 7);
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.wrapper_applies"],
            8
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.native_applies"],
            7
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.native_empty_target_applies"],
            6
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.native_non_empty_target_applies"],
            1
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.runtime_applies"],
            9
        );
        assert_eq!(rows["solver_program.lra_sparse_substitute.fallbacks"], 16);
        assert_eq!(rows["solver_program.lra_sparse_substitute.deopts"], 65);
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.deopts.disabled_by_policy"],
            3
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.deopts.compile_budget_exceeded"],
            29
        );
        assert_eq!(
            rows["solver_program.lra_sparse_substitute.deopts.stale_invalidation_key"],
            31
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.disabled_fallbacks"],
            61
        );
        assert_eq!(rows["solver_program.lra_basis_region.fallbacks"], 199);
        assert_eq!(
            rows["solver_program.lra_basis_region.deopts.disabled_by_policy"],
            61
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.queue_submissions"],
            73
        );
        assert_eq!(rows["solver_program.lra_basis_region.installs"], 79);
        assert_eq!(
            rows["solver_program.lra_basis_region.queue_budget_rejects"],
            83
        );
        assert_eq!(rows["solver_program.lra_basis_region.stale_drops"], 89);
        assert_eq!(
            rows["solver_program.lra_basis_region.unsupported_fallbacks"],
            97
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.compile_failures"],
            101
        );
        assert_eq!(rows["solver_program.lra_basis_region.native_applies"], 103);
        assert_eq!(
            rows["solver_program.lra_basis_region.batch_native_applies"],
            105
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.queue_compile_us_total"],
            107
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.queue_compile_us_max"],
            109
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.evidence_wait_attempts"],
            113
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.evidence_wait_hits"],
            127
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.evidence_wait_timeouts"],
            131
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.evidence_wait_polls"],
            137
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.evidence_wait_us_total"],
            139
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.deopts.compile_budget_exceeded"],
            83
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.deopts.stale_invalidation_key"],
            89
        );
        assert_eq!(
            rows["solver_program.lra_basis_region.deopts.compile_failure"],
            101
        );

        for key in rows.keys() {
            assert!(
                key.starts_with("solver_program."),
                "stable solver-program stats key should use the solver_program namespace: {key}"
            );
        }
    }

    #[test]
    fn lifecycle_stable_rows_expose_disabled_fallback_and_deopt_reasons() {
        let meta = meta();
        let mut lifecycle =
            SolverProgramLifecycleAccounting::new(SolverProgramLifecyclePolicy { max_samples: 1 });

        lifecycle.record_queue_rejected(
            meta.kind,
            meta.backend,
            meta.request_id,
            DeoptReason::DisabledByPolicy,
        );
        lifecycle.record_guard_fail(&meta);

        let rows: BTreeMap<_, _> = lifecycle
            .snapshot()
            .stable_stats_rows()
            .into_iter()
            .collect();
        assert_eq!(
            rows["solver_program.lifecycle.schema_version"],
            u64::from(SOLVER_PROGRAM_LIFECYCLE_SNAPSHOT_SCHEMA_VERSION)
        );
        assert_eq!(rows["solver_program.lifecycle.queue_attempts"], 1);
        assert_eq!(rows["solver_program.lifecycle.queue_rejected"], 1);
        assert_eq!(rows["solver_program.lifecycle.guard_fails"], 1);
        assert_eq!(rows["solver_program.lifecycle.deopts"], 2);
        assert_eq!(rows["solver_program.lifecycle.fallbacks"], 2);
        assert_eq!(rows["solver_program.lifecycle.samples_retained"], 1);
        assert_eq!(rows["solver_program.lifecycle.samples_dropped"], 1);
        assert_eq!(rows["solver_program.lifecycle.deopt.disabled_by_policy"], 1);
        assert_eq!(rows["solver_program.lifecycle.deopt.guard_failed"], 1);
    }

    #[test]
    fn metadata_round_trips_with_schema_and_provenance() {
        let meta = SolverProgramArtifactMeta {
            kind: SolverProgramKind::LraSparseSubstitute,
            provenance: SolverProgramProvenance::LraSparseSubstitute {
                entering_var: 11,
                pivot_terms: 3,
            },
            stats_prefix: "solver_program.lra_sparse_substitute".to_string(),
            ..meta()
        };
        let value = serde_json::to_value(&meta).expect("serialize metadata as value");
        assert_eq!(
            value["schema_version"],
            SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION
        );
        assert_eq!(value["backend"], "external_codegen_backend");
        assert_eq!(value["kind"], "lra_sparse_substitute");
        assert_eq!(
            value["provenance"],
            serde_json::json!({
                "lra_sparse_substitute": {
                    "entering_var": 11,
                    "pivot_terms": 3
                }
            })
        );

        let encoded = serde_json::to_string(&meta).expect("serialize metadata");
        assert!(encoded.contains("\"schema_version\":1"));
        assert!(encoded.contains("\"provenance\""));
        assert!(encoded.contains("\"stats_prefix\""));

        let decoded: SolverProgramArtifactMeta =
            serde_json::from_str(&encoded).expect("deserialize metadata");
        assert_eq!(decoded, meta);
    }

    #[test]
    fn contract_enums_round_trip_with_stable_json_names() {
        for backend in [
            SolverProgramBackend::ExternalCodegenBackend,
            SolverProgramBackend::NativeAssembler,
            SolverProgramBackend::Interpreter,
        ] {
            assert_json_round_trip(&backend);
        }
        assert_eq!(
            serde_json::to_string(&SolverProgramBackend::ExternalCodegenBackend)
                .expect("serialize backend"),
            "\"external_codegen_backend\""
        );

        for boundary in [
            InstallBoundary::SolverStart,
            InstallBoundary::Restart,
            InstallBoundary::TheorySync,
            InstallBoundary::IncrementalBoundary,
        ] {
            assert_json_round_trip(&boundary);
        }
        assert_eq!(
            serde_json::to_string(&InstallBoundary::IncrementalBoundary)
                .expect("serialize boundary"),
            "\"incremental_boundary\""
        );
        assert_eq!(
            serde_json::to_string(&InstallDecision::Deopt(DeoptReason::BackendRejected))
                .expect("serialize deopt decision"),
            "{\"deopt\":\"backend_rejected\"}"
        );
        assert_eq!(
            serde_json::to_string(&DeoptReason::GuardFailed).expect("serialize guard fail"),
            "\"guard_failed\""
        );

        assert_json_round_trip(&InstallPolicy::default());
        assert_json_round_trip(&SolverProgramLifecyclePolicy::default());
        assert_json_round_trip(&SolverProgramLifecycleEvent::GuardFail);
        assert_json_round_trip(&InstallDecision::Deopt(DeoptReason::BackendRejected));
        assert_json_round_trip(&ApplyDecision::Deopt(DeoptReason::GuardFailed));
        assert_json_round_trip(&SolverProgramCompileResult::Compiled(Box::new(meta())));
        assert_json_round_trip(&SolverProgramCompileResult::Unsupported {
            kind: SolverProgramKind::PbKernel,
            reason: DeoptReason::UnsupportedContract,
        });
        assert_json_round_trip(&SolverProgramProvenance::LraSparseSubstitute {
            entering_var: 11,
            pivot_terms: 3,
        });
        assert_json_round_trip(&SolverProgramProvenance::LraBasisRegion {
            basis_generation: 3,
        });
        assert_json_round_trip(&SolverProgramProvenance::ChcExpression { expr_hash: 0xfeed });
        assert_json_round_trip(&SolverProgramProvenance::SatWholeLoop {
            num_vars: 128,
            irredundant_clauses: 256,
            clause_shape_hash: 0x51a7,
        });
        assert_json_round_trip(&SolverProgramProvenance::Unknown);
    }

    #[test]
    fn sat_whole_loop_provenance_matches_only_whole_loop_artifacts() {
        let provenance = SolverProgramProvenance::SatWholeLoop {
            num_vars: 128,
            irredundant_clauses: 256,
            clause_shape_hash: 0x51a7,
        };

        assert!(provenance.matches_kind(SolverProgramKind::SatWholeLoop));
        assert!(!provenance.matches_kind(SolverProgramKind::SatConflict));
        assert!(!provenance.matches_kind(SolverProgramKind::LraBasisRegion));

        let meta = SolverProgramArtifactMeta {
            kind: SolverProgramKind::SatWholeLoop,
            provenance,
            install_boundaries: InstallBoundarySet::solver_start_only(),
            stats_prefix: "solver_program.sat_whole_loop".to_string(),
            ..meta()
        };

        assert_eq!(
            meta.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::SolverStart,
                policy(),
            ),
            InstallDecision::Install
        );
        assert_eq!(
            meta.validate_install(
                key(),
                &TargetFeatures::current(),
                InstallBoundary::Restart,
                policy(),
            ),
            InstallDecision::Deopt(DeoptReason::UnsafeInstallBoundary)
        );
    }
}
