// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Async compiler service for solver-program artifacts (#8875).
//!
//! This service is the external code generation-first successor to the older row-local
//! external backend tier. It owns request/result typing, enqueue budgeting, and stale-artifact
//! cancellation/drop behavior. Solver integration is intentionally separate:
//! callers submit canonical solver-program requests and later poll installable
//! results at safe boundaries.

use ay_core::time::Instant;
use std::fmt;
use std::panic::UnwindSafe;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

use crate::lra_region::{LraBasisRegionRequest, LraBasisRegionRuntimePayload};
use crate::solver_program::{
    DeoptReason, GuardRequirements, InstallBoundarySet, InvalidationKey, SolverProgramArtifactId,
    SolverProgramArtifactMeta, SolverProgramBackend, SolverProgramCompileResult, SolverProgramKind,
    SolverProgramProvenance, TargetFeatures, SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION,
};

/// Default total background compiler budget per solve.
const DEFAULT_TOTAL_BUDGET_US: u64 = 500_000;

/// Default per-artifact timeout for production solver-program compiles.
const DEFAULT_PER_ARTIFACT_TIMEOUT_US: u64 = 50_000;

/// Default lower bound used when a caller does not yet have a precise estimate.
const DEFAULT_MIN_RESERVATION_US: u64 = 1_000;

/// Default maximum number of queued or running solver-program compiles.
const DEFAULT_MAX_IN_FLIGHT: u64 = 64;

/// Producer version for ay-side external code generation solver-program artifacts.
const EXTERNAL_CODEGEN_IR_SOLVER_PROGRAM_PRODUCER_VERSION: u32 = 1;

/// Static SAT formulas above this size require selective baking before whole-loop lowering.
const SAT_WHOLE_LOOP_SELECTIVE_BAKING_CLAUSE_LIMIT: u32 = 10_000;

/// Stable request identity assigned by the async compiler service.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SolverProgramCompileRequestId(pub(crate) u64);

/// Background compiler budget and queue limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SolverProgramCompilerBudget {
    /// Total compile time budget available to this service instance.
    pub(crate) total_budget_us: u64,
    /// Drop any individual result whose compile time exceeds this limit.
    pub(crate) per_artifact_timeout_us: u64,
    /// Minimum budget reservation for one accepted request.
    pub(crate) min_reservation_us: u64,
    /// Maximum number of queued or running requests.
    pub(crate) max_in_flight: u64,
}

impl Default for SolverProgramCompilerBudget {
    fn default() -> Self {
        Self {
            total_budget_us: DEFAULT_TOTAL_BUDGET_US,
            per_artifact_timeout_us: DEFAULT_PER_ARTIFACT_TIMEOUT_US,
            min_reservation_us: DEFAULT_MIN_RESERVATION_US,
            max_in_flight: DEFAULT_MAX_IN_FLIGHT,
        }
    }
}

/// Runtime configuration for the async compiler service.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SolverProgramCompilerConfig {
    /// Global enable bit for enqueueing solver-program compiler work.
    pub(crate) enabled: bool,
    /// Budget and queue limits for the background compiler.
    pub(crate) budget: SolverProgramCompilerBudget,
}

impl Default for SolverProgramCompilerConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            budget: SolverProgramCompilerBudget::default(),
        }
    }
}

/// Solver-program region payload accepted by the external code generation compiler service.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SolverProgramCompilePayload {
    /// Compile a sparse LRA `substitute_var` kernel from one pivot row.
    LraSparseSubstitute {
        /// Sorted non-zero pivot coefficients captured at request time.
        coefficients: Vec<(u32, i64)>,
        /// Variable eliminated from the target row.
        entering_var: u32,
    },
    /// Compile a guarded basis-local LRA region payload.
    LraBasisRegion {
        /// Basis generation captured at request time.
        basis_generation: u64,
        /// Typed row payload captured at a safe LRA boundary.
        payload: LraBasisRegionRuntimePayload,
    },
    /// Compile a whole CDCL loop for one static SAT formula profile.
    SatWholeLoop {
        /// SAT variables captured in the static formula profile.
        num_vars: u32,
        /// Irredundant clauses captured at compile-request time.
        irredundant_clauses: u32,
        /// Stable hash of static clause-length and literal-shape metadata.
        clause_shape_hash: u64,
    },
}

impl SolverProgramCompilePayload {
    #[must_use]
    pub(crate) fn kind(&self) -> SolverProgramKind {
        match self {
            Self::LraSparseSubstitute { .. } => SolverProgramKind::LraSparseSubstitute,
            Self::LraBasisRegion { .. } => SolverProgramKind::LraBasisRegion,
            Self::SatWholeLoop { .. } => SolverProgramKind::SatWholeLoop,
        }
    }

    #[must_use]
    fn default_provenance(&self) -> SolverProgramProvenance {
        match self {
            Self::LraSparseSubstitute {
                coefficients,
                entering_var,
            } => {
                let pivot_terms = coefficients
                    .iter()
                    .filter(|(var, _)| var != entering_var)
                    .count() as u32;
                SolverProgramProvenance::LraSparseSubstitute {
                    entering_var: *entering_var,
                    pivot_terms,
                }
            }
            Self::LraBasisRegion {
                basis_generation, ..
            } => SolverProgramProvenance::LraBasisRegion {
                basis_generation: *basis_generation,
            },
            Self::SatWholeLoop {
                num_vars,
                irredundant_clauses,
                clause_shape_hash,
            } => SolverProgramProvenance::SatWholeLoop {
                num_vars: *num_vars,
                irredundant_clauses: *irredundant_clauses,
                clause_shape_hash: *clause_shape_hash,
            },
        }
    }
}

/// Canonical request consumed by the async external code generation compiler service.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SolverProgramCompilerRequest {
    /// Region payload to lower through ExternalCodegenIr and EXTERNAL_CODEGEN.
    pub(crate) payload: SolverProgramCompilePayload,
    /// Invalidation key captured at request time.
    pub(crate) invalidation_key: InvalidationKey,
    /// Source-level provenance used for metadata and audit trails.
    pub(crate) provenance: SolverProgramProvenance,
    /// Guard/oracle contract required by the produced artifact.
    pub(crate) guard_requirements: GuardRequirements,
    /// Boundaries at which the result may later be installed.
    pub(crate) install_boundaries: InstallBoundarySet,
    /// Target assumptions captured at request time.
    pub(crate) target: TargetFeatures,
    /// Semantic version/hash for normalization and lowering policy.
    pub(crate) semantic_version: u64,
    /// Stable stats prefix for this artifact family.
    pub(crate) stats_prefix: String,
    /// Budget reservation hint used before enqueueing.
    pub(crate) estimated_compile_us: u64,
    /// Expected native code size until the backend exposes exact code size.
    pub(crate) estimated_code_size_bytes: u64,
}

impl SolverProgramCompilerRequest {
    /// Build a sparse-substitute request from the #8874 artifact contract.
    #[must_use]
    pub(crate) fn lra_sparse_substitute(
        coefficients: Vec<(u32, i64)>,
        entering_var: u32,
        invalidation_key: InvalidationKey,
    ) -> Self {
        let payload = SolverProgramCompilePayload::LraSparseSubstitute {
            coefficients,
            entering_var,
        };
        Self {
            provenance: payload.default_provenance(),
            payload,
            invalidation_key,
            guard_requirements: GuardRequirements::conservative(),
            install_boundaries: InstallBoundarySet::restart_only(),
            target: TargetFeatures::current(),
            semantic_version: invalidation_key.semantic_hash,
            stats_prefix: "solver_program.lra_sparse_substitute".to_string(),
            estimated_compile_us: DEFAULT_MIN_RESERVATION_US,
            estimated_code_size_bytes: 4096,
        }
    }

    /// Build a basis-local LRA region request from the #8874/#8876 contract.
    pub(crate) fn lra_basis_region(request: &LraBasisRegionRequest) -> Result<Self, DeoptReason> {
        let Some(runtime_payload) = request.runtime_payload().cloned() else {
            return Err(DeoptReason::UnsupportedContract);
        };
        let payload = SolverProgramCompilePayload::LraBasisRegion {
            basis_generation: request.profile_key.basis_epoch,
            payload: runtime_payload,
        };
        Ok(Self {
            provenance: request.solver_program_provenance(),
            payload,
            invalidation_key: request.solver_program_invalidation_key(),
            guard_requirements: request.solver_program_guard_requirements(),
            install_boundaries: request.solver_program_install_boundaries(),
            target: TargetFeatures::current(),
            semantic_version: request.profile_key.semantic_hash,
            stats_prefix: request.profile_key.stats_prefix().to_string(),
            estimated_compile_us: DEFAULT_MIN_RESERVATION_US,
            estimated_code_size_bytes: estimate_lra_basis_region_code_size_bytes(
                request.row_count,
                request.coefficient_count,
            ),
        })
    }

    /// Build a whole-loop SAT request from the solver-program artifact contract.
    #[must_use]
    pub(crate) fn sat_whole_loop(
        num_vars: u32,
        irredundant_clauses: u32,
        clause_shape_hash: u64,
        invalidation_key: InvalidationKey,
    ) -> Self {
        let payload = SolverProgramCompilePayload::SatWholeLoop {
            num_vars,
            irredundant_clauses,
            clause_shape_hash,
        };
        Self {
            provenance: payload.default_provenance(),
            payload,
            invalidation_key,
            guard_requirements: GuardRequirements::conservative(),
            install_boundaries: InstallBoundarySet::solver_start_only(),
            target: TargetFeatures::current(),
            semantic_version: invalidation_key.semantic_hash,
            stats_prefix: "solver_program.sat_whole_loop".to_string(),
            estimated_compile_us: DEFAULT_MIN_RESERVATION_US,
            estimated_code_size_bytes: 64 * 1024,
        }
    }

    #[must_use]
    pub(crate) fn kind(&self) -> SolverProgramKind {
        self.payload.kind()
    }

    #[must_use]
    pub(crate) fn with_estimated_compile_us(mut self, estimated_compile_us: u64) -> Self {
        self.estimated_compile_us = estimated_compile_us;
        self
    }

    #[must_use]
    pub(crate) fn with_estimated_code_size_bytes(mut self, code_size_bytes: u64) -> Self {
        self.estimated_code_size_bytes = code_size_bytes;
        self
    }

    #[must_use]
    pub(crate) fn with_install_boundaries(
        mut self,
        install_boundaries: InstallBoundarySet,
    ) -> Self {
        self.install_boundaries = install_boundaries;
        self
    }

    fn reservation_us(&self, budget: SolverProgramCompilerBudget) -> u64 {
        self.estimated_compile_us.max(budget.min_reservation_us)
    }

    fn validate_contract(&self) -> Result<(), DeoptReason> {
        if !self.provenance.matches_kind(self.kind())
            || !self.guard_requirements.is_installable_contract()
            || !self.target.has_stable_cpu_feature_metadata()
        {
            return Err(DeoptReason::UnsupportedContract);
        }
        if let SolverProgramCompilePayload::SatWholeLoop {
            irredundant_clauses,
            ..
        } = &self.payload
        {
            if *irredundant_clauses > SAT_WHOLE_LOOP_SELECTIVE_BAKING_CLAUSE_LIMIT {
                return Err(DeoptReason::CodeSizeBudgetExceeded);
            }
        }
        if let SolverProgramCompilePayload::LraBasisRegion { payload, .. } = &self.payload {
            if payload.rows.is_empty() {
                return Err(DeoptReason::UnsupportedContract);
            }
        }
        Ok(())
    }
}

fn estimate_lra_basis_region_code_size_bytes(row_count: u32, coefficient_count: u32) -> u64 {
    1024u64
        .saturating_add(u64::from(row_count).saturating_mul(128))
        .saturating_add(u64::from(coefficient_count).saturating_mul(32))
}

/// Decision returned by an enqueue attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolverProgramEnqueueDecision {
    /// Request was accepted by the service.
    Enqueued {
        /// Service-assigned request ID.
        request_id: SolverProgramCompileRequestId,
        /// Budget reserved before the request entered the background queue.
        reserved_budget_us: u64,
    },
    /// Request was rejected without entering the background queue.
    Rejected(SolverProgramEnqueueRejection),
}

impl SolverProgramEnqueueDecision {
    #[must_use]
    pub(crate) fn request_id(self) -> Option<SolverProgramCompileRequestId> {
        match self {
            Self::Enqueued { request_id, .. } => Some(request_id),
            Self::Rejected(_) => None,
        }
    }
}

/// Reasons an enqueue attempt can be rejected synchronously.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolverProgramEnqueueRejection {
    /// The service has been disabled by runtime policy.
    Disabled,
    /// The service was already shut down.
    ShutDown,
    /// The request does not satisfy the solver-program artifact contract.
    UnsupportedContract(DeoptReason),
    /// The request was stale before it could be queued.
    StaleInvalidationKey,
    /// The queue already contains the maximum allowed in-flight work.
    QueueFull { in_flight: u64, max_in_flight: u64 },
    /// The request would exceed the remaining compile budget.
    BudgetExhausted {
        requested_us: u64,
        remaining_us: u64,
    },
    /// An equivalent request is already queued or running.
    DuplicateInFlight,
    /// The background worker channel was disconnected.
    ChannelClosed,
}

/// Native code owned by a compiled solver-program artifact.
pub(crate) enum SolverProgramNativeCode {
    /// Synthetic native code used by deterministic service unit tests.
    #[cfg(test)]
    TestOnly,
}

impl fmt::Debug for SolverProgramNativeCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(test)]
            Self::TestOnly => f.write_str("TestOnly"),
            #[allow(unreachable_patterns)]
            _ => f.write_str("<unavailable native code>"),
        }
    }
}

/// Compiled artifact returned by the service before install validation.
#[derive(Debug)]
pub(crate) struct SolverProgramCompiledArtifact {
    /// Metadata satisfying the #8874 artifact contract.
    pub(crate) meta: SolverProgramArtifactMeta,
    /// Backend-owned native code. Dropping this value discards uninstalled code.
    pub(crate) code: SolverProgramNativeCode,
}

/// Stale-work point at which the service discarded an artifact request/result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolverProgramStaleDropStage {
    /// Request became stale before backend codegen started.
    BeforeCompile,
    /// Request became stale while backend codegen was running.
    AfterCompile,
    /// Result became stale while waiting for a safe install poll.
    ResultPoll,
}

/// Terminal outcome for one service-assigned request.
#[derive(Debug)]
pub(crate) enum SolverProgramCompilerOutcome {
    /// Backend produced native code and artifact metadata.
    Compiled(Box<SolverProgramCompiledArtifact>),
    /// The region is valid but not supported by the active compiler.
    Unsupported {
        /// Solver region that was considered.
        kind: SolverProgramKind,
        /// Reason the contract could not be satisfied.
        reason: DeoptReason,
    },
    /// Backend returned an ordinary compiler error or panicked under containment.
    Failed { message: String },
    /// Backend exceeded the per-artifact timeout; any produced code was dropped.
    TimedOut,
    /// Reserved budget was no longer available when work reached the backend.
    BudgetExhausted,
    /// Request/result was dropped because its invalidation key became stale.
    DroppedStale {
        /// Point in the service lifecycle where stale work was discarded.
        stage: SolverProgramStaleDropStage,
    },
}

impl SolverProgramCompilerOutcome {
    fn is_compiled(&self) -> bool {
        matches!(self, Self::Compiled(_))
    }
}

/// Result sent from the background compiler to boundary-install call sites.
#[derive(Debug)]
pub(crate) struct SolverProgramCompilerResult {
    /// Service-assigned request ID.
    pub(crate) request_id: SolverProgramCompileRequestId,
    /// Solver region represented by this result.
    pub(crate) kind: SolverProgramKind,
    /// Invalidation key captured by the original request.
    pub(crate) invalidation_key: InvalidationKey,
    /// Compile wall time charged to the budget.
    pub(crate) elapsed_us: u64,
    /// Budget reservation charged at enqueue time.
    pub(crate) reserved_budget_us: u64,
    /// Terminal compile outcome.
    pub(crate) outcome: SolverProgramCompilerOutcome,
}

impl SolverProgramCompilerResult {
    /// Convert service output back to the #8874 metadata-only contract.
    #[must_use]
    pub(crate) fn contract_result(&self) -> Option<SolverProgramCompileResult> {
        match &self.outcome {
            SolverProgramCompilerOutcome::Compiled(artifact) => Some(
                SolverProgramCompileResult::Compiled(Box::new(artifact.meta.clone())),
            ),
            SolverProgramCompilerOutcome::Unsupported { kind, reason } => {
                Some(SolverProgramCompileResult::Unsupported {
                    kind: *kind,
                    reason: *reason,
                })
            }
            SolverProgramCompilerOutcome::Failed { .. }
            | SolverProgramCompilerOutcome::TimedOut
            | SolverProgramCompilerOutcome::BudgetExhausted
            | SolverProgramCompilerOutcome::DroppedStale { .. } => None,
        }
    }

    fn dropped_stale(mut self, stage: SolverProgramStaleDropStage) -> Self {
        self.outcome = SolverProgramCompilerOutcome::DroppedStale { stage };
        self
    }
}

struct QueuedSolverProgramRequest {
    request_id: SolverProgramCompileRequestId,
    request: SolverProgramCompilerRequest,
    dedupe_key: SolverProgramCompileDedupeKey,
    reserved_budget_us: u64,
    cancellation_epoch: u64,
}

impl QueuedSolverProgramRequest {
    fn new(
        request_id: SolverProgramCompileRequestId,
        request: SolverProgramCompilerRequest,
        reserved_budget_us: u64,
        cancellation_epoch: u64,
    ) -> Self {
        let dedupe_key = SolverProgramCompileDedupeKey::from_request(&request);
        Self {
            request_id,
            request,
            dedupe_key,
            reserved_budget_us,
            cancellation_epoch,
        }
    }
}

enum SolverProgramCompilerMessage {
    Compile(Box<QueuedSolverProgramRequest>),
    Shutdown,
}

enum BackendCompileOutcome {
    Compiled(SolverProgramNativeCode),
    Unsupported(DeoptReason),
    Failed(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SolverProgramCompileDedupeKey {
    payload: SolverProgramCompilePayload,
    invalidation_key: InvalidationKey,
    guard_requirements: GuardRequirements,
    install_boundaries: InstallBoundarySet,
    target: TargetFeatures,
    semantic_version: u64,
}

impl SolverProgramCompileDedupeKey {
    fn from_request(request: &SolverProgramCompilerRequest) -> Self {
        Self {
            payload: request.payload.clone(),
            invalidation_key: request.invalidation_key,
            guard_requirements: request.guard_requirements,
            install_boundaries: request.install_boundaries,
            target: request.target.clone(),
            semantic_version: request.semantic_version,
        }
    }
}

trait SolverProgramCompilerBackend: Send + 'static {
    fn compile(&mut self, request: &SolverProgramCompilerRequest) -> BackendCompileOutcome;
}

#[derive(Clone)]
struct SolverProgramCompilerCancellation {
    epoch: Arc<AtomicU64>,
    canceled_requests: Arc<Mutex<Vec<SolverProgramCompileRequestId>>>,
}

impl SolverProgramCompilerCancellation {
    fn new() -> Self {
        Self {
            epoch: Arc::new(AtomicU64::new(0)),
            canceled_requests: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn current_epoch(&self) -> u64 {
        self.epoch.load(Ordering::Acquire)
    }

    fn cancel_all(&self) {
        self.epoch.fetch_add(1, Ordering::AcqRel);
        self.canceled_requests
            .lock()
            .expect("compiler cancellation set poisoned")
            .clear();
    }

    fn cancel_request(&self, request_id: SolverProgramCompileRequestId) {
        let mut canceled_requests = self
            .canceled_requests
            .lock()
            .expect("compiler cancellation set poisoned");
        if !canceled_requests.contains(&request_id) {
            canceled_requests.push(request_id);
        }
    }

    fn is_epoch_cancelled(&self, request_epoch: u64) -> bool {
        request_epoch != self.current_epoch()
    }

    fn take_request_cancelled(&self, request_id: SolverProgramCompileRequestId) -> bool {
        let mut canceled_requests = self
            .canceled_requests
            .lock()
            .expect("compiler cancellation set poisoned");
        if let Some(index) = canceled_requests
            .iter()
            .position(|candidate| *candidate == request_id)
        {
            canceled_requests.swap_remove(index);
            true
        } else {
            false
        }
    }
}

struct ExternalCodegenBackendCompilerBackend;

impl SolverProgramCompilerBackend for ExternalCodegenBackendCompilerBackend {
    fn compile(&mut self, request: &SolverProgramCompilerRequest) -> BackendCompileOutcome {
        match &request.payload {
            SolverProgramCompilePayload::LraSparseSubstitute {
                coefficients,
                entering_var,
            } => compile_lra_sparse_substitute(coefficients, *entering_var),
            SolverProgramCompilePayload::LraBasisRegion { payload, .. } => {
                compile_lra_basis_region(payload, request.invalidation_key)
            }
            SolverProgramCompilePayload::SatWholeLoop {
                num_vars,
                irredundant_clauses,
                clause_shape_hash,
            } => compile_sat_whole_loop(*num_vars, *irredundant_clauses, *clause_shape_hash),
        }
    }
}

/// Async external code generation solver-program compiler service.
pub(crate) struct SolverProgramCompilerService {
    tx: mpsc::Sender<SolverProgramCompilerMessage>,
    rx_result: mpsc::Receiver<SolverProgramCompilerResult>,
    budget_remaining_us: Arc<AtomicU64>,
    in_flight: Arc<AtomicU64>,
    in_flight_dedupe_keys: Arc<Mutex<Vec<SolverProgramCompileDedupeKey>>>,
    live_key: Arc<Mutex<Option<InvalidationKey>>>,
    cancellation: SolverProgramCompilerCancellation,
    config: SolverProgramCompilerConfig,
    next_request_id: u64,
    thread_handle: Option<thread::JoinHandle<()>>,
}

impl SolverProgramCompilerService {
    /// Start a service using the production external code generation compiler backend.
    #[must_use]
    pub(crate) fn new(config: SolverProgramCompilerConfig) -> Self {
        Self::with_backend(config, ExternalCodegenBackendCompilerBackend)
    }

    /// Record the current runtime invalidation key.
    ///
    /// Existing queued work with a different key will be dropped before compile
    /// if possible. Already completed results are checked again during polling.
    pub(crate) fn set_runtime_invalidation_key(&self, key: InvalidationKey) {
        *self.live_key.lock().expect("compiler live key poisoned") = Some(key);
    }

    /// Clear runtime-key filtering, allowing callers to queue bootstrap work.
    pub(crate) fn clear_runtime_invalidation_key(&self) {
        *self.live_key.lock().expect("compiler live key poisoned") = None;
    }

    /// Alias for lifecycle call sites that cancel stale work after mutation.
    pub(crate) fn cancel_stale(&self, runtime_key: InvalidationKey) {
        self.set_runtime_invalidation_key(runtime_key);
    }

    /// Cancel one request without changing the runtime invalidation key.
    pub(crate) fn cancel_request(&self, request_id: SolverProgramCompileRequestId) {
        self.cancellation.cancel_request(request_id);
    }

    /// Submit one request to the background compiler if policy and budget allow it.
    pub(crate) fn submit(
        &mut self,
        request: SolverProgramCompilerRequest,
    ) -> SolverProgramEnqueueDecision {
        if !self.config.enabled {
            return SolverProgramEnqueueDecision::Rejected(SolverProgramEnqueueRejection::Disabled);
        }
        if self.thread_handle.is_none() {
            return SolverProgramEnqueueDecision::Rejected(SolverProgramEnqueueRejection::ShutDown);
        }
        if let Err(reason) = request.validate_contract() {
            return SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::UnsupportedContract(reason),
            );
        }
        if request_is_stale(request.invalidation_key, &self.live_key) {
            return SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::StaleInvalidationKey,
            );
        }
        let dedupe_key = SolverProgramCompileDedupeKey::from_request(&request);
        {
            let mut in_flight_keys = self
                .in_flight_dedupe_keys
                .lock()
                .expect("compiler dedupe key set poisoned");
            if in_flight_keys.contains(&dedupe_key) {
                return SolverProgramEnqueueDecision::Rejected(
                    SolverProgramEnqueueRejection::DuplicateInFlight,
                );
            }
            in_flight_keys.push(dedupe_key.clone());
        }

        let in_flight = self.in_flight.load(Ordering::Relaxed);
        if in_flight >= self.config.budget.max_in_flight {
            remove_in_flight_dedupe_key(&self.in_flight_dedupe_keys, &dedupe_key);
            return SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::QueueFull {
                    in_flight,
                    max_in_flight: self.config.budget.max_in_flight,
                },
            );
        }

        let reserved_budget_us = request.reservation_us(self.config.budget);
        if let Err(remaining_us) = reserve_budget(&self.budget_remaining_us, reserved_budget_us) {
            remove_in_flight_dedupe_key(&self.in_flight_dedupe_keys, &dedupe_key);
            return SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::BudgetExhausted {
                    requested_us: reserved_budget_us,
                    remaining_us,
                },
            );
        }

        let request_id = SolverProgramCompileRequestId(self.next_request_id);
        self.next_request_id += 1;
        self.in_flight.fetch_add(1, Ordering::Relaxed);

        let message =
            SolverProgramCompilerMessage::Compile(Box::new(QueuedSolverProgramRequest::new(
                request_id,
                request,
                reserved_budget_us,
                self.cancellation.current_epoch(),
            )));

        if let Err(err) = self.tx.send(message) {
            self.in_flight.fetch_sub(1, Ordering::Relaxed);
            refund_budget(&self.budget_remaining_us, reserved_budget_us);
            if let SolverProgramCompilerMessage::Compile(queued) = err.0 {
                remove_in_flight_dedupe_key(&self.in_flight_dedupe_keys, &queued.dedupe_key);
            }
            return SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::ChannelClosed,
            );
        }

        SolverProgramEnqueueDecision::Enqueued {
            request_id,
            reserved_budget_us,
        }
    }

    /// Non-blocking drain of completed results.
    ///
    /// This is the boundary-facing API: results are checked one more time
    /// against the current runtime key before any caller can install them.
    #[must_use]
    pub(crate) fn poll_results(&self) -> Vec<SolverProgramCompilerResult> {
        let mut results = Vec::new();
        while let Ok(result) = self.rx_result.try_recv() {
            results.push(drop_result_if_stale_or_cancelled(
                result,
                &self.live_key,
                &self.cancellation,
                SolverProgramStaleDropStage::ResultPoll,
            ));
        }
        results
    }

    /// Remaining background compile budget in microseconds.
    #[must_use]
    pub(crate) fn budget_remaining_us(&self) -> u64 {
        self.budget_remaining_us.load(Ordering::Relaxed)
    }

    /// Number of requests that have not yet published a terminal result.
    #[must_use]
    pub(crate) fn in_flight(&self) -> u64 {
        self.in_flight.load(Ordering::Acquire)
    }

    /// Shut down the background compiler and wait for the worker to exit.
    pub(crate) fn shutdown(&mut self) {
        self.cancellation.cancel_all();
        let _ = self.tx.send(SolverProgramCompilerMessage::Shutdown);
        if let Some(handle) = self.thread_handle.take() {
            let _ = handle.join();
        }
    }

    /// Drop queued/completed work, restore the compile budget, and start a fresh worker.
    pub(crate) fn reset(&mut self) {
        let config = self.config;
        self.cancellation.cancel_all();
        let _ = self.tx.send(SolverProgramCompilerMessage::Shutdown);
        drop(self.thread_handle.take());
        *self = Self::new(config);
    }

    fn with_backend<B>(config: SolverProgramCompilerConfig, backend: B) -> Self
    where
        B: SolverProgramCompilerBackend,
    {
        let (tx, rx) = mpsc::channel::<SolverProgramCompilerMessage>();
        let (tx_result, rx_result) = mpsc::channel::<SolverProgramCompilerResult>();
        let budget_remaining_us = Arc::new(AtomicU64::new(config.budget.total_budget_us));
        let in_flight = Arc::new(AtomicU64::new(0));
        let in_flight_dedupe_keys = Arc::new(Mutex::new(Vec::new()));
        let live_key = Arc::new(Mutex::new(None));
        let cancellation = SolverProgramCompilerCancellation::new();

        let worker_budget = Arc::clone(&budget_remaining_us);
        let worker_in_flight = Arc::clone(&in_flight);
        let worker_in_flight_dedupe_keys = Arc::clone(&in_flight_dedupe_keys);
        let worker_live_key = Arc::clone(&live_key);
        let worker_cancellation = cancellation.clone();
        let worker_config = config;
        let handle = thread::Builder::new()
            .name("ay-solver-program-compiler".into())
            .spawn(move || {
                background_thread(
                    rx,
                    tx_result,
                    worker_budget,
                    worker_in_flight,
                    worker_in_flight_dedupe_keys,
                    worker_live_key,
                    worker_cancellation,
                    worker_config,
                    backend,
                );
            })
            .expect("failed to spawn solver-program compiler thread");

        Self {
            tx,
            rx_result,
            budget_remaining_us,
            in_flight,
            in_flight_dedupe_keys,
            live_key,
            cancellation,
            config,
            next_request_id: 0,
            thread_handle: Some(handle),
        }
    }

    #[cfg(test)]
    pub(crate) fn with_completed_results_for_test(
        config: SolverProgramCompilerConfig,
        results: Vec<SolverProgramCompilerResult>,
    ) -> Self {
        let (tx, _rx) = mpsc::channel::<SolverProgramCompilerMessage>();
        let (tx_result, rx_result) = mpsc::channel::<SolverProgramCompilerResult>();
        for result in results {
            tx_result
                .send(result)
                .expect("test result receiver should be alive");
        }
        drop(tx_result);

        Self {
            tx,
            rx_result,
            budget_remaining_us: Arc::new(AtomicU64::new(config.budget.total_budget_us)),
            in_flight: Arc::new(AtomicU64::new(0)),
            in_flight_dedupe_keys: Arc::new(Mutex::new(Vec::new())),
            live_key: Arc::new(Mutex::new(None)),
            cancellation: SolverProgramCompilerCancellation::new(),
            config,
            next_request_id: 0,
            thread_handle: None,
        }
    }
}

impl Default for SolverProgramCompilerService {
    fn default() -> Self {
        Self::new(SolverProgramCompilerConfig::default())
    }
}

impl Drop for SolverProgramCompilerService {
    fn drop(&mut self) {
        self.shutdown();
    }
}

fn background_thread<B>(
    rx: mpsc::Receiver<SolverProgramCompilerMessage>,
    tx_result: mpsc::Sender<SolverProgramCompilerResult>,
    budget_remaining_us: Arc<AtomicU64>,
    in_flight: Arc<AtomicU64>,
    in_flight_dedupe_keys: Arc<Mutex<Vec<SolverProgramCompileDedupeKey>>>,
    live_key: Arc<Mutex<Option<InvalidationKey>>>,
    cancellation: SolverProgramCompilerCancellation,
    config: SolverProgramCompilerConfig,
    mut backend: B,
) where
    B: SolverProgramCompilerBackend,
{
    while let Ok(message) = rx.recv() {
        match message {
            SolverProgramCompilerMessage::Shutdown => break,
            SolverProgramCompilerMessage::Compile(queued) => {
                let queued = *queued;
                let dedupe_key = queued.dedupe_key.clone();
                let result = process_queued_request(
                    queued,
                    &mut backend,
                    &budget_remaining_us,
                    &live_key,
                    &cancellation,
                    config,
                );
                let _ = tx_result.send(result);
                remove_in_flight_dedupe_key(&in_flight_dedupe_keys, &dedupe_key);
                // Publish the terminal result before advertising the request as
                // idle. Safe-boundary consumers use `in_flight() == 0` as a
                // completion fence before their final non-blocking result poll.
                in_flight.fetch_sub(1, Ordering::Release);
            }
        }
    }
}

fn process_queued_request<B>(
    queued: QueuedSolverProgramRequest,
    backend: &mut B,
    budget_remaining_us: &AtomicU64,
    live_key: &Mutex<Option<InvalidationKey>>,
    cancellation: &SolverProgramCompilerCancellation,
    config: SolverProgramCompilerConfig,
) -> SolverProgramCompilerResult
where
    B: SolverProgramCompilerBackend,
{
    let kind = queued.request.kind();
    let invalidation_key = queued.request.invalidation_key;

    if queued_request_is_cancelled(&queued, cancellation)
        || request_is_stale(invalidation_key, live_key)
    {
        refund_budget(budget_remaining_us, queued.reserved_budget_us);
        return base_result(
            queued,
            0,
            SolverProgramCompilerOutcome::DroppedStale {
                stage: SolverProgramStaleDropStage::BeforeCompile,
            },
        );
    }

    if queued.reserved_budget_us == 0 && budget_remaining_us.load(Ordering::Relaxed) == 0 {
        return base_result(queued, 0, SolverProgramCompilerOutcome::BudgetExhausted);
    }

    let start = Instant::now();
    let outcome = backend.compile(&queued.request);
    let elapsed_us = start.elapsed().as_micros() as u64;
    settle_budget(budget_remaining_us, queued.reserved_budget_us, elapsed_us);

    if elapsed_us > config.budget.per_artifact_timeout_us {
        return base_result(queued, elapsed_us, SolverProgramCompilerOutcome::TimedOut);
    }

    let outcome = match outcome {
        BackendCompileOutcome::Compiled(code) => {
            let meta = artifact_meta(&queued.request, queued.request_id, elapsed_us);
            SolverProgramCompilerOutcome::Compiled(Box::new(SolverProgramCompiledArtifact {
                meta,
                code,
            }))
        }
        BackendCompileOutcome::Unsupported(reason) => {
            SolverProgramCompilerOutcome::Unsupported { kind, reason }
        }
        BackendCompileOutcome::Failed(message) => SolverProgramCompilerOutcome::Failed { message },
    };

    let result = base_result(queued, elapsed_us, outcome);
    drop_result_if_stale_or_cancelled(
        result,
        live_key,
        cancellation,
        SolverProgramStaleDropStage::AfterCompile,
    )
}

fn base_result(
    queued: QueuedSolverProgramRequest,
    elapsed_us: u64,
    outcome: SolverProgramCompilerOutcome,
) -> SolverProgramCompilerResult {
    SolverProgramCompilerResult {
        request_id: queued.request_id,
        kind: queued.request.kind(),
        invalidation_key: queued.request.invalidation_key,
        elapsed_us,
        reserved_budget_us: queued.reserved_budget_us,
        outcome,
    }
}

fn artifact_meta(
    request: &SolverProgramCompilerRequest,
    request_id: SolverProgramCompileRequestId,
    elapsed_us: u64,
) -> SolverProgramArtifactMeta {
    SolverProgramArtifactMeta {
        schema_version: SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION,
        id: SolverProgramArtifactId(request_id.0),
        kind: request.kind(),
        backend: SolverProgramBackend::ExternalCodegenBackend,
        producer_version: EXTERNAL_CODEGEN_IR_SOLVER_PROGRAM_PRODUCER_VERSION,
        semantic_version: request.semantic_version,
        provenance: request.provenance.clone(),
        invalidation_key: request.invalidation_key,
        guard_requirements: request.guard_requirements,
        install_boundaries: request.install_boundaries,
        target: request.target.clone(),
        code_size_bytes: request.estimated_code_size_bytes,
        compile_latency_us: elapsed_us,
        stats_prefix: request.stats_prefix.clone(),
        request_id: Some(request_id.0),
    }
}

fn request_is_stale(
    invalidation_key: InvalidationKey,
    live_key: &Mutex<Option<InvalidationKey>>,
) -> bool {
    live_key
        .lock()
        .expect("compiler live key poisoned")
        .is_some_and(|current| !invalidation_key.is_valid_for(current))
}

fn queued_request_is_cancelled(
    queued: &QueuedSolverProgramRequest,
    cancellation: &SolverProgramCompilerCancellation,
) -> bool {
    cancellation.is_epoch_cancelled(queued.cancellation_epoch)
        || cancellation.take_request_cancelled(queued.request_id)
}

fn result_is_cancelled(
    result: &SolverProgramCompilerResult,
    cancellation: &SolverProgramCompilerCancellation,
) -> bool {
    cancellation.take_request_cancelled(result.request_id)
}

fn drop_result_if_stale_or_cancelled(
    result: SolverProgramCompilerResult,
    live_key: &Mutex<Option<InvalidationKey>>,
    cancellation: &SolverProgramCompilerCancellation,
    stage: SolverProgramStaleDropStage,
) -> SolverProgramCompilerResult {
    if result_is_cancelled(&result, cancellation)
        || (result.outcome.is_compiled() && request_is_stale(result.invalidation_key, live_key))
    {
        result.dropped_stale(stage)
    } else {
        result
    }
}

fn reserve_budget(budget_remaining_us: &AtomicU64, requested_us: u64) -> Result<(), u64> {
    loop {
        let remaining = budget_remaining_us.load(Ordering::Relaxed);
        if remaining < requested_us {
            return Err(remaining);
        }
        let next = remaining - requested_us;
        if budget_remaining_us
            .compare_exchange_weak(remaining, next, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            return Ok(());
        }
    }
}

fn refund_budget(budget_remaining_us: &AtomicU64, refund_us: u64) {
    budget_remaining_us.fetch_add(refund_us, Ordering::Relaxed);
}

fn settle_budget(budget_remaining_us: &AtomicU64, reserved_us: u64, elapsed_us: u64) {
    if elapsed_us < reserved_us {
        refund_budget(budget_remaining_us, reserved_us - elapsed_us);
    } else if elapsed_us > reserved_us {
        let overage = elapsed_us - reserved_us;
        budget_remaining_us
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
                Some(current.saturating_sub(overage))
            })
            .ok();
    }
}

fn remove_in_flight_dedupe_key(
    in_flight_dedupe_keys: &Mutex<Vec<SolverProgramCompileDedupeKey>>,
    dedupe_key: &SolverProgramCompileDedupeKey,
) {
    let mut in_flight_dedupe_keys = in_flight_dedupe_keys
        .lock()
        .expect("compiler dedupe key set poisoned");
    if let Some(index) = in_flight_dedupe_keys
        .iter()
        .position(|candidate| candidate == dedupe_key)
    {
        in_flight_dedupe_keys.swap_remove(index);
    }
}

fn compile_lra_sparse_substitute(
    _coefficients: &[(u32, i64)],
    _entering_var: u32,
) -> BackendCompileOutcome {
    BackendCompileOutcome::Unsupported(DeoptReason::BackendRejected)
}

fn compile_lra_basis_region(
    _payload: &LraBasisRegionRuntimePayload,
    _invalidation_key: InvalidationKey,
) -> BackendCompileOutcome {
    BackendCompileOutcome::Unsupported(DeoptReason::BackendRejected)
}

fn compile_sat_whole_loop(
    _num_vars: u32,
    _irredundant_clauses: u32,
    _clause_shape_hash: u64,
) -> BackendCompileOutcome {
    BackendCompileOutcome::Unsupported(DeoptReason::BackendRejected)
}

fn contain_compile_panic<F, T>(site: &'static str, f: F) -> Result<T, String>
where
    F: FnOnce() -> T + UnwindSafe,
{
    match std::panic::catch_unwind(f) {
        Ok(result) => Ok(result),
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "<non-string panic payload>".to_string()
            };
            Err(format!("{site}: {msg}"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lra_region::LraBasisRegionRuntimeRow;
    use std::sync::atomic::AtomicBool;
    use std::time::Duration;

    fn key(seed: u64) -> InvalidationKey {
        InvalidationKey {
            generations: crate::solver_program::SolverProgramGenerations {
                constraints: seed,
                theory_atoms: seed + 1,
                basis: seed + 2,
                trail: seed + 3,
                config: seed + 4,
            },
            shape_hash: seed + 10,
            semantic_hash: seed + 20,
        }
    }

    fn request(seed: u64) -> SolverProgramCompilerRequest {
        SolverProgramCompilerRequest::lra_sparse_substitute(vec![(1, 2), (3, 4)], 1, key(seed))
    }

    fn request_with_coefficients(
        seed: u64,
        coefficients: Vec<(u32, i64)>,
    ) -> SolverProgramCompilerRequest {
        SolverProgramCompilerRequest::lra_sparse_substitute(coefficients, 1, key(seed))
    }

    fn sat_whole_loop_request(seed: u64) -> SolverProgramCompilerRequest {
        SolverProgramCompilerRequest::sat_whole_loop(128, 256, 0x51a7_1009, key(seed))
    }

    fn basis_region_request() -> LraBasisRegionRequest {
        let epochs = crate::lra_region::LraRegionEpochs {
            constraints: 1,
            theory_atoms: 2,
            basis: 3,
            trail: 4,
            config: 5,
        };
        let neighborhood = crate::lra_region::LraRegionNeighborhood::substitute(0, 2, vec![1]);
        let payload = LraBasisRegionRuntimePayload::new(
            neighborhood,
            vec![
                LraBasisRegionRuntimeRow::new(0, 2, 5, vec![(0, -1), (3, 1)]),
                LraBasisRegionRuntimeRow::new(1, 1, 22, vec![(0, -3), (3, 7)]),
            ],
        );
        LraBasisRegionRequest::try_new_with_runtime_payload(
            epochs,
            payload,
            crate::lra_region::LraRegionGuardMetadata::conservative(),
        )
        .expect("basis-region payload should be valid")
    }

    fn config(total_budget_us: u64) -> SolverProgramCompilerConfig {
        SolverProgramCompilerConfig {
            budget: SolverProgramCompilerBudget {
                total_budget_us,
                per_artifact_timeout_us: 50_000,
                min_reservation_us: 1,
                max_in_flight: 64,
            },
            ..SolverProgramCompilerConfig::default()
        }
    }

    struct StaticBackend {
        outcome: Option<BackendCompileOutcome>,
        called: Arc<AtomicU64>,
    }

    impl StaticBackend {
        fn compiled() -> Self {
            Self {
                outcome: Some(BackendCompileOutcome::Compiled(
                    SolverProgramNativeCode::TestOnly,
                )),
                called: Arc::new(AtomicU64::new(0)),
            }
        }

        fn unsupported() -> Self {
            Self {
                outcome: Some(BackendCompileOutcome::Unsupported(
                    DeoptReason::UnsupportedContract,
                )),
                called: Arc::new(AtomicU64::new(0)),
            }
        }
    }

    impl SolverProgramCompilerBackend for StaticBackend {
        fn compile(&mut self, _request: &SolverProgramCompilerRequest) -> BackendCompileOutcome {
            self.called.fetch_add(1, Ordering::Relaxed);
            self.outcome.take().expect("static backend called once")
        }
    }

    struct BlockingBackend {
        started: mpsc::Sender<()>,
        release: mpsc::Receiver<()>,
    }

    impl SolverProgramCompilerBackend for BlockingBackend {
        fn compile(&mut self, _request: &SolverProgramCompilerRequest) -> BackendCompileOutcome {
            let _ = self.started.send(());
            self.release
                .recv_timeout(Duration::from_secs(5))
                .expect("test should release blocking backend");
            BackendCompileOutcome::Unsupported(DeoptReason::UnsupportedContract)
        }
    }

    struct CancelDuringCompileBackend {
        cancellation: SolverProgramCompilerCancellation,
        request_id: SolverProgramCompileRequestId,
    }

    impl SolverProgramCompilerBackend for CancelDuringCompileBackend {
        fn compile(&mut self, _request: &SolverProgramCompilerRequest) -> BackendCompileOutcome {
            self.cancellation.cancel_request(self.request_id);
            thread::sleep(Duration::from_millis(2));
            BackendCompileOutcome::Compiled(SolverProgramNativeCode::TestOnly)
        }
    }

    struct CountingBlockingBackend {
        started: mpsc::Sender<()>,
        first_done: mpsc::Sender<()>,
        second_started: mpsc::Sender<()>,
        release: mpsc::Receiver<()>,
        called: Arc<AtomicU64>,
    }

    impl SolverProgramCompilerBackend for CountingBlockingBackend {
        fn compile(&mut self, _request: &SolverProgramCompilerRequest) -> BackendCompileOutcome {
            let call = self.called.fetch_add(1, Ordering::Relaxed);
            if call == 0 {
                let _ = self.started.send(());
                self.release
                    .recv_timeout(Duration::from_secs(5))
                    .expect("test should release blocking backend");
                let _ = self.first_done.send(());
            } else {
                let _ = self.second_started.send(());
            }
            BackendCompileOutcome::Unsupported(DeoptReason::UnsupportedContract)
        }
    }

    #[test]
    fn request_builder_uses_external_codegen_sparse_substitute_contract() {
        let request = request(7);

        assert_eq!(request.kind(), SolverProgramKind::LraSparseSubstitute);
        assert_eq!(
            request.provenance,
            SolverProgramProvenance::LraSparseSubstitute {
                entering_var: 1,
                pivot_terms: 1,
            }
        );
        assert!(request.guard_requirements.is_installable_contract());
        assert!(request.install_boundaries.restart);
        assert_eq!(request.semantic_version, key(7).semantic_hash);
    }

    #[test]
    fn request_builder_uses_solver_start_for_sat_whole_loop_contract() {
        let request = sat_whole_loop_request(8);

        assert_eq!(request.kind(), SolverProgramKind::SatWholeLoop);
        assert_eq!(
            request.provenance,
            SolverProgramProvenance::SatWholeLoop {
                num_vars: 128,
                irredundant_clauses: 256,
                clause_shape_hash: 0x51a7_1009,
            }
        );
        assert!(request.guard_requirements.is_installable_contract());
        assert!(request.install_boundaries.solver_start);
        assert!(!request.install_boundaries.restart);
        assert_eq!(request.stats_prefix, "solver_program.sat_whole_loop");
        assert_eq!(request.semantic_version, key(8).semantic_hash);
    }

    #[test]
    fn request_builder_preserves_lra_basis_region_payload() {
        let region = basis_region_request();
        let request = SolverProgramCompilerRequest::lra_basis_region(&region)
            .expect("runtime payload should build compiler request");

        assert_eq!(request.kind(), SolverProgramKind::LraBasisRegion);
        assert_eq!(
            request.provenance,
            SolverProgramProvenance::LraBasisRegion {
                basis_generation: 3,
            }
        );
        assert!(request.guard_requirements.is_installable_contract());
        assert!(request.install_boundaries.restart);
        assert_eq!(request.stats_prefix, "solver_program.lra_basis_region");
        assert_eq!(request.semantic_version, region.profile_key.semantic_hash);
        let SolverProgramCompilePayload::LraBasisRegion { payload, .. } = request.payload else {
            panic!("expected basis-region payload");
        };
        assert_eq!(payload.rows.len(), 2);
        assert_eq!(payload.rows[0].constant, 5);
        assert_eq!(payload.rows[1].shape.coefficients, vec![(0, -3), (3, 7)]);
    }

    #[test]
    fn metadata_only_lra_basis_region_request_is_not_compiler_payload() {
        let metadata_only = LraBasisRegionRequest::try_new(
            crate::lra_region::LraRegionEpochs {
                constraints: 1,
                theory_atoms: 2,
                basis: 3,
                trail: 4,
                config: 5,
            },
            crate::lra_region::LraRegionNeighborhood::substitute(0, 2, vec![1]),
            vec![
                crate::lra_region::LraRegionRowShape::new(0, 2, vec![(0, -1), (3, 1)]),
                crate::lra_region::LraRegionRowShape::new(1, 1, vec![(0, -3), (3, 7)]),
            ],
            crate::lra_region::LraRegionGuardMetadata::conservative(),
        )
        .expect("metadata request should be valid");

        assert_eq!(
            SolverProgramCompilerRequest::lra_basis_region(&metadata_only),
            Err(DeoptReason::UnsupportedContract)
        );
    }

    #[test]
    fn enqueue_rejects_sat_whole_loop_without_selective_baking() {
        let backend = StaticBackend::unsupported();
        let called = Arc::clone(&backend.called);
        let mut service = SolverProgramCompilerService::with_backend(config(100), backend);
        service.set_runtime_invalidation_key(key(9));

        let decision = service.submit(SolverProgramCompilerRequest::sat_whole_loop(
            512,
            SAT_WHOLE_LOOP_SELECTIVE_BAKING_CLAUSE_LIMIT + 1,
            0x51a7_1009,
            key(9),
        ));

        assert_eq!(
            decision,
            SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::UnsupportedContract(
                    DeoptReason::CodeSizeBudgetExceeded
                )
            )
        );
        assert_eq!(service.in_flight(), 0);
        assert_eq!(service.budget_remaining_us(), 100);
        assert_eq!(called.load(Ordering::Relaxed), 0);
        service.shutdown();
    }

    #[test]
    fn enqueue_rejects_budget_reservation_that_exceeds_remaining() {
        let mut service =
            SolverProgramCompilerService::with_backend(config(10), StaticBackend::unsupported());
        service.set_runtime_invalidation_key(key(1));

        let decision = service.submit(request(1).with_estimated_compile_us(11));

        assert_eq!(
            decision,
            SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::BudgetExhausted {
                    requested_us: 11,
                    remaining_us: 10,
                }
            )
        );
        assert_eq!(service.budget_remaining_us(), 10);
        service.shutdown();
    }

    #[test]
    fn enqueue_rejects_stale_request_against_runtime_key() {
        let mut service =
            SolverProgramCompilerService::with_backend(config(100), StaticBackend::unsupported());
        service.set_runtime_invalidation_key(key(1));

        let decision = service.submit(request(2));

        assert_eq!(
            decision,
            SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::StaleInvalidationKey
            )
        );
        assert_eq!(service.in_flight(), 0);
        service.shutdown();
    }

    #[test]
    fn queue_limit_counts_enqueued_work_until_terminal_result() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let mut service = SolverProgramCompilerService::with_backend(
            SolverProgramCompilerConfig {
                budget: SolverProgramCompilerBudget {
                    max_in_flight: 1,
                    ..config(100).budget
                },
                ..config(100)
            },
            BlockingBackend {
                started: started_tx,
                release: release_rx,
            },
        );
        service.set_runtime_invalidation_key(key(1));

        let first = service.submit(request(1).with_estimated_compile_us(10));
        let second = service.submit(
            request_with_coefficients(1, vec![(1, 2), (5, 6)]).with_estimated_compile_us(10),
        );

        assert!(matches!(
            first,
            SolverProgramEnqueueDecision::Enqueued { .. }
        ));
        assert_eq!(
            second,
            SolverProgramEnqueueDecision::Rejected(SolverProgramEnqueueRejection::QueueFull {
                in_flight: 1,
                max_in_flight: 1,
            })
        );

        started_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("backend should start");
        release_tx.send(()).expect("release backend");

        for _ in 0..50 {
            if service.in_flight() == 0 {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(service.in_flight(), 0);
        assert_eq!(service.poll_results().len(), 1);
        service.shutdown();
    }

    #[test]
    fn duplicate_compile_request_is_rejected_until_first_finishes() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let mut service = SolverProgramCompilerService::with_backend(
            config(10_000),
            BlockingBackend {
                started: started_tx,
                release: release_rx,
            },
        );
        service.set_runtime_invalidation_key(key(1));

        let first = service.submit(request(1).with_estimated_compile_us(10));
        let duplicate = service.submit(request(1).with_estimated_compile_us(20));

        assert!(matches!(
            first,
            SolverProgramEnqueueDecision::Enqueued { .. }
        ));
        assert_eq!(
            duplicate,
            SolverProgramEnqueueDecision::Rejected(
                SolverProgramEnqueueRejection::DuplicateInFlight
            )
        );
        assert_eq!(service.budget_remaining_us(), 9_990);

        started_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("backend should start first compile");
        release_tx.send(()).expect("release first backend call");
        for _ in 0..50 {
            if service.in_flight() == 0 {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(service.in_flight(), 0);
        assert_eq!(service.poll_results().len(), 1);

        let after_first_finishes = service.submit(request(1).with_estimated_compile_us(10));
        assert!(matches!(
            after_first_finishes,
            SolverProgramEnqueueDecision::Enqueued { .. }
        ));
        started_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("backend should start second compile");
        release_tx.send(()).expect("release second backend call");
        service.shutdown();
    }

    #[test]
    fn stale_queued_work_is_dropped_before_compile_and_refunds_budget() {
        let mut backend = StaticBackend::compiled();
        let called = Arc::clone(&backend.called);
        let budget_remaining_us = AtomicU64::new(90);
        let live_key = Mutex::new(Some(key(2)));
        let queued = QueuedSolverProgramRequest::new(
            SolverProgramCompileRequestId(3),
            request(1).with_estimated_compile_us(10),
            10,
            0,
        );
        let cancellation = SolverProgramCompilerCancellation::new();

        let result = process_queued_request(
            queued,
            &mut backend,
            &budget_remaining_us,
            &live_key,
            &cancellation,
            config(100),
        );

        assert_eq!(called.load(Ordering::Relaxed), 0);
        assert_eq!(budget_remaining_us.load(Ordering::Relaxed), 100);
        assert!(matches!(
            result.outcome,
            SolverProgramCompilerOutcome::DroppedStale {
                stage: SolverProgramStaleDropStage::BeforeCompile,
            }
        ));
        assert!(result.contract_result().is_none());
    }

    #[test]
    fn cancelled_queued_work_is_dropped_before_compile_and_refunds_budget() {
        let mut backend = StaticBackend::compiled();
        let called = Arc::clone(&backend.called);
        let budget_remaining_us = AtomicU64::new(90);
        let live_key = Mutex::new(Some(key(1)));
        let request_id = SolverProgramCompileRequestId(5);
        let queued = QueuedSolverProgramRequest::new(
            request_id,
            request(1).with_estimated_compile_us(10),
            10,
            0,
        );
        let cancellation = SolverProgramCompilerCancellation::new();
        cancellation.cancel_request(request_id);

        let result = process_queued_request(
            queued,
            &mut backend,
            &budget_remaining_us,
            &live_key,
            &cancellation,
            config(100),
        );

        assert_eq!(called.load(Ordering::Relaxed), 0);
        assert_eq!(budget_remaining_us.load(Ordering::Relaxed), 100);
        assert!(matches!(
            result.outcome,
            SolverProgramCompilerOutcome::DroppedStale {
                stage: SolverProgramStaleDropStage::BeforeCompile,
            }
        ));
    }

    #[test]
    fn cancelled_running_work_is_charged_before_drop() {
        let request_id = SolverProgramCompileRequestId(6);
        let cancellation = SolverProgramCompilerCancellation::new();
        let mut backend = CancelDuringCompileBackend {
            cancellation: cancellation.clone(),
            request_id,
        };
        let budget_remaining_us = AtomicU64::new(9_000);
        let live_key = Mutex::new(Some(key(1)));
        let queued = QueuedSolverProgramRequest::new(
            request_id,
            request(1).with_estimated_compile_us(1_000),
            1_000,
            0,
        );

        let result = process_queued_request(
            queued,
            &mut backend,
            &budget_remaining_us,
            &live_key,
            &cancellation,
            config(10_000),
        );

        assert!(result.elapsed_us > 0);
        assert_eq!(
            budget_remaining_us.load(Ordering::Relaxed),
            10_000u64.saturating_sub(result.elapsed_us)
        );
        assert!(matches!(
            result.outcome,
            SolverProgramCompilerOutcome::DroppedStale {
                stage: SolverProgramStaleDropStage::AfterCompile,
            }
        ));
    }

    #[test]
    fn reset_drops_queued_work_without_waiting_for_running_compile() {
        let (started_tx, started_rx) = mpsc::channel();
        let (first_done_tx, first_done_rx) = mpsc::channel();
        let (second_started_tx, second_started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let called = Arc::new(AtomicU64::new(0));
        let mut service = SolverProgramCompilerService::with_backend(
            config(100),
            CountingBlockingBackend {
                started: started_tx,
                first_done: first_done_tx,
                second_started: second_started_tx,
                release: release_rx,
                called: Arc::clone(&called),
            },
        );
        service.set_runtime_invalidation_key(key(1));
        assert!(matches!(
            service.submit(
                request_with_coefficients(1, vec![(1, 2), (5, 6)]).with_estimated_compile_us(10)
            ),
            SolverProgramEnqueueDecision::Enqueued { .. }
        ));
        started_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("backend should start first compile");
        assert!(matches!(
            service.submit(request(1).with_estimated_compile_us(10)),
            SolverProgramEnqueueDecision::Enqueued { .. }
        ));

        let (reset_done_tx, reset_done_rx) = mpsc::channel();
        let reset_handle = thread::spawn(move || {
            service.reset();
            reset_done_tx
                .send(service.budget_remaining_us())
                .expect("send reset budget");
        });

        match reset_done_rx.recv_timeout(Duration::from_secs(1)) {
            Ok(remaining) => assert_eq!(remaining, 100),
            Err(err) => {
                let _ = release_tx.send(());
                let _ = reset_handle.join();
                panic!("reset blocked behind queued compile work: {err}");
            }
        }

        release_tx.send(()).expect("release first compile");
        first_done_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("first compile should finish after release");
        assert!(
            second_started_rx
                .recv_timeout(Duration::from_millis(200))
                .is_err(),
            "reset should cancel queued work before it reaches the backend"
        );
        assert_eq!(called.load(Ordering::Relaxed), 1);
        reset_handle.join().expect("reset thread should finish");
    }

    #[test]
    fn compiled_result_has_installable_external_codegen_backend_metadata() {
        let mut backend = StaticBackend::compiled();
        let budget_remaining_us = AtomicU64::new(99);
        let live_key = Mutex::new(Some(key(1)));
        let queued = QueuedSolverProgramRequest::new(
            SolverProgramCompileRequestId(42),
            request(1)
                .with_estimated_compile_us(1)
                .with_estimated_code_size_bytes(8192),
            1,
            0,
        );
        let cancellation = SolverProgramCompilerCancellation::new();

        let result = process_queued_request(
            queued,
            &mut backend,
            &budget_remaining_us,
            &live_key,
            &cancellation,
            config(100),
        );

        let SolverProgramCompilerOutcome::Compiled(artifact) = &result.outcome else {
            panic!("expected compiled artifact: {result:?}");
        };
        assert!(matches!(artifact.code, SolverProgramNativeCode::TestOnly));
        assert_eq!(artifact.meta.id, SolverProgramArtifactId(42));
        assert_eq!(artifact.meta.request_id, Some(42));
        assert_eq!(
            artifact.meta.backend,
            SolverProgramBackend::ExternalCodegenBackend
        );
        assert_eq!(artifact.meta.kind, SolverProgramKind::LraSparseSubstitute);
        assert_eq!(artifact.meta.invalidation_key, key(1));
        assert_eq!(artifact.meta.code_size_bytes, 8192);
        assert_eq!(artifact.meta.compile_latency_us, result.elapsed_us);

        let contract = result
            .contract_result()
            .expect("compiled result should expose contract metadata");
        assert!(matches!(contract, SolverProgramCompileResult::Compiled(_)));
    }

    #[test]
    fn lra_basis_region_compiled_result_preserves_runtime_evidence_metadata() {
        let mut backend = StaticBackend::compiled();
        let compiler_request =
            SolverProgramCompilerRequest::lra_basis_region(&basis_region_request())
                .expect("basis-region payload should build compiler request")
                .with_estimated_compile_us(1);
        let expected_key = compiler_request.invalidation_key;
        let budget_remaining_us = AtomicU64::new(99);
        let live_key = Mutex::new(Some(expected_key));
        let queued = QueuedSolverProgramRequest::new(
            SolverProgramCompileRequestId(44),
            compiler_request,
            1,
            0,
        );
        let cancellation = SolverProgramCompilerCancellation::new();

        let result = process_queued_request(
            queued,
            &mut backend,
            &budget_remaining_us,
            &live_key,
            &cancellation,
            config(100),
        );

        let SolverProgramCompilerOutcome::Compiled(artifact) = &result.outcome else {
            panic!("expected compiled basis-region artifact: {result:?}");
        };
        assert!(matches!(artifact.code, SolverProgramNativeCode::TestOnly));
        assert_eq!(artifact.meta.id, SolverProgramArtifactId(44));
        assert_eq!(artifact.meta.request_id, Some(44));
        assert_eq!(
            artifact.meta.backend,
            SolverProgramBackend::ExternalCodegenBackend
        );
        assert_eq!(artifact.meta.kind, SolverProgramKind::LraBasisRegion);
        assert_eq!(
            artifact.meta.provenance,
            SolverProgramProvenance::LraBasisRegion {
                basis_generation: 3,
            }
        );
        assert_eq!(artifact.meta.invalidation_key, expected_key);
        assert_eq!(
            artifact.meta.guard_requirements,
            GuardRequirements::conservative()
        );
        assert_eq!(
            artifact.meta.install_boundaries,
            InstallBoundarySet::restart_only()
        );
        assert_eq!(artifact.meta.semantic_version, expected_key.semantic_hash);
        assert_eq!(
            artifact.meta.stats_prefix,
            "solver_program.lra_basis_region"
        );
        assert_eq!(artifact.meta.code_size_bytes, 1_408);
        assert_eq!(artifact.meta.compile_latency_us, result.elapsed_us);

        let contract = result
            .contract_result()
            .expect("compiled basis-region result should expose contract metadata");
        let SolverProgramCompileResult::Compiled(meta) = contract else {
            panic!("expected compiled contract metadata");
        };
        assert_eq!(meta.kind, SolverProgramKind::LraBasisRegion);
        assert_eq!(meta.invalidation_key, expected_key);
    }

    #[test]
    fn sat_whole_loop_result_contract_is_unsupported_until_lowering_exists() {
        let mut backend = StaticBackend::unsupported();
        let budget_remaining_us = AtomicU64::new(99);
        let live_key = Mutex::new(Some(key(8)));
        let queued = QueuedSolverProgramRequest::new(
            SolverProgramCompileRequestId(43),
            sat_whole_loop_request(8).with_estimated_compile_us(1),
            1,
            0,
        );
        let cancellation = SolverProgramCompilerCancellation::new();

        let result = process_queued_request(
            queued,
            &mut backend,
            &budget_remaining_us,
            &live_key,
            &cancellation,
            config(100),
        );

        assert_eq!(result.kind, SolverProgramKind::SatWholeLoop);
        assert!(matches!(
            result.outcome,
            SolverProgramCompilerOutcome::Unsupported {
                kind: SolverProgramKind::SatWholeLoop,
                reason: DeoptReason::UnsupportedContract,
            }
        ));
        assert_eq!(
            result.contract_result(),
            Some(SolverProgramCompileResult::Unsupported {
                kind: SolverProgramKind::SatWholeLoop,
                reason: DeoptReason::UnsupportedContract,
            })
        );
    }

    #[test]
    fn poll_stage_drops_compiled_result_that_became_stale() {
        let live_key = Mutex::new(Some(key(2)));
        let meta_request = request(1);
        let result = SolverProgramCompilerResult {
            request_id: SolverProgramCompileRequestId(4),
            kind: SolverProgramKind::LraSparseSubstitute,
            invalidation_key: key(1),
            elapsed_us: 7,
            reserved_budget_us: 1,
            outcome: SolverProgramCompilerOutcome::Compiled(Box::new(
                SolverProgramCompiledArtifact {
                    meta: artifact_meta(&meta_request, SolverProgramCompileRequestId(4), 7),
                    code: SolverProgramNativeCode::TestOnly,
                },
            )),
        };

        let cancellation = SolverProgramCompilerCancellation::new();
        let result = drop_result_if_stale_or_cancelled(
            result,
            &live_key,
            &cancellation,
            SolverProgramStaleDropStage::ResultPoll,
        );

        assert!(matches!(
            result.outcome,
            SolverProgramCompilerOutcome::DroppedStale {
                stage: SolverProgramStaleDropStage::ResultPoll,
            }
        ));
    }

    #[test]
    fn disabled_service_rejects_without_reserving_budget() {
        let mut service = SolverProgramCompilerService::with_backend(
            SolverProgramCompilerConfig {
                enabled: false,
                ..config(100)
            },
            StaticBackend::unsupported(),
        );

        let decision = service.submit(request(1));

        assert_eq!(
            decision,
            SolverProgramEnqueueDecision::Rejected(SolverProgramEnqueueRejection::Disabled)
        );
        assert_eq!(service.budget_remaining_us(), 100);
        service.shutdown();
    }

    #[test]
    fn panic_containment_turns_backend_panic_into_message() {
        let panicked = AtomicBool::new(false);
        let result = contain_compile_panic("site", || {
            panicked.store(true, Ordering::Relaxed);
            panic!("boom");
        });

        assert!(panicked.load(Ordering::Relaxed));
        assert_eq!(result, Err("site: boom".to_string()));
    }

    #[test]
    fn production_backend_reports_unsupported_without_external_codegen_feature() {
        let mut backend = ExternalCodegenBackendCompilerBackend;

        let outcome = backend.compile(&request(1));

        assert!(matches!(
            outcome,
            BackendCompileOutcome::Unsupported(DeoptReason::BackendRejected)
        ));
    }
}
