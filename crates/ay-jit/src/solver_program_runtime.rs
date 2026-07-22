// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Metadata-only runtime gate for compiled solver programs (#8877).
//!
//! This module deliberately does not own executable memory or call generated
//! functions. It defines the boundary-facing contract that future LRA, SAT, and
//! CHC integrations must pass before installing or applying external code generation
//! solver-program artifacts.
//!
//! ## STATUS (2026-07-14 triage)
//!
//! #8877 foundation whose "follow-up lanes" never landed; frozen since
//! the 2026-05-24 publish squash. Zero callers.
//! See the development design notes

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::solver_program::{
    DeoptReason, InstallBoundary, InstallDecision, InstallPolicy, InvalidationKey,
    SolverProgramArtifactId, SolverProgramArtifactMeta, SolverProgramGenerations,
    SolverProgramLifecycleAccounting, SolverProgramLifecyclePolicy, SolverProgramLifecycleSnapshot,
    TargetFeatures,
};

/// Current serialized runtime snapshot schema version.
pub(crate) const SOLVER_PROGRAM_RUNTIME_SNAPSHOT_SCHEMA_VERSION: u32 = 2;
/// Maximum deopt records retained in one invalidation report.
pub(crate) const SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT: usize = 32;

/// Runtime guard facts that must be true before native solver-program code runs.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramRuntimeGuards {
    /// Generic solver path is available for immediate fallback/deopt.
    pub(crate) interpreter_fallback_available: bool,
    /// Differential/oracle checking is available before default-on execution.
    pub(crate) oracle_check_available: bool,
    /// Current proof/witness mode can tolerate compiled-region fallback.
    pub(crate) proof_witness_safe: bool,
    /// Number of compiled frames currently executing in this solver.
    pub(crate) active_compiled_frames: u32,
}

impl SolverProgramRuntimeGuards {
    /// Guard facts used by tests and future explicit opt-in call sites.
    #[must_use]
    pub(crate) fn conservative_ready() -> Self {
        Self {
            interpreter_fallback_available: true,
            oracle_check_available: true,
            proof_witness_safe: true,
            active_compiled_frames: 0,
        }
    }

    fn validate_before_install(self, meta: &SolverProgramArtifactMeta) -> Result<(), DeoptReason> {
        if self.active_compiled_frames != 0 {
            return Err(DeoptReason::UnsafeInstallBoundary);
        }
        self.validate_before_apply(meta)
    }

    fn validate_before_apply(self, meta: &SolverProgramArtifactMeta) -> Result<(), DeoptReason> {
        if self.active_compiled_frames != 0 {
            return Err(DeoptReason::GuardFailed);
        }
        if meta.guard_requirements.require_interpreter_fallback
            && !self.interpreter_fallback_available
        {
            return Err(DeoptReason::GuardFailed);
        }
        if meta.guard_requirements.require_oracle_check && !self.oracle_check_available {
            return Err(DeoptReason::GuardFailed);
        }
        if !self.proof_witness_safe {
            return Err(DeoptReason::GuardFailed);
        }
        Ok(())
    }
}

/// Incremental or mutable-state event that may stale compiled artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramInvalidationEvent {
    /// An assertion scope was pushed.
    Push,
    /// One or more assertion scopes were popped.
    Pop,
    /// A temporary assumption set changed the solve context.
    Assumption,
    /// A lower-level generation or region hash changed directly.
    Generation,
}

/// Request to move the runtime key to a new incremental-solving state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramInvalidationRequest {
    /// Event that caused this invalidation.
    pub(crate) event: SolverProgramInvalidationEvent,
    /// Runtime key after the event has been applied by the generic solver.
    pub(crate) next_runtime_key: InvalidationKey,
}

impl SolverProgramInvalidationRequest {
    #[must_use]
    fn new(event: SolverProgramInvalidationEvent, next_runtime_key: InvalidationKey) -> Self {
        Self {
            event,
            next_runtime_key,
        }
    }

    /// Assertion-scope push after the generic solver has updated its key.
    #[must_use]
    pub(crate) fn push(next_runtime_key: InvalidationKey) -> Self {
        Self::new(SolverProgramInvalidationEvent::Push, next_runtime_key)
    }

    /// Assertion-scope pop after stale scoped state has been discarded.
    #[must_use]
    pub(crate) fn pop(next_runtime_key: InvalidationKey) -> Self {
        Self::new(SolverProgramInvalidationEvent::Pop, next_runtime_key)
    }

    /// Assumption solve after temporary assignment/trail state changed.
    #[must_use]
    pub(crate) fn assumption(next_runtime_key: InvalidationKey) -> Self {
        Self::new(SolverProgramInvalidationEvent::Assumption, next_runtime_key)
    }

    /// Direct generation or region-hash invalidation.
    #[must_use]
    pub(crate) fn generation(next_runtime_key: InvalidationKey) -> Self {
        Self::new(SolverProgramInvalidationEvent::Generation, next_runtime_key)
    }
}

/// Per-generation key delta produced by an invalidation event.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct SolverProgramGenerationDelta {
    /// Clause/constraint arena generation changed.
    pub(crate) constraints: bool,
    /// Theory atom table generation changed.
    pub(crate) theory_atoms: bool,
    /// Simplex/LRA basis generation changed.
    pub(crate) basis: bool,
    /// Trail or assignment generation changed.
    pub(crate) trail: bool,
    /// Runtime policy/configuration generation changed.
    pub(crate) config: bool,
}

impl SolverProgramGenerationDelta {
    #[must_use]
    fn between(before: SolverProgramGenerations, after: SolverProgramGenerations) -> Self {
        Self {
            constraints: before.constraints != after.constraints,
            theory_atoms: before.theory_atoms != after.theory_atoms,
            basis: before.basis != after.basis,
            trail: before.trail != after.trail,
            config: before.config != after.config,
        }
    }

    /// Whether any generation changed.
    #[must_use]
    pub(crate) fn any(self) -> bool {
        self.constraints || self.theory_atoms || self.basis || self.trail || self.config
    }
}

/// Runtime-key before/after evidence for one invalidation event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct SolverProgramInvalidationDelta {
    /// Runtime key before the event.
    pub(crate) before: InvalidationKey,
    /// Runtime key after the event.
    pub(crate) after: InvalidationKey,
    /// Generation fields that changed.
    pub(crate) generations: SolverProgramGenerationDelta,
    /// Region shape hash changed.
    pub(crate) shape_hash_changed: bool,
    /// Region semantic hash changed.
    pub(crate) semantic_hash_changed: bool,
}

impl SolverProgramInvalidationDelta {
    #[must_use]
    fn between(before: InvalidationKey, after: InvalidationKey) -> Self {
        Self {
            before,
            after,
            generations: SolverProgramGenerationDelta::between(
                before.generations,
                after.generations,
            ),
            shape_hash_changed: before.shape_hash != after.shape_hash,
            semantic_hash_changed: before.semantic_hash != after.semantic_hash,
        }
    }

    /// Whether the invalidation actually changed the runtime key.
    #[must_use]
    pub(crate) fn key_changed(self) -> bool {
        self.generations.any() || self.shape_hash_changed || self.semantic_hash_changed
    }
}

/// Aggregate counters for runtime-key invalidation events.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramInvalidationCounters {
    /// Total invalidation requests observed.
    pub(crate) requests: u64,
    /// Push invalidation requests.
    pub(crate) push_requests: u64,
    /// Pop invalidation requests.
    pub(crate) pop_requests: u64,
    /// Assumption invalidation requests.
    pub(crate) assumption_requests: u64,
    /// Direct generation invalidation requests.
    pub(crate) generation_requests: u64,
    /// Requests that changed the runtime key.
    pub(crate) key_changes: u64,
    /// Requests that left the runtime key unchanged.
    pub(crate) noops: u64,
    /// Installed artifacts removed because their key went stale.
    pub(crate) artifacts_deopted: u64,
    /// Deopt records retained in bounded reports.
    pub(crate) reported_deopts: u64,
    /// Deopt records omitted from bounded reports.
    pub(crate) truncated_deopts: u64,
}

impl SolverProgramInvalidationCounters {
    fn record(
        &mut self,
        event: SolverProgramInvalidationEvent,
        key_changed: bool,
        artifacts_deopted: u64,
        reported_deopts: u64,
        truncated_deopts: u64,
    ) {
        self.requests = self.requests.saturating_add(1);
        match event {
            SolverProgramInvalidationEvent::Push => {
                self.push_requests = self.push_requests.saturating_add(1);
            }
            SolverProgramInvalidationEvent::Pop => {
                self.pop_requests = self.pop_requests.saturating_add(1);
            }
            SolverProgramInvalidationEvent::Assumption => {
                self.assumption_requests = self.assumption_requests.saturating_add(1);
            }
            SolverProgramInvalidationEvent::Generation => {
                self.generation_requests = self.generation_requests.saturating_add(1);
            }
        }
        if key_changed {
            self.key_changes = self.key_changes.saturating_add(1);
        } else {
            self.noops = self.noops.saturating_add(1);
        }
        self.artifacts_deopted = self.artifacts_deopted.saturating_add(artifacts_deopted);
        self.reported_deopts = self.reported_deopts.saturating_add(reported_deopts);
        self.truncated_deopts = self.truncated_deopts.saturating_add(truncated_deopts);
    }
}

/// Bounded evidence emitted after one incremental invalidation event.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramInvalidationReport {
    /// Event that caused this invalidation.
    pub(crate) event: SolverProgramInvalidationEvent,
    /// Runtime-key before/after delta.
    pub(crate) key_delta: SolverProgramInvalidationDelta,
    /// Bounded deopt records for stale installed artifacts.
    pub(crate) deopted: Vec<SolverProgramDeoptMetadata>,
    /// Total number of artifacts deopted, including truncated records.
    pub(crate) deopted_artifacts: u64,
    /// Number of deopt records omitted from `deopted` due to the report bound.
    pub(crate) truncated_deopts: u64,
    /// Number of installed artifacts retained after invalidation.
    pub(crate) retained_artifacts: u64,
    /// Maximum deopt records this report was allowed to retain.
    pub(crate) report_limit: usize,
    /// Follow-up signal for compile queues and stats surfaces.
    pub(crate) recompile_trigger: SolverProgramRecompileTrigger,
}

/// Hint for follow-up lanes after a deopt outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramRecompileTrigger {
    /// The generic solver path should run; no new compile is useful now.
    None,
    /// Mutable solver state changed, so callers may enqueue a fresh artifact.
    RuntimeStateChanged,
}

impl SolverProgramRecompileTrigger {
    #[must_use]
    fn for_reason(reason: DeoptReason) -> Self {
        match reason {
            DeoptReason::StaleInvalidationKey => Self::RuntimeStateChanged,
            DeoptReason::DisabledByPolicy
            | DeoptReason::BackendRejected
            | DeoptReason::TargetMismatch
            | DeoptReason::GuardFailed
            | DeoptReason::UnsafeInstallBoundary
            | DeoptReason::CodeSizeBudgetExceeded
            | DeoptReason::CompileBudgetExceeded
            | DeoptReason::UnsupportedContract => Self::None,
        }
    }
}

/// Structured deopt evidence returned by runtime install/apply gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramDeoptMetadata {
    /// Artifact that deopted.
    pub(crate) artifact_id: SolverProgramArtifactId,
    /// Solver-program kind from artifact metadata.
    pub(crate) kind: crate::solver_program::SolverProgramKind,
    /// Backend that produced the artifact.
    pub(crate) backend: crate::solver_program::SolverProgramBackend,
    /// Async compiler request ID when available.
    pub(crate) request_id: Option<u64>,
    /// Install boundary tied to the deopt, if any.
    pub(crate) boundary: Option<InstallBoundary>,
    /// Reason native code could not be installed or applied.
    pub(crate) reason: DeoptReason,
    /// Whether follow-up lanes should rebuild against the current runtime key.
    pub(crate) recompile_trigger: SolverProgramRecompileTrigger,
    /// Key captured by the artifact at compile time.
    pub(crate) artifact_key: InvalidationKey,
    /// Runtime key observed when the deopt happened.
    pub(crate) runtime_key: InvalidationKey,
}

impl SolverProgramDeoptMetadata {
    fn from_meta(
        meta: &SolverProgramArtifactMeta,
        boundary: Option<InstallBoundary>,
        reason: DeoptReason,
        runtime_key: InvalidationKey,
    ) -> Self {
        Self {
            artifact_id: meta.id,
            kind: meta.kind,
            backend: meta.backend,
            request_id: meta.request_id,
            boundary,
            reason,
            recompile_trigger: SolverProgramRecompileTrigger::for_reason(reason),
            artifact_key: meta.invalidation_key,
            runtime_key,
        }
    }
}

/// Metadata retained after an artifact passes install validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramInstallRecord {
    /// Installed artifact metadata.
    pub(crate) meta: SolverProgramArtifactMeta,
    /// Boundary where the artifact was installed.
    pub(crate) boundary: InstallBoundary,
    /// Runtime key that was current at install time.
    pub(crate) installed_for_key: InvalidationKey,
    /// Monotonic sequence assigned by the local runtime.
    pub(crate) install_sequence: u64,
}

/// Outcome of a runtime install attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramRuntimeInstallOutcome {
    /// Artifact metadata was installed into the runtime registry.
    Installed(SolverProgramInstallRecord),
    /// Artifact was rejected and must use the generic solver path.
    Deopt(SolverProgramDeoptMetadata),
}

/// Outcome of a runtime apply attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SolverProgramRuntimeApplyOutcome {
    /// Installed artifact passed all apply guards.
    Applied(SolverProgramInstallRecord),
    /// Installed artifact deopted before native code could run.
    Deopt(SolverProgramDeoptMetadata),
    /// No artifact with this ID is installed.
    NotInstalled(SolverProgramArtifactId),
}

/// Versioned snapshot for future CLI/stats surfaces.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SolverProgramRuntimeSnapshot {
    /// Serialized snapshot schema version.
    pub(crate) schema_version: u32,
    /// Runtime invalidation key currently enforced.
    pub(crate) runtime_key: InvalidationKey,
    /// Runtime target feature set currently enforced.
    pub(crate) runtime_target: TargetFeatures,
    /// Install policy currently enforced.
    pub(crate) policy: InstallPolicy,
    /// Runtime guard facts currently enforced.
    pub(crate) guards: SolverProgramRuntimeGuards,
    /// Installed metadata records, sorted by artifact ID for stable snapshots.
    pub(crate) installed: Vec<SolverProgramInstallRecord>,
    /// Lifecycle accounting consumed by observability lanes.
    pub(crate) lifecycle: SolverProgramLifecycleSnapshot,
    /// Runtime-key invalidation accounting.
    pub(crate) invalidations: SolverProgramInvalidationCounters,
}

/// Metadata-only runtime gate for compiled solver-program artifacts.
#[derive(Debug, Clone)]
pub(crate) struct SolverProgramRuntime {
    runtime_key: InvalidationKey,
    runtime_target: TargetFeatures,
    policy: InstallPolicy,
    guards: SolverProgramRuntimeGuards,
    lifecycle: SolverProgramLifecycleAccounting,
    invalidations: SolverProgramInvalidationCounters,
    installed: BTreeMap<SolverProgramArtifactId, SolverProgramInstallRecord>,
    next_install_sequence: u64,
}

impl SolverProgramRuntime {
    /// Create a runtime gate for the current target.
    #[must_use]
    pub(crate) fn new(runtime_key: InvalidationKey, policy: InstallPolicy) -> Self {
        Self::with_target(runtime_key, TargetFeatures::current(), policy)
    }

    /// Create a runtime gate with explicit target metadata.
    #[must_use]
    pub(crate) fn with_target(
        runtime_key: InvalidationKey,
        runtime_target: TargetFeatures,
        policy: InstallPolicy,
    ) -> Self {
        Self {
            runtime_key,
            runtime_target,
            policy,
            guards: SolverProgramRuntimeGuards::default(),
            lifecycle: SolverProgramLifecycleAccounting::new(
                SolverProgramLifecyclePolicy::default(),
            ),
            invalidations: SolverProgramInvalidationCounters::default(),
            installed: BTreeMap::new(),
            next_install_sequence: 0,
        }
    }

    /// Replace runtime guard facts. Defaults are fail-closed.
    pub(crate) fn set_guards(&mut self, guards: SolverProgramRuntimeGuards) {
        self.guards = guards;
    }

    /// Update the runtime invalidation key after mutable solver state changes.
    pub(crate) fn set_runtime_key(&mut self, runtime_key: InvalidationKey) {
        self.runtime_key = runtime_key;
    }

    /// Apply a tracked incremental invalidation and drop stale installed records.
    ///
    /// This is metadata-only: callers have already updated the generic solver
    /// state and pass the resulting key. Any installed artifact whose captured
    /// key no longer matches is removed before native code can run again.
    pub(crate) fn invalidate_for_incremental_event(
        &mut self,
        request: SolverProgramInvalidationRequest,
    ) -> SolverProgramInvalidationReport {
        let before = self.runtime_key;
        self.runtime_key = request.next_runtime_key;
        let key_delta = SolverProgramInvalidationDelta::between(before, self.runtime_key);

        let mut stale_ids: Vec<_> = self
            .installed
            .iter()
            .filter_map(|(artifact_id, record)| {
                (!record.meta.invalidation_key.is_valid_for(self.runtime_key))
                    .then_some(*artifact_id)
            })
            .collect();
        stale_ids.sort_by_key(|artifact_id| artifact_id.0);

        let mut deopted = Vec::new();
        let mut deopted_artifacts = 0_u64;
        let mut truncated_deopts = 0_u64;
        for artifact_id in stale_ids {
            let Some(record) = self.installed.remove(&artifact_id) else {
                continue;
            };
            deopted_artifacts = deopted_artifacts.saturating_add(1);
            let deopt = SolverProgramDeoptMetadata::from_meta(
                &record.meta,
                Some(record.boundary),
                DeoptReason::StaleInvalidationKey,
                self.runtime_key,
            );
            if deopted.len() < SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT {
                deopted.push(deopt);
            } else {
                truncated_deopts = truncated_deopts.saturating_add(1);
            }
        }

        let reported_deopts = usize_to_u64(deopted.len());
        self.invalidations.record(
            request.event,
            key_delta.key_changed(),
            deopted_artifacts,
            reported_deopts,
            truncated_deopts,
        );

        SolverProgramInvalidationReport {
            event: request.event,
            key_delta,
            deopted,
            deopted_artifacts,
            truncated_deopts,
            retained_artifacts: usize_to_u64(self.installed.len()),
            report_limit: SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT,
            recompile_trigger: if key_delta.key_changed() {
                SolverProgramRecompileTrigger::RuntimeStateChanged
            } else {
                SolverProgramRecompileTrigger::None
            },
        }
    }

    /// Update the install/apply policy.
    pub(crate) fn set_policy(&mut self, policy: InstallPolicy) {
        self.policy = policy;
    }

    /// Validate artifact metadata and runtime guards without mutating state.
    #[must_use]
    pub(crate) fn validate_guards_before_install(
        &self,
        meta: &SolverProgramArtifactMeta,
        boundary: InstallBoundary,
    ) -> InstallDecision {
        let decision = meta.validate_install(
            self.runtime_key,
            &self.runtime_target,
            boundary,
            self.policy,
        );
        if !decision.is_install() {
            return decision;
        }
        match self.guards.validate_before_install(meta) {
            Ok(()) => InstallDecision::Install,
            Err(reason) => InstallDecision::Deopt(reason),
        }
    }

    /// Validate and record an install attempt.
    pub(crate) fn install_metadata(
        &mut self,
        meta: SolverProgramArtifactMeta,
        boundary: InstallBoundary,
    ) -> SolverProgramRuntimeInstallOutcome {
        let decision = self.validate_guards_before_install(&meta, boundary);
        self.lifecycle
            .record_install_decision(&meta, boundary, decision);

        match decision {
            InstallDecision::Install => {
                let record = SolverProgramInstallRecord {
                    meta,
                    boundary,
                    installed_for_key: self.runtime_key,
                    install_sequence: self.next_install_sequence,
                };
                self.next_install_sequence = self.next_install_sequence.saturating_add(1);
                self.installed.insert(record.meta.id, record.clone());
                SolverProgramRuntimeInstallOutcome::Installed(record)
            }
            InstallDecision::Deopt(reason) => {
                SolverProgramRuntimeInstallOutcome::Deopt(SolverProgramDeoptMetadata::from_meta(
                    &meta,
                    Some(boundary),
                    reason,
                    self.runtime_key,
                ))
            }
        }
    }

    /// Validate and record an apply attempt for an installed artifact.
    pub(crate) fn apply_installed(
        &mut self,
        artifact_id: SolverProgramArtifactId,
    ) -> SolverProgramRuntimeApplyOutcome {
        let Some(record) = self.installed.get(&artifact_id).cloned() else {
            return SolverProgramRuntimeApplyOutcome::NotInstalled(artifact_id);
        };

        let decision = self.validate_apply_record(&record);
        match decision {
            InstallDecision::Install => {
                self.lifecycle.record_apply_success(&record.meta);
                SolverProgramRuntimeApplyOutcome::Applied(record)
            }
            InstallDecision::Deopt(reason) => {
                if reason == DeoptReason::StaleInvalidationKey {
                    self.installed.remove(&artifact_id);
                }
                if reason == DeoptReason::GuardFailed {
                    self.lifecycle.record_guard_fail(&record.meta);
                } else {
                    self.lifecycle.record_apply_deopt(&record.meta, reason);
                }
                SolverProgramRuntimeApplyOutcome::Deopt(SolverProgramDeoptMetadata::from_meta(
                    &record.meta,
                    None,
                    reason,
                    self.runtime_key,
                ))
            }
        }
    }

    /// Return an installed record if present.
    #[must_use]
    pub(crate) fn installed_record(
        &self,
        artifact_id: SolverProgramArtifactId,
    ) -> Option<&SolverProgramInstallRecord> {
        self.installed.get(&artifact_id)
    }

    /// Number of installed metadata records currently retained.
    #[must_use]
    pub(crate) fn installed_count(&self) -> usize {
        self.installed.len()
    }

    /// Lifecycle accounting snapshot.
    #[must_use]
    pub(crate) fn lifecycle_snapshot(&self) -> SolverProgramLifecycleSnapshot {
        self.lifecycle.snapshot()
    }

    /// Full runtime snapshot for future stats surfaces.
    #[must_use]
    pub(crate) fn snapshot(&self) -> SolverProgramRuntimeSnapshot {
        let mut installed: Vec<_> = self.installed.values().cloned().collect();
        installed.sort_by_key(|record| record.meta.id.0);
        SolverProgramRuntimeSnapshot {
            schema_version: SOLVER_PROGRAM_RUNTIME_SNAPSHOT_SCHEMA_VERSION,
            runtime_key: self.runtime_key,
            runtime_target: self.runtime_target.clone(),
            policy: self.policy,
            guards: self.guards,
            installed,
            lifecycle: self.lifecycle.snapshot(),
            invalidations: self.invalidations,
        }
    }

    fn validate_apply_record(&self, record: &SolverProgramInstallRecord) -> InstallDecision {
        let decision = record.meta.validate_install(
            self.runtime_key,
            &self.runtime_target,
            record.boundary,
            self.policy,
        );
        if !decision.is_install() {
            return decision;
        }
        if record.meta.guard_requirements.require_generation_match
            && !record.meta.invalidation_key.is_valid_for(self.runtime_key)
        {
            return InstallDecision::Deopt(DeoptReason::StaleInvalidationKey);
        }
        match self.guards.validate_before_apply(&record.meta) {
            Ok(()) => InstallDecision::Install,
            Err(reason) => InstallDecision::Deopt(reason),
        }
    }
}

fn usize_to_u64(value: usize) -> u64 {
    value.try_into().unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_program::{
        GuardRequirements, InstallBoundarySet, SolverProgramArtifactMeta, SolverProgramBackend,
        SolverProgramGenerations, SolverProgramKind, SolverProgramProvenance,
        SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION,
    };
    use serde::{de::DeserializeOwned, Serialize};
    use std::fmt::Debug;

    fn assert_json_round_trip<T>(value: &T)
    where
        T: Serialize + DeserializeOwned + PartialEq + Debug,
    {
        let encoded = serde_json::to_string(value).expect("serialize value");
        let decoded: T = serde_json::from_str(&encoded).expect("deserialize value");
        assert_eq!(&decoded, value);
    }

    fn key(seed: u64) -> InvalidationKey {
        InvalidationKey {
            generations: SolverProgramGenerations {
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

    fn meta(seed: u64) -> SolverProgramArtifactMeta {
        SolverProgramArtifactMeta {
            schema_version: SOLVER_PROGRAM_ARTIFACT_SCHEMA_VERSION,
            id: SolverProgramArtifactId(seed),
            kind: SolverProgramKind::LraBasisRegion,
            backend: SolverProgramBackend::ExternalCodegenBackend,
            producer_version: 1,
            semantic_version: key(seed).semantic_hash,
            provenance: SolverProgramProvenance::LraBasisRegion {
                basis_generation: key(seed).generations.basis,
            },
            invalidation_key: key(seed),
            guard_requirements: GuardRequirements::conservative(),
            install_boundaries: InstallBoundarySet::restart_only(),
            target: TargetFeatures::current(),
            code_size_bytes: 4096,
            compile_latency_us: 1_000,
            stats_prefix: "solver_program.lra_basis_region".to_string(),
            request_id: Some(seed + 100),
        }
    }

    fn meta_for_key(id: u64, invalidation_key: InvalidationKey) -> SolverProgramArtifactMeta {
        SolverProgramArtifactMeta {
            id: SolverProgramArtifactId(id),
            semantic_version: invalidation_key.semantic_hash,
            provenance: SolverProgramProvenance::LraBasisRegion {
                basis_generation: invalidation_key.generations.basis,
            },
            invalidation_key,
            request_id: Some(id + 100),
            ..meta(id)
        }
    }

    fn policy() -> InstallPolicy {
        InstallPolicy::allow_external_codegen_for_testing()
    }

    fn ready_runtime(seed: u64) -> SolverProgramRuntime {
        let mut runtime = SolverProgramRuntime::new(key(seed), policy());
        runtime.set_guards(SolverProgramRuntimeGuards::conservative_ready());
        runtime
    }

    fn install(runtime: &mut SolverProgramRuntime, meta: SolverProgramArtifactMeta) {
        assert!(matches!(
            runtime.install_metadata(meta, InstallBoundary::Restart),
            SolverProgramRuntimeInstallOutcome::Installed(_)
        ));
    }

    #[test]
    fn runtime_install_is_fail_closed_until_guards_are_explicitly_ready() {
        let mut runtime = SolverProgramRuntime::new(key(1), policy());
        let outcome = runtime.install_metadata(meta(1), InstallBoundary::Restart);

        let SolverProgramRuntimeInstallOutcome::Deopt(deopt) = outcome else {
            panic!("default runtime guards should deopt");
        };
        assert_eq!(deopt.reason, DeoptReason::GuardFailed);
        assert_eq!(deopt.recompile_trigger, SolverProgramRecompileTrigger::None);
        assert_eq!(runtime.installed_count(), 0);

        let snapshot = runtime.lifecycle_snapshot();
        assert_eq!(snapshot.counters.install_attempts, 1);
        assert_eq!(snapshot.counters.installs, 0);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.guard_failed, 1);
    }

    #[test]
    fn runtime_installs_only_at_explicit_safe_boundary() {
        let mut runtime = ready_runtime(2);
        let outcome = runtime.install_metadata(meta(2), InstallBoundary::Restart);

        let SolverProgramRuntimeInstallOutcome::Installed(record) = outcome else {
            panic!("ready runtime should install matching artifact");
        };
        assert_eq!(record.meta.id, SolverProgramArtifactId(2));
        assert_eq!(record.boundary, InstallBoundary::Restart);
        assert_eq!(record.installed_for_key, key(2));
        assert_eq!(runtime.installed_count(), 1);
        assert!(runtime
            .installed_record(SolverProgramArtifactId(2))
            .is_some());

        let unsafe_outcome = runtime.install_metadata(meta(2), InstallBoundary::SolverStart);
        let SolverProgramRuntimeInstallOutcome::Deopt(deopt) = unsafe_outcome else {
            panic!("artifact should not install outside its boundary set");
        };
        assert_eq!(deopt.reason, DeoptReason::UnsafeInstallBoundary);

        let snapshot = runtime.snapshot();
        assert_eq!(
            snapshot.schema_version,
            SOLVER_PROGRAM_RUNTIME_SNAPSHOT_SCHEMA_VERSION
        );
        assert_eq!(snapshot.installed.len(), 1);
        assert_eq!(snapshot.lifecycle.counters.install_attempts, 2);
        assert_eq!(snapshot.lifecycle.counters.installs, 1);
        assert_json_round_trip(&snapshot);
    }

    #[test]
    fn active_compiled_frame_blocks_install_and_apply() {
        let mut runtime = ready_runtime(3);
        let mut blocked_guards = SolverProgramRuntimeGuards::conservative_ready();
        blocked_guards.active_compiled_frames = 1;
        runtime.set_guards(blocked_guards);

        let install_outcome = runtime.install_metadata(meta(3), InstallBoundary::Restart);
        let SolverProgramRuntimeInstallOutcome::Deopt(deopt) = install_outcome else {
            panic!("install while compiled frame is active should deopt");
        };
        assert_eq!(deopt.reason, DeoptReason::UnsafeInstallBoundary);

        runtime.set_guards(SolverProgramRuntimeGuards::conservative_ready());
        assert!(matches!(
            runtime.install_metadata(meta(3), InstallBoundary::Restart),
            SolverProgramRuntimeInstallOutcome::Installed(_)
        ));

        runtime.set_guards(blocked_guards);
        let apply_outcome = runtime.apply_installed(SolverProgramArtifactId(3));
        let SolverProgramRuntimeApplyOutcome::Deopt(deopt) = apply_outcome else {
            panic!("apply while compiled frame is active should deopt");
        };
        assert_eq!(deopt.reason, DeoptReason::GuardFailed);

        let snapshot = runtime.lifecycle_snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 0);
        assert_eq!(snapshot.counters.guard_fails, 1);
        assert_eq!(snapshot.counters.deopt_reasons.guard_failed, 1);
    }

    #[test]
    fn stale_installed_artifact_deopts_before_apply_and_requests_recompile() {
        let mut runtime = ready_runtime(4);
        assert!(matches!(
            runtime.install_metadata(meta(4), InstallBoundary::Restart),
            SolverProgramRuntimeInstallOutcome::Installed(_)
        ));

        runtime.set_runtime_key(key(5));
        let apply_outcome = runtime.apply_installed(SolverProgramArtifactId(4));

        let SolverProgramRuntimeApplyOutcome::Deopt(deopt) = apply_outcome else {
            panic!("stale installed artifact should deopt before apply");
        };
        assert_eq!(deopt.reason, DeoptReason::StaleInvalidationKey);
        assert_eq!(
            deopt.recompile_trigger,
            SolverProgramRecompileTrigger::RuntimeStateChanged
        );
        assert_eq!(deopt.artifact_key, key(4));
        assert_eq!(deopt.runtime_key, key(5));
        assert_eq!(runtime.installed_count(), 0);

        let snapshot = runtime.lifecycle_snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 0);
        assert_eq!(snapshot.counters.deopts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.stale_invalidation_key, 1);
        assert_json_round_trip(&deopt);
    }

    #[test]
    fn push_invalidation_updates_runtime_key_and_deopts_stale_records() {
        let installed_key = key(8);
        let mut runtime = ready_runtime(8);
        install(&mut runtime, meta_for_key(80, installed_key));
        install(&mut runtime, meta_for_key(81, installed_key));

        let next_key = InvalidationKey {
            generations: SolverProgramGenerations {
                constraints: installed_key.generations.constraints + 1,
                trail: installed_key.generations.trail + 1,
                ..installed_key.generations
            },
            shape_hash: installed_key.shape_hash + 1,
            ..installed_key
        };
        let report = runtime
            .invalidate_for_incremental_event(SolverProgramInvalidationRequest::push(next_key));

        assert_eq!(report.event, SolverProgramInvalidationEvent::Push);
        assert_eq!(report.key_delta.before, installed_key);
        assert_eq!(report.key_delta.after, next_key);
        assert!(report.key_delta.generations.constraints);
        assert!(report.key_delta.generations.trail);
        assert!(!report.key_delta.generations.basis);
        assert!(report.key_delta.shape_hash_changed);
        assert!(!report.key_delta.semantic_hash_changed);
        assert_eq!(report.deopted_artifacts, 2);
        assert_eq!(report.deopted.len(), 2);
        assert_eq!(report.truncated_deopts, 0);
        assert_eq!(report.retained_artifacts, 0);
        assert_eq!(
            report.recompile_trigger,
            SolverProgramRecompileTrigger::RuntimeStateChanged
        );
        assert_eq!(runtime.installed_count(), 0);
        assert!(report
            .deopted
            .iter()
            .all(|deopt| deopt.reason == DeoptReason::StaleInvalidationKey));
        assert_eq!(report.deopted[0].artifact_id, SolverProgramArtifactId(80));
        assert_eq!(report.deopted[0].artifact_key, installed_key);
        assert_eq!(report.deopted[0].runtime_key, next_key);

        let snapshot = runtime.snapshot();
        assert_eq!(snapshot.runtime_key, next_key);
        assert_eq!(snapshot.invalidations.requests, 1);
        assert_eq!(snapshot.invalidations.push_requests, 1);
        assert_eq!(snapshot.invalidations.key_changes, 1);
        assert_eq!(snapshot.invalidations.artifacts_deopted, 2);
        assert_eq!(snapshot.invalidations.reported_deopts, 2);
        assert_eq!(snapshot.invalidations.truncated_deopts, 0);
        assert_json_round_trip(&report);
        assert_json_round_trip(&snapshot);
    }

    #[test]
    fn pop_invalidation_without_key_change_retains_installed_artifacts() {
        let installed_key = key(9);
        let mut runtime = ready_runtime(9);
        install(&mut runtime, meta_for_key(90, installed_key));

        let report = runtime
            .invalidate_for_incremental_event(SolverProgramInvalidationRequest::pop(installed_key));

        assert_eq!(report.event, SolverProgramInvalidationEvent::Pop);
        assert!(!report.key_delta.key_changed());
        assert_eq!(report.deopted_artifacts, 0);
        assert!(report.deopted.is_empty());
        assert_eq!(report.retained_artifacts, 1);
        assert_eq!(
            report.recompile_trigger,
            SolverProgramRecompileTrigger::None
        );
        assert!(runtime
            .installed_record(SolverProgramArtifactId(90))
            .is_some());

        let snapshot = runtime.snapshot();
        assert_eq!(snapshot.invalidations.requests, 1);
        assert_eq!(snapshot.invalidations.pop_requests, 1);
        assert_eq!(snapshot.invalidations.key_changes, 0);
        assert_eq!(snapshot.invalidations.noops, 1);
        assert_eq!(snapshot.invalidations.artifacts_deopted, 0);
    }

    #[test]
    fn assumption_invalidation_is_fail_closed_on_trail_generation_change() {
        let installed_key = key(10);
        let mut runtime = ready_runtime(10);
        install(&mut runtime, meta_for_key(100, installed_key));

        let next_key = InvalidationKey {
            generations: SolverProgramGenerations {
                trail: installed_key.generations.trail + 1,
                ..installed_key.generations
            },
            ..installed_key
        };
        let report = runtime.invalidate_for_incremental_event(
            SolverProgramInvalidationRequest::assumption(next_key),
        );

        assert_eq!(report.event, SolverProgramInvalidationEvent::Assumption);
        assert!(report.key_delta.generations.trail);
        assert!(!report.key_delta.generations.constraints);
        assert!(!report.key_delta.shape_hash_changed);
        assert_eq!(report.deopted_artifacts, 1);
        assert_eq!(report.deopted[0].artifact_id, SolverProgramArtifactId(100));
        assert_eq!(
            report.recompile_trigger,
            SolverProgramRecompileTrigger::RuntimeStateChanged
        );
        assert_eq!(runtime.installed_count(), 0);

        let snapshot = runtime.snapshot();
        assert_eq!(snapshot.invalidations.assumption_requests, 1);
        assert_eq!(snapshot.invalidations.artifacts_deopted, 1);
    }

    #[test]
    fn generation_invalidation_report_is_bounded_but_removes_all_stale_artifacts() {
        let installed_key = key(11);
        let mut runtime = ready_runtime(11);
        let total_artifacts = SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT + 2;
        for offset in 0..total_artifacts {
            install(
                &mut runtime,
                meta_for_key(1100 + usize_to_u64(offset), installed_key),
            );
        }
        assert_eq!(runtime.installed_count(), total_artifacts);

        let next_key = InvalidationKey {
            generations: SolverProgramGenerations {
                config: installed_key.generations.config + 1,
                ..installed_key.generations
            },
            semantic_hash: installed_key.semantic_hash + 1,
            ..installed_key
        };
        let report = runtime.invalidate_for_incremental_event(
            SolverProgramInvalidationRequest::generation(next_key),
        );

        assert_eq!(report.event, SolverProgramInvalidationEvent::Generation);
        assert!(report.key_delta.generations.config);
        assert!(report.key_delta.semantic_hash_changed);
        assert_eq!(
            report.report_limit,
            SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT
        );
        assert_eq!(
            report.deopted.len(),
            SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT
        );
        assert_eq!(report.deopted_artifacts, usize_to_u64(total_artifacts));
        assert_eq!(report.truncated_deopts, 2);
        assert_eq!(runtime.installed_count(), 0);
        assert_eq!(report.deopted[0].artifact_id, SolverProgramArtifactId(1100));

        let snapshot = runtime.snapshot();
        assert_eq!(snapshot.invalidations.generation_requests, 1);
        assert_eq!(
            snapshot.invalidations.artifacts_deopted,
            usize_to_u64(total_artifacts)
        );
        assert_eq!(
            snapshot.invalidations.reported_deopts,
            usize_to_u64(SOLVER_PROGRAM_INVALIDATION_REPORT_LIMIT)
        );
        assert_eq!(snapshot.invalidations.truncated_deopts, 2);
    }

    #[test]
    fn successful_apply_records_lifecycle_without_deopt() {
        let mut runtime = ready_runtime(6);
        assert!(matches!(
            runtime.install_metadata(meta(6), InstallBoundary::Restart),
            SolverProgramRuntimeInstallOutcome::Installed(_)
        ));

        let apply_outcome = runtime.apply_installed(SolverProgramArtifactId(6));
        let SolverProgramRuntimeApplyOutcome::Applied(record) = apply_outcome else {
            panic!("ready installed artifact should apply");
        };
        assert_eq!(record.meta.id, SolverProgramArtifactId(6));

        let snapshot = runtime.lifecycle_snapshot();
        assert_eq!(snapshot.counters.install_attempts, 1);
        assert_eq!(snapshot.counters.installs, 1);
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.applies, 1);
        assert_eq!(snapshot.counters.deopts, 0);
    }

    #[test]
    fn runtime_deopts_apply_when_policy_is_disabled_after_install() {
        let mut runtime = ready_runtime(7);
        assert!(matches!(
            runtime.install_metadata(meta(7), InstallBoundary::Restart),
            SolverProgramRuntimeInstallOutcome::Installed(_)
        ));

        runtime.set_policy(InstallPolicy::default());
        let apply_outcome = runtime.apply_installed(SolverProgramArtifactId(7));

        let SolverProgramRuntimeApplyOutcome::Deopt(deopt) = apply_outcome else {
            panic!("disabled policy should deopt apply");
        };
        assert_eq!(deopt.reason, DeoptReason::DisabledByPolicy);
        assert_eq!(deopt.recompile_trigger, SolverProgramRecompileTrigger::None);
        assert_eq!(runtime.installed_count(), 1);

        let snapshot = runtime.lifecycle_snapshot();
        assert_eq!(snapshot.counters.apply_attempts, 1);
        assert_eq!(snapshot.counters.deopt_reasons.disabled_by_policy, 1);
    }
}
