// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stable solver capability descriptor for downstream routing.
//!
//! This module reports AY-owned public primitives from the narrow DPLL/model
//! consumer crate. It intentionally names cross-crate CHC/ALL-SAT surfaces by
//! stable public symbol and schema strings instead of depending on the broad
//! facade crate. Downstream consumers can depend on `ay-dpll` for capability
//! metadata plus model-blocking primitives without pulling unrelated engines.

use super::model_blocking::{
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
};
use super::verification::AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA;
use super::verification::AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA;
use sha2::{Digest, Sha256};

/// Schema identifier for the AY solver capability descriptor.
pub const AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA: &str = "ay.solver-capability-descriptor.v1";

/// Schema version for the AY solver capability descriptor.
pub const AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the compact solver capability descriptor manifest.
pub const AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA: &str =
    "ay.solver-capability-descriptor-manifest.v1";

/// Schema version for the compact solver capability descriptor manifest.
pub const AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the symbolic execution contract manifest.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA: &str =
    "ay.symbolic-execution-contract-manifest.v1";

/// Schema version for the symbolic execution contract manifest.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the symbolic execution contract manifest health report.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA: &str =
    "ay.symbolic-execution-contract-manifest-health.v1";

/// Schema version for the symbolic execution contract manifest health report.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the symbolic execution contract diagnostic summary.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA: &str =
    "ay.symbolic-execution-contract-diagnostic-summary.v1";

/// Schema version for the symbolic execution contract diagnostic summary.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the symbolic execution route admission decision.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA: &str =
    "ay.symbolic-execution-route-admission.v1";

/// Schema version for the symbolic execution route admission decision.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for per-capability symbolic execution route readiness.
pub const AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA: &str =
    "ay.symbolic-execution-capability-route-readiness.v1";

/// Schema version for per-capability symbolic execution route readiness.
pub const AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the downstream symbolic-execution contract bundle.
pub const AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA: &str =
    "ay.symbolic-execution-downstream-contract-bundle.v1";

/// Schema version for the downstream symbolic-execution contract bundle.
pub const AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA_VERSION: u32 = 1;

/// Solver selected by the symbolic-execution route readiness contract.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER: &str = "ay";

/// Narrow crate that owns symbolic-execution route readiness evidence.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE: &str = "ay-dpll";

/// Kind of path stored in `selected_solver_path`.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND: &str = "rust_api_symbol";

/// Stable contract revision required by symbolic route-readiness consumers.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION: &str =
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA;

/// Kind of current AY revision evidence emitted by route-readiness rows.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND: &str = "ay_build_commit";

/// Schema identifier for the model-blocking symbolic execution contract.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA: &str =
    "ay.model-blocking-symbolic-execution-contract.v1";

/// Schema version for the model-blocking symbolic execution contract.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the incremental-assumptions symbolic execution contract.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA: &str =
    "ay.incremental-assumptions-symbolic-execution-contract.v1";

/// Schema version for the incremental-assumptions symbolic execution contract.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Schema identifier for the ALL-SAT enumeration symbolic execution contract.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA: &str =
    "ay.all-sat-enumeration-symbolic-execution-contract.v1";

/// Schema version for the ALL-SAT enumeration symbolic execution contract.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Consumer responsibility: the source model must cross AY's accepted-model boundary.
pub const AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY: &str =
    "require_ay_accepted_model_boundary";

/// Consumer responsibility: the requested symbolic projection must be non-empty.
pub const AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_NON_EMPTY_PROJECTION: &str =
    "require_non_empty_projection_terms";

/// Consumer responsibility: all rejection/error paths are routed fail-closed.
pub const AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION: &str =
    "treat_rejected_or_error_as_fail_closed";

/// Consumer responsibility: forward AY-owned evidence without local reinterpretation.
pub const AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE: &str =
    "forward_ay_status_reason_without_reinterpretation";

/// Consumer responsibility: assumption inputs must be Boolean terms.
pub const AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_BOOLEAN_ASSUMPTIONS: &str =
    "require_boolean_assumption_terms";

/// Consumer responsibility: use the atomic assumption solve envelope for evidence.
pub const AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS: &str =
    "use_assumption_solve_details_atomic_envelope";

/// Consumer responsibility: read unsat assumptions only from UNSAT details.
pub const AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_UNSAT_CORE_ON_UNSAT: &str =
    "read_unsat_assumptions_only_when_unsat";

/// Consumer responsibility: check consumer acceptance before using SAT models.
pub const AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ACCEPT_MODEL_BOUNDARY: &str =
    "call_accept_for_consumer_before_sat_model_use";

/// Consumer responsibility: Unknown/error/panic outcomes remain fail-closed.
pub const AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION: &str =
    "treat_unknown_error_or_panic_as_fail_closed";

/// Consumer responsibility: an ALL-SAT consumer must set an explicit cap or accept AY's default.
pub const AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CAP_BOUND: &str =
    "set_explicit_max_solutions_or_accept_default_cap";

/// Consumer responsibility: downstream complete-enumeration use must check the ALL-SAT outcome.
pub const AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME: &str =
    "check_all_sat_outcome_before_complete_enumeration_use";

/// Consumer responsibility: projected enumeration must use AY's projection field.
pub const AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_PROJECTION_SCOPE: &str =
    "use_all_sat_projection_for_downstream_routing_scope";

/// Consumer responsibility: capped or error outcomes remain fail-closed.
pub const AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION: &str =
    "treat_capped_or_error_as_fail_closed";

/// Consumer responsibility: forward AY-owned ALL-SAT stats and outcome evidence.
pub const AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE: &str =
    "forward_ay_all_sat_stats_and_outcome";

/// Stable capability code for AY public solver primitives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolverCapabilityCode {
    /// Finite-domain model enumeration with a public enumerator.
    FiniteDomainEnumeration,
    /// Public typed model-blocking clause construction.
    ModelBlocking,
    /// ALL-SAT enumeration over Boolean clauses with internal blocking clauses.
    AllSatEnumeration,
    /// Assumption-based incremental solving.
    IncrementalAssumptions,
    /// CHC proof/model production and consumer evidence.
    ChcProofModelProduction,
    /// CHC proof-run model and replay-transcript artifact validation.
    ChcProofArtifactBundle,
    /// BTOR2/unsafe-trace assignment completeness evidence.
    Btor2TraceReplayCompleteness,
}

impl SolverCapabilityCode {
    /// Return the stable lower-snake-case capability code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::FiniteDomainEnumeration => "finite_domain_enumeration",
            Self::ModelBlocking => "model_blocking",
            Self::AllSatEnumeration => "all_sat_enumeration",
            Self::IncrementalAssumptions => "incremental_assumptions",
            Self::ChcProofModelProduction => "chc_proof_model_production",
            Self::ChcProofArtifactBundle => "chc_proof_artifact_bundle",
            Self::Btor2TraceReplayCompleteness => "btor2_trace_replay_completeness",
        }
    }

    /// Return a compact human-readable capability name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::FiniteDomainEnumeration => "Finite-domain enumeration",
            Self::ModelBlocking => "Model blocking",
            Self::AllSatEnumeration => "ALL-SAT enumeration",
            Self::IncrementalAssumptions => "Incremental assumptions",
            Self::ChcProofModelProduction => "CHC proof/model production",
            Self::ChcProofArtifactBundle => "CHC proof artifact bundle",
            Self::Btor2TraceReplayCompleteness => "BTOR2 trace replay completeness",
        }
    }
}

/// Public availability status for a capability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolverCapabilityStatus {
    /// AY exposes a stable public API for this capability.
    Available,
    /// AY does not currently expose a stable public API for this capability.
    Blocked,
}

impl SolverCapabilityStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Available => "available",
            Self::Blocked => "blocked",
        }
    }
}

/// Stable reason code for a capability descriptor row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolverCapabilityReason {
    /// AY owns and exposes the named public primitive.
    AYOwnedPublicApi,
    /// AY does not yet expose a typed public primitive for this boundary.
    PublicApiUnavailable,
}

impl SolverCapabilityReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::AYOwnedPublicApi => "ay_owned_public_api",
            Self::PublicApiUnavailable => "public_api_unavailable",
        }
    }
}

/// One machine-readable capability row for downstream routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolverCapability {
    /// Stable capability enum value.
    pub capability: SolverCapabilityCode,
    /// Stable lower-snake-case capability code.
    pub capability_code: &'static str,
    /// Compact human-readable capability name.
    pub capability_name: &'static str,
    /// Typed availability status.
    pub status: SolverCapabilityStatus,
    /// Stable lower-snake-case status code.
    pub status_code: &'static str,
    /// Typed availability reason.
    pub reason: SolverCapabilityReason,
    /// Stable lower-snake-case reason code.
    pub reason_code: &'static str,
    /// Public Rust API symbols that implement or report this capability.
    pub api_symbols: &'static [&'static str],
    /// Stable evidence schema identifiers emitted by this capability.
    pub evidence_schemas: &'static [&'static str],
    /// Whether rejected use of this capability should be treated as fail-closed.
    pub fail_closed: bool,
}

impl SolverCapability {
    const fn available(
        capability: SolverCapabilityCode,
        api_symbols: &'static [&'static str],
        evidence_schemas: &'static [&'static str],
    ) -> Self {
        Self {
            capability,
            capability_code: capability.code(),
            capability_name: capability.name(),
            status: SolverCapabilityStatus::Available,
            status_code: SolverCapabilityStatus::Available.code(),
            reason: SolverCapabilityReason::AYOwnedPublicApi,
            reason_code: SolverCapabilityReason::AYOwnedPublicApi.code(),
            api_symbols,
            evidence_schemas,
            fail_closed: true,
        }
    }

    /// Render this capability row as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "capability": self.capability_code,
            "name": self.capability_name,
            "status": self.status_code,
            "reason": self.reason_code,
            "api_symbols": self.api_symbols,
            "evidence_schemas": self.evidence_schemas,
            "fail_closed": self.fail_closed,
        })
    }
}

/// Stable contract row for capability-specific downstream routing evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolverCapabilityContract {
    /// Contract schema identifier.
    pub schema: &'static str,
    /// Contract schema version.
    pub schema_version: u32,
    /// Capability this contract describes.
    pub capability_code: &'static str,
    /// Public Rust API symbols that implement or report this contract.
    pub api_symbols: &'static [&'static str],
    /// Stable evidence schema identifiers emitted by this contract.
    pub evidence_schemas: &'static [&'static str],
    /// Status codes that represent accepted routing through this contract.
    pub accepted_status_codes: &'static [&'static str],
    /// Status codes that represent rejected/fail-closed routing.
    pub rejected_status_codes: &'static [&'static str],
    /// Reason codes that represent accepted routing through this contract.
    pub accepted_reason_codes: &'static [&'static str],
    /// Reason codes that represent rejected/fail-closed routing.
    pub rejected_reason_codes: &'static [&'static str],
    /// Stable downstream responsibility codes required to consume this contract.
    pub consumer_responsibilities: &'static [&'static str],
    /// Whether rejected use of this contract must be treated as fail-closed.
    pub fail_closed: bool,
}

impl SolverCapabilityContract {
    /// Render this contract as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "capability": self.capability_code,
            "api_symbols": self.api_symbols,
            "evidence_schemas": self.evidence_schemas,
            "accepted_status_codes": self.accepted_status_codes,
            "rejected_status_codes": self.rejected_status_codes,
            "accepted_reason_codes": self.accepted_reason_codes,
            "rejected_reason_codes": self.rejected_reason_codes,
            "consumer_responsibilities": self.consumer_responsibilities,
            "fail_closed": self.fail_closed,
        })
    }

    /// Render this contract as deterministic string key/value pairs.
    #[must_use]
    pub fn to_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        vec![
            ("schema", self.schema.to_string()),
            ("schema_version", self.schema_version.to_string()),
            ("capability", self.capability_code.to_string()),
            ("api_symbols", self.api_symbols.join(",")),
            ("evidence_schemas", self.evidence_schemas.join(",")),
            (
                "accepted_status_codes",
                self.accepted_status_codes.join(","),
            ),
            (
                "rejected_status_codes",
                self.rejected_status_codes.join(","),
            ),
            (
                "accepted_reason_codes",
                self.accepted_reason_codes.join(","),
            ),
            (
                "rejected_reason_codes",
                self.rejected_reason_codes.join(","),
            ),
            (
                "consumer_responsibilities",
                self.consumer_responsibilities.join(","),
            ),
            ("fail_closed", self.fail_closed.to_string()),
        ]
    }
}

/// One symbolic-execution routing contract row in the aggregate manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionContractManifestEntry {
    /// Stable lower-snake-case capability code.
    pub capability_code: &'static str,
    /// Compact human-readable capability name.
    pub capability_name: &'static str,
    /// Contract schema identifier.
    pub contract_schema: &'static str,
    /// Contract schema version.
    pub contract_schema_version: u32,
    /// Public helper that returns the typed contract.
    pub contract_helper: &'static str,
    /// Public helper that returns deterministic key/value rows.
    pub key_value_helper: &'static str,
    /// Status codes that represent accepted routing through this contract.
    pub accepted_status_codes: &'static [&'static str],
    /// Status codes that represent rejected/fail-closed routing.
    pub rejected_status_codes: &'static [&'static str],
    /// Reason codes that represent accepted routing through this contract.
    pub accepted_reason_codes: &'static [&'static str],
    /// Reason codes that represent rejected/fail-closed routing.
    pub rejected_reason_codes: &'static [&'static str],
    /// Whether rejected use of this contract must be treated as fail-closed.
    pub fail_closed: bool,
}

impl SymbolicExecutionContractManifestEntry {
    /// Render this manifest entry as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "capability": self.capability_code,
            "capability_name": self.capability_name,
            "contract_schema": self.contract_schema,
            "contract_schema_version": self.contract_schema_version,
            "contract_helper": self.contract_helper,
            "key_value_helper": self.key_value_helper,
            "accepted_status_codes": self.accepted_status_codes,
            "rejected_status_codes": self.rejected_status_codes,
            "accepted_reason_codes": self.accepted_reason_codes,
            "rejected_reason_codes": self.rejected_reason_codes,
            "fail_closed": self.fail_closed,
        })
    }
}

/// Aggregate symbolic-execution contract manifest for downstream routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionContractManifest {
    /// Manifest schema identifier.
    pub schema: &'static str,
    /// Manifest schema version.
    pub schema_version: u32,
    /// Stable solver identifier.
    pub solver: &'static str,
    /// Stable contract rows in deterministic order.
    pub contracts: &'static [SymbolicExecutionContractManifestEntry],
    /// Whether every included contract is fail-closed.
    pub all_contracts_fail_closed: bool,
}

impl SymbolicExecutionContractManifest {
    /// Render this manifest as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "solver": self.solver,
            "contract_count": self.contracts.len(),
            "contracts": self
                .contracts
                .iter()
                .map(SymbolicExecutionContractManifestEntry::to_json_value)
                .collect::<Vec<_>>(),
            "all_contracts_fail_closed": self.all_contracts_fail_closed,
        })
    }

    /// Render this manifest as deterministic string key/value pairs.
    #[must_use]
    pub fn to_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        let mut pairs = vec![
            ("schema", self.schema.to_string()),
            ("schema_version", self.schema_version.to_string()),
            ("solver", self.solver.to_string()),
            ("contract_count", self.contracts.len().to_string()),
            (
                "contract_capabilities",
                self.contracts
                    .iter()
                    .map(|entry| entry.capability_code)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "contract_capability_names",
                self.contracts
                    .iter()
                    .map(|entry| entry.capability_name)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "contract_schemas",
                self.contracts
                    .iter()
                    .map(|entry| entry.contract_schema)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "contract_schema_versions",
                self.contracts
                    .iter()
                    .map(|entry| entry.contract_schema_version.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "contract_helpers",
                self.contracts
                    .iter()
                    .map(|entry| entry.contract_helper)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "key_value_helpers",
                self.contracts
                    .iter()
                    .map(|entry| entry.key_value_helper)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "all_contracts_fail_closed",
                self.all_contracts_fail_closed.to_string(),
            ),
        ];

        for entry in self.contracts {
            pairs.extend([
                (
                    contract_manifest_key(entry.capability_code, "capability_name"),
                    entry.capability_name.to_string(),
                ),
                (
                    contract_manifest_key(entry.capability_code, "contract_schema"),
                    entry.contract_schema.to_string(),
                ),
                (
                    contract_manifest_key(entry.capability_code, "contract_schema_version"),
                    entry.contract_schema_version.to_string(),
                ),
                (
                    contract_manifest_key(entry.capability_code, "contract_helper"),
                    entry.contract_helper.to_string(),
                ),
                (
                    contract_manifest_key(entry.capability_code, "key_value_helper"),
                    entry.key_value_helper.to_string(),
                ),
                (
                    contract_manifest_key(entry.capability_code, "accepted_status_codes"),
                    entry.accepted_status_codes.join(","),
                ),
                (
                    contract_manifest_key(entry.capability_code, "rejected_status_codes"),
                    entry.rejected_status_codes.join(","),
                ),
                (
                    contract_manifest_key(entry.capability_code, "accepted_reason_codes"),
                    entry.accepted_reason_codes.join(","),
                ),
                (
                    contract_manifest_key(entry.capability_code, "rejected_reason_codes"),
                    entry.rejected_reason_codes.join(","),
                ),
                (
                    contract_manifest_key(entry.capability_code, "fail_closed"),
                    entry.fail_closed.to_string(),
                ),
            ]);
        }

        pairs
    }
}

/// Validation status for the symbolic-execution contract manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionContractManifestHealthStatus {
    /// All required contracts and key fields are complete.
    Complete,
    /// At least one required contract or field is missing or mismatched.
    Incomplete,
}

impl SymbolicExecutionContractManifestHealthStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::Incomplete => "incomplete",
        }
    }
}

/// Coarse health diagnostic class for downstream admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionContractManifestHealthDiagnostic {
    /// The manifest and rows are complete and usable by consumers.
    Healthy,
    /// Required contract data or rows are missing.
    Incomplete,
    /// Schema/version/helper/status/reason data is stale, duplicated, or mismatched.
    StaleOrMismatched,
    /// A manifest or contract is not fail-closed.
    FailClosedViolation,
}

impl SymbolicExecutionContractManifestHealthDiagnostic {
    /// Return the stable lower-snake-case diagnostic code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Healthy => "healthy",
            Self::Incomplete => "incomplete",
            Self::StaleOrMismatched => "stale_or_mismatched",
            Self::FailClosedViolation => "fail_closed_violation",
        }
    }
}

/// Validation reason for the symbolic-execution contract manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionContractManifestHealthReason {
    /// All required checks passed.
    Complete,
    /// The aggregate manifest schema did not match the AY-owned schema.
    ManifestSchemaMismatch,
    /// The aggregate manifest schema version did not match the AY-owned version.
    ManifestVersionMismatch,
    /// A required contract was absent.
    MissingRequiredContract,
    /// A required key/value pair was absent.
    MissingKeyValuePair,
    /// A contract capability appeared more than once.
    DuplicateContract,
    /// A key/value row appeared more than once.
    DuplicateKeyValuePair,
    /// A diagnostic summary text line was malformed.
    MalformedDiagnosticLine,
    /// A key/value pair was present but did not match the AY-owned value.
    KeyValueMismatch,
    /// A contract schema did not match the AY-owned schema.
    ContractSchemaMismatch,
    /// A contract schema version did not match the AY-owned version.
    ContractVersionMismatch,
    /// A typed contract helper name was absent or mismatched.
    ContractHelperMismatch,
    /// A key/value helper name was absent or mismatched.
    KeyValueHelperMismatch,
    /// A contract or aggregate manifest was not fail-closed.
    NotFailClosed,
    /// Accepted or rejected status code vocabulary did not match.
    StatusCodeMismatch,
    /// Accepted or rejected reason code vocabulary did not match.
    ReasonCodeMismatch,
}

impl SymbolicExecutionContractManifestHealthReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::ManifestSchemaMismatch => "manifest_schema_mismatch",
            Self::ManifestVersionMismatch => "manifest_version_mismatch",
            Self::MissingRequiredContract => "missing_required_contract",
            Self::MissingKeyValuePair => "missing_key_value_pair",
            Self::DuplicateContract => "duplicate_contract",
            Self::DuplicateKeyValuePair => "duplicate_key_value_pair",
            Self::MalformedDiagnosticLine => "malformed_diagnostic_line",
            Self::KeyValueMismatch => "key_value_mismatch",
            Self::ContractSchemaMismatch => "contract_schema_mismatch",
            Self::ContractVersionMismatch => "contract_version_mismatch",
            Self::ContractHelperMismatch => "contract_helper_mismatch",
            Self::KeyValueHelperMismatch => "key_value_helper_mismatch",
            Self::NotFailClosed => "not_fail_closed",
            Self::StatusCodeMismatch => "status_code_mismatch",
            Self::ReasonCodeMismatch => "reason_code_mismatch",
        }
    }
}

/// One validation issue in a symbolic-execution contract manifest health report.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionContractManifestHealthIssue {
    /// Contract capability code, when the issue belongs to a specific contract.
    pub capability_code: Option<&'static str>,
    /// Field or key that failed validation.
    pub field: &'static str,
    /// Typed issue reason.
    pub reason: SymbolicExecutionContractManifestHealthReason,
    /// Stable lower-snake-case issue reason code.
    pub reason_code: &'static str,
    /// Expected value, if the validation had one.
    pub expected: Option<String>,
    /// Actual value observed in the manifest or key/value pairs.
    pub actual: Option<String>,
}

impl SymbolicExecutionContractManifestHealthIssue {
    fn new(
        capability_code: Option<&'static str>,
        field: &'static str,
        reason: SymbolicExecutionContractManifestHealthReason,
        expected: Option<String>,
        actual: Option<String>,
    ) -> Self {
        Self {
            capability_code,
            field,
            reason,
            reason_code: reason.code(),
            expected,
            actual,
        }
    }

    /// Render this issue as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "capability": self.capability_code,
            "field": self.field,
            "reason": self.reason_code,
            "expected": self.expected,
            "actual": self.actual,
        })
    }
}

/// Health report for the symbolic-execution contract manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionContractManifestHealthReport {
    /// Health report schema identifier.
    pub schema: &'static str,
    /// Health report schema version.
    pub schema_version: u32,
    /// Typed validation status.
    pub status: SymbolicExecutionContractManifestHealthStatus,
    /// Stable lower-snake-case validation status code.
    pub status_code: &'static str,
    /// Primary validation reason.
    pub reason: SymbolicExecutionContractManifestHealthReason,
    /// Stable lower-snake-case primary reason code.
    pub reason_code: &'static str,
    /// Required contract capability codes.
    pub required_capabilities: &'static [&'static str],
    /// Required contract capability codes that were present.
    pub present_capabilities: Vec<&'static str>,
    /// Whether the manifest is complete enough for downstream consumption.
    pub accepted_for_consumer: bool,
    /// Whether every present and required contract was fail-closed.
    pub all_contracts_fail_closed: bool,
    /// Validation issues. Empty means the manifest is complete.
    pub issues: Vec<SymbolicExecutionContractManifestHealthIssue>,
}

impl SymbolicExecutionContractManifestHealthReport {
    /// Return the coarse admission diagnostic for downstream routing.
    #[must_use]
    pub fn diagnostic(&self) -> SymbolicExecutionContractManifestHealthDiagnostic {
        if self.status == SymbolicExecutionContractManifestHealthStatus::Complete {
            return SymbolicExecutionContractManifestHealthDiagnostic::Healthy;
        }
        if self.issues.iter().any(|issue| {
            issue.reason == SymbolicExecutionContractManifestHealthReason::NotFailClosed
        }) {
            return SymbolicExecutionContractManifestHealthDiagnostic::FailClosedViolation;
        }
        if self.issues.iter().any(|issue| {
            matches!(
                issue.reason,
                SymbolicExecutionContractManifestHealthReason::MissingRequiredContract
                    | SymbolicExecutionContractManifestHealthReason::MissingKeyValuePair
            )
        }) {
            return SymbolicExecutionContractManifestHealthDiagnostic::Incomplete;
        }
        SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
    }

    /// Return the stable lower-snake-case admission diagnostic code.
    #[must_use]
    pub fn diagnostic_code(&self) -> &'static str {
        self.diagnostic().code()
    }

    /// Render this health report as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "diagnostic": self.diagnostic_code(),
            "required_capabilities": self.required_capabilities,
            "present_capabilities": self.present_capabilities,
            "accepted_for_consumer": self.accepted_for_consumer,
            "all_contracts_fail_closed": self.all_contracts_fail_closed,
            "issue_count": self.issues.len(),
            "issues": self
                .issues
                .iter()
                .map(SymbolicExecutionContractManifestHealthIssue::to_json_value)
                .collect::<Vec<_>>(),
        })
    }

    /// Render this health report as deterministic string key/value pairs.
    #[must_use]
    pub fn to_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        vec![
            ("schema", self.schema.to_string()),
            ("schema_version", self.schema_version.to_string()),
            ("status", self.status_code.to_string()),
            ("reason", self.reason_code.to_string()),
            ("diagnostic", self.diagnostic_code().to_string()),
            (
                "required_capabilities",
                self.required_capabilities.join(","),
            ),
            ("present_capabilities", self.present_capabilities.join(",")),
            (
                "accepted_for_consumer",
                self.accepted_for_consumer.to_string(),
            ),
            (
                "all_contracts_fail_closed",
                self.all_contracts_fail_closed.to_string(),
            ),
            ("issue_count", self.issues.len().to_string()),
            (
                "issue_reason_codes",
                self.issues
                    .iter()
                    .map(|issue| issue.reason_code)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
        ]
    }

    /// Render this health report as deterministic key/value rows including issue details.
    #[must_use]
    pub fn to_diagnostic_key_value_rows(&self) -> Vec<(String, String)> {
        let mut rows = self
            .to_key_value_pairs()
            .into_iter()
            .map(|(key, value)| (key.to_string(), value))
            .collect::<Vec<_>>();

        for (index, issue) in self.issues.iter().enumerate() {
            let prefix = format!("issue_{index}");
            rows.extend([
                (
                    format!("{prefix}_capability"),
                    issue.capability_code.unwrap_or("none").to_string(),
                ),
                (format!("{prefix}_field"), issue.field.to_string()),
                (format!("{prefix}_reason"), issue.reason_code.to_string()),
                (
                    format!("{prefix}_expected"),
                    diagnostic_option_value(issue.expected.as_deref()),
                ),
                (
                    format!("{prefix}_actual"),
                    diagnostic_option_value(issue.actual.as_deref()),
                ),
            ]);
        }

        rows
    }

    /// Render this health report as stable line-oriented diagnostics.
    #[must_use]
    pub fn to_diagnostic_lines(&self) -> Vec<String> {
        self.to_diagnostic_key_value_rows()
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }
}

/// Compact downstream summary for the symbolic-execution manifest round trip.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionContractManifestDiagnosticSummary {
    /// Summary schema identifier.
    pub schema: &'static str,
    /// Summary schema version.
    pub schema_version: u32,
    /// Source manifest schema identifier.
    pub manifest_schema: &'static str,
    /// Source manifest schema version.
    pub manifest_schema_version: u32,
    /// Stable manifest identity string.
    pub manifest_identity: String,
    /// SHA-256 digest over deterministic source manifest rows.
    pub manifest_sha256: String,
    /// Source health schema identifier.
    pub health_schema: &'static str,
    /// Source health schema version.
    pub health_schema_version: u32,
    /// Stable lower-snake-case health status code.
    pub health_status: &'static str,
    /// Stable lower-snake-case coarse diagnostic code.
    pub health_diagnostic: &'static str,
    /// Stable lower-snake-case primary health reason code.
    pub health_reason: &'static str,
    /// Whether the summary is accepted for downstream consumption.
    pub accepted_for_consumer: bool,
    /// Whether the summary is fail-closed.
    pub fail_closed: bool,
    /// Number of contracts in the source manifest.
    pub contract_count: usize,
    /// Stable contract capability codes.
    pub contract_capabilities: Vec<&'static str>,
    /// Number of typed contract helpers.
    pub contract_helper_count: usize,
    /// Public typed contract helper names.
    pub contract_helpers: Vec<&'static str>,
    /// Number of key/value helper names.
    pub key_value_helper_count: usize,
    /// Public key/value helper names.
    pub key_value_helpers: Vec<&'static str>,
    /// Number of validator helper names.
    pub validator_count: usize,
    /// Public validator helper names.
    pub validators: &'static [&'static str],
    /// Number of diagnostic helper names.
    pub diagnostic_helper_count: usize,
    /// Public diagnostic helper names.
    pub diagnostic_helpers: &'static [&'static str],
    /// Number of health issues.
    pub issue_count: usize,
    /// Stable reason codes present in the health report.
    pub reason_codes: Vec<&'static str>,
}

impl SymbolicExecutionContractManifestDiagnosticSummary {
    /// Render this summary as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "manifest_schema": self.manifest_schema,
            "manifest_schema_version": self.manifest_schema_version,
            "manifest_identity": self.manifest_identity,
            "manifest_sha256": self.manifest_sha256,
            "health_schema": self.health_schema,
            "health_schema_version": self.health_schema_version,
            "health_status": self.health_status,
            "health_diagnostic": self.health_diagnostic,
            "health_reason": self.health_reason,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "contract_count": self.contract_count,
            "contract_capabilities": self.contract_capabilities,
            "contract_helper_count": self.contract_helper_count,
            "contract_helpers": self.contract_helpers,
            "key_value_helper_count": self.key_value_helper_count,
            "key_value_helpers": self.key_value_helpers,
            "validator_count": self.validator_count,
            "validators": self.validators,
            "diagnostic_helper_count": self.diagnostic_helper_count,
            "diagnostic_helpers": self.diagnostic_helpers,
            "issue_count": self.issue_count,
            "reason_codes": self.reason_codes,
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
                "manifest_schema".to_string(),
                self.manifest_schema.to_string(),
            ),
            (
                "manifest_schema_version".to_string(),
                self.manifest_schema_version.to_string(),
            ),
            (
                "manifest_identity".to_string(),
                self.manifest_identity.clone(),
            ),
            ("manifest_sha256".to_string(), self.manifest_sha256.clone()),
            ("health_schema".to_string(), self.health_schema.to_string()),
            (
                "health_schema_version".to_string(),
                self.health_schema_version.to_string(),
            ),
            ("health_status".to_string(), self.health_status.to_string()),
            (
                "health_diagnostic".to_string(),
                self.health_diagnostic.to_string(),
            ),
            ("health_reason".to_string(), self.health_reason.to_string()),
            (
                "accepted_for_consumer".to_string(),
                self.accepted_for_consumer.to_string(),
            ),
            ("fail_closed".to_string(), self.fail_closed.to_string()),
            (
                "contract_count".to_string(),
                self.contract_count.to_string(),
            ),
            (
                "contract_capabilities".to_string(),
                self.contract_capabilities.join(","),
            ),
            (
                "contract_helper_count".to_string(),
                self.contract_helper_count.to_string(),
            ),
            (
                "contract_helpers".to_string(),
                self.contract_helpers.join(","),
            ),
            (
                "key_value_helper_count".to_string(),
                self.key_value_helper_count.to_string(),
            ),
            (
                "key_value_helpers".to_string(),
                self.key_value_helpers.join(","),
            ),
            (
                "validator_count".to_string(),
                self.validator_count.to_string(),
            ),
            ("validators".to_string(), self.validators.join(",")),
            (
                "diagnostic_helper_count".to_string(),
                self.diagnostic_helper_count.to_string(),
            ),
            (
                "diagnostic_helpers".to_string(),
                self.diagnostic_helpers.join(","),
            ),
            ("issue_count".to_string(), self.issue_count.to_string()),
            ("reason_codes".to_string(), self.reason_codes.join(",")),
        ]
    }

    /// Render this summary as deterministic text lines.
    #[must_use]
    pub fn to_text_lines(&self) -> Vec<String> {
        self.to_key_value_rows()
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }
}

/// Admission status for the aggregate symbolic-execution route decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionRouteAdmissionStatus {
    /// All AY-owned symbolic-execution route rows are current and fail-closed.
    Accepted,
    /// One or more route rows are unknown, missing, stale, or fail-open.
    Blocked,
}

impl SymbolicExecutionRouteAdmissionStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Blocked => "blocked",
        }
    }
}

/// Admission reason for the aggregate symbolic-execution route decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionRouteAdmissionReason {
    /// AY owns every required symbolic-execution route row.
    AYAuthoritativeRoutes,
    /// The source manifest diagnostic summary was rejected.
    SummaryRejected,
    /// A forwarded row names a capability outside the AY-owned route set.
    UnknownCapability,
    /// A forwarded row key is outside the AY-owned route schema.
    UnknownRouteRow,
    /// A required route row is absent.
    MissingRouteRow,
    /// A route row appeared more than once.
    DuplicateRouteRow,
    /// A route row is malformed.
    MalformedRouteRow,
    /// A route row no longer matches AY-owned metadata.
    StaleRouteRow,
    /// A route row or source summary is not fail-closed.
    NotFailClosed,
}

impl SymbolicExecutionRouteAdmissionReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::AYAuthoritativeRoutes => "ay_authoritative_routes",
            Self::SummaryRejected => "summary_rejected",
            Self::UnknownCapability => "unknown_capability",
            Self::UnknownRouteRow => "unknown_route_row",
            Self::MissingRouteRow => "missing_route_row",
            Self::DuplicateRouteRow => "duplicate_route_row",
            Self::MalformedRouteRow => "malformed_route_row",
            Self::StaleRouteRow => "stale_route_row",
            Self::NotFailClosed => "not_fail_closed",
        }
    }
}

/// Compact downstream route/admission decision for symbolic execution.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionRouteAdmissionDecision {
    /// Route admission schema identifier.
    pub schema: &'static str,
    /// Route admission schema version.
    pub schema_version: u32,
    /// Typed admission status.
    pub status: SymbolicExecutionRouteAdmissionStatus,
    /// Stable lower-snake-case admission status code.
    pub status_code: &'static str,
    /// Typed admission reason.
    pub reason: SymbolicExecutionRouteAdmissionReason,
    /// Stable lower-snake-case admission reason code.
    pub reason_code: &'static str,
    /// Whether downstream consumers may use the route decision.
    pub accepted_for_consumer: bool,
    /// Whether any rejection must be treated as fail-closed.
    pub fail_closed: bool,
    /// Source contract manifest schema identifier.
    pub manifest_schema: &'static str,
    /// Source contract manifest schema version.
    pub manifest_schema_version: u32,
    /// Source diagnostic summary schema identifier.
    pub diagnostic_summary_schema: &'static str,
    /// Source diagnostic summary schema version.
    pub diagnostic_summary_schema_version: u32,
    /// Stable source manifest identity string.
    pub manifest_identity: String,
    /// Stable source manifest digest.
    pub manifest_sha256: String,
    /// Stable source diagnostic summary health status.
    pub health_status: &'static str,
    /// Stable source diagnostic summary health diagnostic.
    pub health_diagnostic: &'static str,
    /// Stable source diagnostic summary health reason.
    pub health_reason: &'static str,
    /// Number of authoritative route rows.
    pub route_count: usize,
    /// Stable capability codes covered by this decision.
    pub route_capabilities: Vec<&'static str>,
    /// Public typed contract helper names in route order.
    pub authoritative_contract_helpers: Vec<&'static str>,
    /// Public key/value helper names in route order.
    pub authoritative_key_value_helpers: Vec<&'static str>,
    /// Public route authority pairs as `capability:helper`.
    pub route_authorities: Vec<String>,
    /// Public validator helper names for this route decision.
    pub validators: &'static [&'static str],
    /// Field that caused rejection, or `none`.
    pub issue_field: String,
    /// Expected value for the rejection field, if any.
    pub issue_expected: Option<String>,
    /// Actual value observed for the rejection field, if any.
    pub issue_actual: Option<String>,
}

impl SymbolicExecutionRouteAdmissionDecision {
    /// Render this route decision as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "manifest_schema": self.manifest_schema,
            "manifest_schema_version": self.manifest_schema_version,
            "diagnostic_summary_schema": self.diagnostic_summary_schema,
            "diagnostic_summary_schema_version": self.diagnostic_summary_schema_version,
            "manifest_identity": self.manifest_identity,
            "manifest_sha256": self.manifest_sha256,
            "health_status": self.health_status,
            "health_diagnostic": self.health_diagnostic,
            "health_reason": self.health_reason,
            "route_count": self.route_count,
            "route_capabilities": self.route_capabilities,
            "authoritative_contract_helpers": self.authoritative_contract_helpers,
            "authoritative_key_value_helpers": self.authoritative_key_value_helpers,
            "route_authorities": self.route_authorities,
            "validators": self.validators,
            "issue_field": self.issue_field,
            "issue_expected": self.issue_expected,
            "issue_actual": self.issue_actual,
        })
    }

    /// Render this route decision as deterministic key/value rows.
    #[must_use]
    pub fn to_key_value_rows(&self) -> Vec<(String, String)> {
        let mut rows = vec![
            ("schema".to_string(), self.schema.to_string()),
            (
                "schema_version".to_string(),
                self.schema_version.to_string(),
            ),
            ("status".to_string(), self.status_code.to_string()),
            ("reason".to_string(), self.reason_code.to_string()),
            (
                "accepted_for_consumer".to_string(),
                self.accepted_for_consumer.to_string(),
            ),
            ("fail_closed".to_string(), self.fail_closed.to_string()),
            (
                "manifest_schema".to_string(),
                self.manifest_schema.to_string(),
            ),
            (
                "manifest_schema_version".to_string(),
                self.manifest_schema_version.to_string(),
            ),
            (
                "diagnostic_summary_schema".to_string(),
                self.diagnostic_summary_schema.to_string(),
            ),
            (
                "diagnostic_summary_schema_version".to_string(),
                self.diagnostic_summary_schema_version.to_string(),
            ),
            (
                "manifest_identity".to_string(),
                self.manifest_identity.clone(),
            ),
            ("manifest_sha256".to_string(), self.manifest_sha256.clone()),
            ("health_status".to_string(), self.health_status.to_string()),
            (
                "health_diagnostic".to_string(),
                self.health_diagnostic.to_string(),
            ),
            ("health_reason".to_string(), self.health_reason.to_string()),
            ("route_count".to_string(), self.route_count.to_string()),
            (
                "route_capabilities".to_string(),
                self.route_capabilities.join(","),
            ),
            (
                "authoritative_contract_helpers".to_string(),
                self.authoritative_contract_helpers.join(","),
            ),
            (
                "authoritative_key_value_helpers".to_string(),
                self.authoritative_key_value_helpers.join(","),
            ),
            (
                "route_authorities".to_string(),
                self.route_authorities.join(","),
            ),
            ("validators".to_string(), self.validators.join(",")),
            ("issue_field".to_string(), self.issue_field.clone()),
            (
                "issue_expected".to_string(),
                route_option_value(self.issue_expected.as_deref()),
            ),
            (
                "issue_actual".to_string(),
                route_option_value(self.issue_actual.as_deref()),
            ),
        ];

        for entry in AY_SYMBOLIC_EXECUTION_CONTRACTS {
            rows.extend([
                (
                    route_admission_key(entry.capability_code, "contract_schema"),
                    entry.contract_schema.to_string(),
                ),
                (
                    route_admission_key(entry.capability_code, "contract_schema_version"),
                    entry.contract_schema_version.to_string(),
                ),
                (
                    route_admission_key(entry.capability_code, "contract_helper"),
                    entry.contract_helper.to_string(),
                ),
                (
                    route_admission_key(entry.capability_code, "key_value_helper"),
                    entry.key_value_helper.to_string(),
                ),
                (
                    route_admission_key(entry.capability_code, "accepted_status_codes"),
                    entry.accepted_status_codes.join(","),
                ),
                (
                    route_admission_key(entry.capability_code, "rejected_status_codes"),
                    entry.rejected_status_codes.join(","),
                ),
                (
                    route_admission_key(entry.capability_code, "accepted_reason_codes"),
                    entry.accepted_reason_codes.join(","),
                ),
                (
                    route_admission_key(entry.capability_code, "rejected_reason_codes"),
                    entry.rejected_reason_codes.join(","),
                ),
                (
                    route_admission_key(entry.capability_code, "fail_closed"),
                    entry.fail_closed.to_string(),
                ),
            ]);
        }

        rows
    }

    /// Render this route decision as deterministic text lines.
    #[must_use]
    pub fn to_text_lines(&self) -> Vec<String> {
        self.to_key_value_rows()
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }
}

/// Readiness status for one AY-owned symbolic-execution capability route.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionCapabilityRouteReadinessStatus {
    /// This capability is ready to be routed through AY-owned primitives.
    Ready,
    /// This capability is not ready and must be treated fail-closed.
    Blocked,
}

impl SymbolicExecutionCapabilityRouteReadinessStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Ready => "ready",
            Self::Blocked => "blocked",
        }
    }
}

/// Readiness reason for one AY-owned symbolic-execution capability route.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionCapabilityRouteReadinessReason {
    /// The capability route is accepted by AY-owned route admission.
    AYAuthoritativeCapabilityRoute,
    /// The aggregate route admission decision was rejected.
    RouteAdmissionBlocked,
    /// The requested capability is not in the symbolic-execution contract manifest.
    UnknownCapability,
    /// A required manifest entry for the capability is absent.
    MissingManifestEntry,
    /// The capability contract schema does not match AY-owned metadata.
    ContractSchemaMismatch,
    /// The capability contract schema version does not match AY-owned metadata.
    ContractVersionMismatch,
    /// The typed contract helper does not match AY-owned metadata.
    ContractHelperMismatch,
    /// The key/value helper does not match AY-owned metadata.
    KeyValueHelperMismatch,
    /// Accepted or rejected status code vocabulary does not match.
    StatusCodeMismatch,
    /// Accepted or rejected reason code vocabulary does not match.
    ReasonCodeMismatch,
    /// The current AY revision evidence is unavailable.
    RevisionEvidenceUnavailable,
    /// The capability route or source route decision is not fail-closed.
    NotFailClosed,
    /// A forwarded readiness row names an unknown key.
    UnknownReadinessRow,
    /// A required readiness row is absent.
    MissingReadinessRow,
    /// A readiness row appeared more than once.
    DuplicateReadinessRow,
    /// A readiness row is malformed.
    MalformedReadinessRow,
    /// A readiness row no longer matches AY-owned metadata.
    StaleReadinessRow,
}

impl SymbolicExecutionCapabilityRouteReadinessReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::AYAuthoritativeCapabilityRoute => "ay_authoritative_capability_route",
            Self::RouteAdmissionBlocked => "route_admission_blocked",
            Self::UnknownCapability => "unknown_capability",
            Self::MissingManifestEntry => "missing_manifest_entry",
            Self::ContractSchemaMismatch => "contract_schema_mismatch",
            Self::ContractVersionMismatch => "contract_version_mismatch",
            Self::ContractHelperMismatch => "contract_helper_mismatch",
            Self::KeyValueHelperMismatch => "key_value_helper_mismatch",
            Self::StatusCodeMismatch => "status_code_mismatch",
            Self::ReasonCodeMismatch => "reason_code_mismatch",
            Self::RevisionEvidenceUnavailable => "revision_evidence_unavailable",
            Self::NotFailClosed => "not_fail_closed",
            Self::UnknownReadinessRow => "unknown_readiness_row",
            Self::MissingReadinessRow => "missing_readiness_row",
            Self::DuplicateReadinessRow => "duplicate_readiness_row",
            Self::MalformedReadinessRow => "malformed_readiness_row",
            Self::StaleReadinessRow => "stale_readiness_row",
        }
    }
}

/// AY-owned readiness decision for one symbolic-execution capability route.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionCapabilityRouteReadiness {
    /// Readiness schema identifier.
    pub schema: &'static str,
    /// Readiness schema version.
    pub schema_version: u32,
    /// Capability this readiness decision describes.
    pub capability: SolverCapabilityCode,
    /// Stable lower-snake-case capability code.
    pub capability_code: &'static str,
    /// Compact human-readable capability name.
    pub capability_name: &'static str,
    /// Typed readiness status.
    pub status: SymbolicExecutionCapabilityRouteReadinessStatus,
    /// Stable lower-snake-case readiness status code.
    pub status_code: &'static str,
    /// Typed readiness reason.
    pub reason: SymbolicExecutionCapabilityRouteReadinessReason,
    /// Stable lower-snake-case readiness reason code.
    pub reason_code: &'static str,
    /// Stable solver selected by this AY-owned route.
    pub selected_solver: &'static str,
    /// Narrow crate that owns the selected solver route.
    pub selected_solver_crate: &'static str,
    /// Kind of selected solver path evidence.
    pub selected_solver_path_kind: &'static str,
    /// Public API path selected for this capability route.
    pub selected_solver_path: &'static str,
    /// Whether this capability is supported for downstream routing.
    pub supported: bool,
    /// Stable unsupported reason code, or `none` when supported.
    pub unsupported_reason: &'static str,
    /// Whether downstream consumers may route this capability.
    pub accepted_for_consumer: bool,
    /// Whether any rejection must be treated as fail-closed.
    pub fail_closed: bool,
    /// Stable contract revision required by downstream consumers.
    pub required_contract_revision: &'static str,
    /// Kind of current AY revision evidence.
    pub current_ay_revision_kind: &'static str,
    /// Current AY build revision evidence.
    pub current_ay_revision: &'static str,
    /// Source route admission schema identifier.
    pub route_admission_schema: &'static str,
    /// Source route admission schema version.
    pub route_admission_schema_version: u32,
    /// Source route admission status code.
    pub route_admission_status: &'static str,
    /// Source route admission reason code.
    pub route_admission_reason: &'static str,
    /// Source manifest schema identifier.
    pub manifest_schema: &'static str,
    /// Source manifest schema version.
    pub manifest_schema_version: u32,
    /// Contract schema identifier for this capability.
    pub contract_schema: &'static str,
    /// Contract schema version for this capability.
    pub contract_schema_version: u32,
    /// Public helper that returns the typed contract.
    pub contract_helper: &'static str,
    /// Public helper that returns deterministic key/value rows.
    pub key_value_helper: &'static str,
    /// Public Rust API symbols that implement or report this capability.
    pub api_symbols: &'static [&'static str],
    /// Stable evidence schema identifiers emitted by this capability.
    pub evidence_schemas: &'static [&'static str],
    /// Status codes that represent accepted routing through this capability.
    pub accepted_status_codes: &'static [&'static str],
    /// Status codes that represent rejected/fail-closed routing.
    pub rejected_status_codes: &'static [&'static str],
    /// Reason codes that represent accepted routing through this capability.
    pub accepted_reason_codes: &'static [&'static str],
    /// Reason codes that represent rejected/fail-closed routing.
    pub rejected_reason_codes: &'static [&'static str],
    /// Stable downstream responsibility codes required to consume this capability.
    pub consumer_responsibilities: &'static [&'static str],
    /// Field that caused rejection, or `none`.
    pub issue_field: String,
    /// Expected value for the rejection field, if any.
    pub issue_expected: Option<String>,
    /// Actual value observed for the rejection field, if any.
    pub issue_actual: Option<String>,
}

impl SymbolicExecutionCapabilityRouteReadiness {
    /// Render this readiness decision as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "capability": self.capability_code,
            "capability_name": self.capability_name,
            "status": self.status_code,
            "reason": self.reason_code,
            "selected_solver": self.selected_solver,
            "selected_solver_crate": self.selected_solver_crate,
            "selected_solver_path_kind": self.selected_solver_path_kind,
            "selected_solver_path": self.selected_solver_path,
            "supported": self.supported,
            "unsupported_reason": self.unsupported_reason,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "required_contract_revision": self.required_contract_revision,
            "current_ay_revision_kind": self.current_ay_revision_kind,
            "current_ay_revision": self.current_ay_revision,
            "route_admission_schema": self.route_admission_schema,
            "route_admission_schema_version": self.route_admission_schema_version,
            "route_admission_status": self.route_admission_status,
            "route_admission_reason": self.route_admission_reason,
            "manifest_schema": self.manifest_schema,
            "manifest_schema_version": self.manifest_schema_version,
            "contract_schema": self.contract_schema,
            "contract_schema_version": self.contract_schema_version,
            "contract_helper": self.contract_helper,
            "key_value_helper": self.key_value_helper,
            "api_symbols": self.api_symbols,
            "evidence_schemas": self.evidence_schemas,
            "accepted_status_codes": self.accepted_status_codes,
            "rejected_status_codes": self.rejected_status_codes,
            "accepted_reason_codes": self.accepted_reason_codes,
            "rejected_reason_codes": self.rejected_reason_codes,
            "consumer_responsibilities": self.consumer_responsibilities,
            "issue_field": self.issue_field,
            "issue_expected": self.issue_expected,
            "issue_actual": self.issue_actual,
        })
    }

    /// Render this readiness decision as deterministic key/value rows.
    #[must_use]
    pub fn to_key_value_rows(&self) -> Vec<(String, String)> {
        vec![
            ("schema".to_string(), self.schema.to_string()),
            (
                "schema_version".to_string(),
                self.schema_version.to_string(),
            ),
            ("capability".to_string(), self.capability_code.to_string()),
            (
                "capability_name".to_string(),
                self.capability_name.to_string(),
            ),
            ("status".to_string(), self.status_code.to_string()),
            ("reason".to_string(), self.reason_code.to_string()),
            (
                "selected_solver".to_string(),
                self.selected_solver.to_string(),
            ),
            (
                "selected_solver_crate".to_string(),
                self.selected_solver_crate.to_string(),
            ),
            (
                "selected_solver_path_kind".to_string(),
                self.selected_solver_path_kind.to_string(),
            ),
            (
                "selected_solver_path".to_string(),
                self.selected_solver_path.to_string(),
            ),
            ("supported".to_string(), self.supported.to_string()),
            (
                "unsupported_reason".to_string(),
                self.unsupported_reason.to_string(),
            ),
            (
                "accepted_for_consumer".to_string(),
                self.accepted_for_consumer.to_string(),
            ),
            ("fail_closed".to_string(), self.fail_closed.to_string()),
            (
                "required_contract_revision".to_string(),
                self.required_contract_revision.to_string(),
            ),
            (
                "current_ay_revision_kind".to_string(),
                self.current_ay_revision_kind.to_string(),
            ),
            (
                "current_ay_revision".to_string(),
                self.current_ay_revision.to_string(),
            ),
            (
                "route_admission_schema".to_string(),
                self.route_admission_schema.to_string(),
            ),
            (
                "route_admission_schema_version".to_string(),
                self.route_admission_schema_version.to_string(),
            ),
            (
                "route_admission_status".to_string(),
                self.route_admission_status.to_string(),
            ),
            (
                "route_admission_reason".to_string(),
                self.route_admission_reason.to_string(),
            ),
            (
                "manifest_schema".to_string(),
                self.manifest_schema.to_string(),
            ),
            (
                "manifest_schema_version".to_string(),
                self.manifest_schema_version.to_string(),
            ),
            (
                "contract_schema".to_string(),
                self.contract_schema.to_string(),
            ),
            (
                "contract_schema_version".to_string(),
                self.contract_schema_version.to_string(),
            ),
            (
                "contract_helper".to_string(),
                self.contract_helper.to_string(),
            ),
            (
                "key_value_helper".to_string(),
                self.key_value_helper.to_string(),
            ),
            ("api_symbols".to_string(), self.api_symbols.join(",")),
            (
                "evidence_schemas".to_string(),
                self.evidence_schemas.join(","),
            ),
            (
                "accepted_status_codes".to_string(),
                self.accepted_status_codes.join(","),
            ),
            (
                "rejected_status_codes".to_string(),
                self.rejected_status_codes.join(","),
            ),
            (
                "accepted_reason_codes".to_string(),
                self.accepted_reason_codes.join(","),
            ),
            (
                "rejected_reason_codes".to_string(),
                self.rejected_reason_codes.join(","),
            ),
            (
                "consumer_responsibilities".to_string(),
                self.consumer_responsibilities.join(","),
            ),
            ("issue_field".to_string(), self.issue_field.clone()),
            (
                "issue_expected".to_string(),
                route_option_value(self.issue_expected.as_deref()),
            ),
            (
                "issue_actual".to_string(),
                route_option_value(self.issue_actual.as_deref()),
            ),
        ]
    }

    /// Render this readiness decision as deterministic text lines.
    #[must_use]
    pub fn to_text_lines(&self) -> Vec<String> {
        self.to_key_value_rows()
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }
}

/// Admission status for the downstream symbolic-execution contract bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionDownstreamContractBundleStatus {
    /// The bundle is complete, current, and fail-closed.
    Accepted,
    /// The bundle is incomplete, stale, malformed, or fail-open.
    Blocked,
}

impl SymbolicExecutionDownstreamContractBundleStatus {
    /// Return the stable lower-snake-case status code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Blocked => "blocked",
        }
    }
}

/// Admission reason for the downstream symbolic-execution contract bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolicExecutionDownstreamContractBundleReason {
    /// AY owns the descriptor, route admission, readiness, and validation rows.
    AYAuthoritativeDownstreamContractBundle,
    /// The solver capability descriptor manifest is not consumable.
    SolverCapabilityDescriptorRejected,
    /// The contract diagnostic summary is not consumable.
    ContractDiagnosticSummaryRejected,
    /// The aggregate route admission decision is not consumable.
    RouteAdmissionRejected,
    /// At least one per-capability readiness row is not consumable.
    CapabilityRouteReadinessRejected,
    /// A forwarded bundle row appeared more than once.
    DuplicateBundleRow,
    /// A forwarded bundle row key is outside the AY-owned schema.
    UnknownBundleRow,
    /// A required bundle row is absent.
    MissingBundleRow,
    /// A forwarded bundle text line was malformed.
    MalformedBundleRow,
    /// A forwarded bundle row no longer matches AY-owned metadata.
    StaleBundleRow,
    /// A forwarded bundle or nested evidence row is not fail-closed.
    NotFailClosed,
}

impl SymbolicExecutionDownstreamContractBundleReason {
    /// Return the stable lower-snake-case reason code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::AYAuthoritativeDownstreamContractBundle => {
                "ay_authoritative_downstream_contract_bundle"
            }
            Self::SolverCapabilityDescriptorRejected => "solver_capability_descriptor_rejected",
            Self::ContractDiagnosticSummaryRejected => "contract_diagnostic_summary_rejected",
            Self::RouteAdmissionRejected => "route_admission_rejected",
            Self::CapabilityRouteReadinessRejected => "capability_route_readiness_rejected",
            Self::DuplicateBundleRow => "duplicate_bundle_row",
            Self::UnknownBundleRow => "unknown_bundle_row",
            Self::MissingBundleRow => "missing_bundle_row",
            Self::MalformedBundleRow => "malformed_bundle_row",
            Self::StaleBundleRow => "stale_bundle_row",
            Self::NotFailClosed => "not_fail_closed",
        }
    }
}

/// One AY-owned bundle for downstream symbolic-execution routing consumers.
///
/// The bundle joins the narrow solver capability descriptor, symbolic route
/// admission, all-supported capability readiness, and validation row surfaces so
/// downstream consumers do not have to reconstruct the route matrix locally.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolicExecutionDownstreamContractBundle {
    /// Bundle schema identifier.
    pub schema: &'static str,
    /// Bundle schema version.
    pub schema_version: u32,
    /// Typed bundle admission status.
    pub status: SymbolicExecutionDownstreamContractBundleStatus,
    /// Stable lower-snake-case bundle status code.
    pub status_code: &'static str,
    /// Typed bundle admission reason.
    pub reason: SymbolicExecutionDownstreamContractBundleReason,
    /// Stable lower-snake-case bundle reason code.
    pub reason_code: &'static str,
    /// Whether downstream consumers may use this bundle.
    pub accepted_for_consumer: bool,
    /// Whether any rejection must be treated as fail-closed.
    pub fail_closed: bool,
    /// Stable solver identifier.
    pub solver: &'static str,
    /// Compact solver capability descriptor manifest.
    pub solver_capability_descriptor: SolverCapabilityDescriptorManifest,
    /// Contract diagnostic summary that feeds route admission.
    pub contract_diagnostic_summary: SymbolicExecutionContractManifestDiagnosticSummary,
    /// Aggregate route admission decision.
    pub route_admission_decision: SymbolicExecutionRouteAdmissionDecision,
    /// Readiness rows for every supported symbolic-execution capability.
    pub all_supported_capability_route_readiness: Vec<SymbolicExecutionCapabilityRouteReadiness>,
    /// Stable validation row groups included in this bundle.
    pub validation_row_groups: &'static [&'static str],
    /// Public helper names that produce this bundle surface.
    pub helper_names: &'static [&'static str],
    /// Public validator names for this bundle surface.
    pub validator_names: &'static [&'static str],
    /// Field that caused rejection, or `none`.
    pub issue_field: String,
    /// Expected value for the rejection field, if any.
    pub issue_expected: Option<String>,
    /// Actual value observed for the rejection field, if any.
    pub issue_actual: Option<String>,
}

impl SymbolicExecutionDownstreamContractBundle {
    /// Return the capability codes covered by all-supported readiness rows.
    #[must_use]
    pub fn readiness_capabilities(&self) -> Vec<&'static str> {
        self.all_supported_capability_route_readiness
            .iter()
            .map(|readiness| readiness.capability_code)
            .collect()
    }

    /// Return the readiness status codes in deterministic readiness order.
    #[must_use]
    pub fn readiness_status_codes(&self) -> Vec<&'static str> {
        self.all_supported_capability_route_readiness
            .iter()
            .map(|readiness| readiness.status_code)
            .collect()
    }

    /// Return the readiness reason codes in deterministic readiness order.
    #[must_use]
    pub fn readiness_reason_codes(&self) -> Vec<&'static str> {
        self.all_supported_capability_route_readiness
            .iter()
            .map(|readiness| readiness.reason_code)
            .collect()
    }

    /// Render the nested validation rows this bundle authoritatively carries.
    #[must_use]
    pub fn to_validation_key_value_rows(&self) -> Vec<(String, String)> {
        let mut rows = Vec::new();
        rows.extend(prefix_static_key_value_pairs(
            "descriptor",
            self.solver_capability_descriptor.to_key_value_pairs(),
        ));
        rows.extend(prefix_string_key_value_rows(
            "diagnostic_summary",
            self.contract_diagnostic_summary.to_key_value_rows(),
        ));
        rows.extend(prefix_string_key_value_rows(
            "route",
            self.route_admission_decision.to_key_value_rows(),
        ));
        rows.extend(prefix_string_key_value_rows(
            "readiness",
            prefixed_capability_route_readiness_rows(
                &self.all_supported_capability_route_readiness,
            ),
        ));
        rows
    }

    /// Render this bundle as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "status": self.status_code,
            "reason": self.reason_code,
            "accepted_for_consumer": self.accepted_for_consumer,
            "fail_closed": self.fail_closed,
            "solver": self.solver,
            "solver_capability_descriptor": self.solver_capability_descriptor.to_json_value(),
            "contract_diagnostic_summary": self.contract_diagnostic_summary.to_json_value(),
            "route_admission_decision": self.route_admission_decision.to_json_value(),
            "all_supported_capability_route_readiness": self
                .all_supported_capability_route_readiness
                .iter()
                .map(SymbolicExecutionCapabilityRouteReadiness::to_json_value)
                .collect::<Vec<_>>(),
            "validation_row_groups": self.validation_row_groups,
            "validation_row_count": self.to_validation_key_value_rows().len(),
            "helper_names": self.helper_names,
            "validator_names": self.validator_names,
            "issue_field": self.issue_field,
            "issue_expected": self.issue_expected,
            "issue_actual": self.issue_actual,
        })
    }

    /// Render this bundle as deterministic key/value rows.
    #[must_use]
    pub fn to_key_value_rows(&self) -> Vec<(String, String)> {
        let validation_rows = self.to_validation_key_value_rows();
        let mut rows = vec![
            ("schema".to_string(), self.schema.to_string()),
            (
                "schema_version".to_string(),
                self.schema_version.to_string(),
            ),
            ("status".to_string(), self.status_code.to_string()),
            ("reason".to_string(), self.reason_code.to_string()),
            (
                "accepted_for_consumer".to_string(),
                self.accepted_for_consumer.to_string(),
            ),
            ("fail_closed".to_string(), self.fail_closed.to_string()),
            ("solver".to_string(), self.solver.to_string()),
            (
                "solver_capability_descriptor_schema".to_string(),
                self.solver_capability_descriptor.schema.to_string(),
            ),
            (
                "solver_capability_descriptor_capability_count".to_string(),
                self.solver_capability_descriptor
                    .capability_count
                    .to_string(),
            ),
            (
                "contract_diagnostic_summary_schema".to_string(),
                self.contract_diagnostic_summary.schema.to_string(),
            ),
            (
                "contract_diagnostic_summary_health_status".to_string(),
                self.contract_diagnostic_summary.health_status.to_string(),
            ),
            (
                "route_admission_decision_schema".to_string(),
                self.route_admission_decision.schema.to_string(),
            ),
            (
                "route_admission_decision_status".to_string(),
                self.route_admission_decision.status_code.to_string(),
            ),
            (
                "all_supported_readiness_schema".to_string(),
                AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA.to_string(),
            ),
            (
                "readiness_count".to_string(),
                self.all_supported_capability_route_readiness
                    .len()
                    .to_string(),
            ),
            (
                "readiness_capabilities".to_string(),
                self.readiness_capabilities().join(","),
            ),
            (
                "readiness_statuses".to_string(),
                self.readiness_status_codes().join(","),
            ),
            (
                "readiness_reasons".to_string(),
                self.readiness_reason_codes().join(","),
            ),
            (
                "validation_row_groups".to_string(),
                self.validation_row_groups.join(","),
            ),
            (
                "validation_row_count".to_string(),
                validation_rows.len().to_string(),
            ),
            ("helper_names".to_string(), self.helper_names.join(",")),
            (
                "validator_names".to_string(),
                self.validator_names.join(","),
            ),
            ("issue_field".to_string(), self.issue_field.clone()),
            (
                "issue_expected".to_string(),
                route_option_value(self.issue_expected.as_deref()),
            ),
            (
                "issue_actual".to_string(),
                route_option_value(self.issue_actual.as_deref()),
            ),
        ];
        rows.extend(validation_rows);
        rows
    }

    /// Render this bundle as deterministic text lines.
    #[must_use]
    pub fn to_text_lines(&self) -> Vec<String> {
        self.to_key_value_rows()
            .into_iter()
            .map(|(key, value)| format!("{key}={value}"))
            .collect()
    }
}

/// Aggregate capability descriptor for AY public consumer APIs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolverCapabilityDescriptor {
    /// Descriptor schema identifier.
    pub schema: &'static str,
    /// Descriptor schema version.
    pub schema_version: u32,
    /// Stable solver identifier.
    pub solver: &'static str,
    /// Stable capability rows.
    pub capabilities: &'static [SolverCapability],
}

impl SolverCapabilityDescriptor {
    /// Return the row for a stable capability code, if present.
    #[must_use]
    pub fn capability(&self, code: SolverCapabilityCode) -> Option<&'static SolverCapability> {
        self.capabilities
            .iter()
            .find(|capability| capability.capability == code)
    }

    /// Return true when the descriptor reports an available public primitive.
    #[must_use]
    pub fn supports(&self, code: SolverCapabilityCode) -> bool {
        self.capability(code)
            .is_some_and(|capability| capability.status == SolverCapabilityStatus::Available)
    }

    /// Render this descriptor as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "solver": self.solver,
            "capabilities": self
                .capabilities
                .iter()
                .map(SolverCapability::to_json_value)
                .collect::<Vec<_>>(),
        })
    }

    /// Return a compact forwardable manifest for this descriptor.
    #[must_use]
    pub fn manifest(&self) -> SolverCapabilityDescriptorManifest {
        let mut capability_codes = Vec::with_capacity(self.capabilities.len());
        let mut available_capability_codes = Vec::new();
        let mut blocked_capability_codes = Vec::new();
        let mut api_symbols = Vec::new();
        let mut evidence_schemas = Vec::new();
        let mut all_capabilities_fail_closed = true;

        for capability in self.capabilities {
            capability_codes.push(capability.capability_code);
            if capability.status == SolverCapabilityStatus::Available {
                available_capability_codes.push(capability.capability_code);
            } else {
                blocked_capability_codes.push(capability.capability_code);
            }
            all_capabilities_fail_closed &= capability.fail_closed;

            for &api_symbol in capability.api_symbols {
                push_unique(&mut api_symbols, api_symbol);
            }
            for &evidence_schema in capability.evidence_schemas {
                push_unique(&mut evidence_schemas, evidence_schema);
            }
        }

        SolverCapabilityDescriptorManifest {
            schema: AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA,
            schema_version: AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION,
            descriptor_schema: self.schema,
            descriptor_schema_version: self.schema_version,
            solver: self.solver,
            capability_count: self.capabilities.len(),
            capability_codes,
            available_capability_codes,
            blocked_capability_codes,
            api_symbols,
            evidence_schemas,
            all_capabilities_fail_closed,
            capability_contracts: vec![
                model_blocking_symbolic_execution_contract(),
                incremental_assumptions_symbolic_execution_contract(),
                all_sat_enumeration_symbolic_execution_contract(),
            ],
        }
    }

    /// Render a compact deterministic key/value manifest for sidecar emitters.
    #[must_use]
    pub fn to_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        self.manifest().to_key_value_pairs()
    }
}

/// Compact forwardable manifest for AY solver capability metadata.
///
/// This manifest is designed for routing and sidecar rows. It intentionally
/// flattens the descriptor into deterministic lists so downstream consumers can
/// forward AY-owned capability metadata without depending on the broad facade
/// crate or rebuilding a local routing matrix.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SolverCapabilityDescriptorManifest {
    /// Manifest schema identifier.
    pub schema: &'static str,
    /// Manifest schema version.
    pub schema_version: u32,
    /// Source capability descriptor schema identifier.
    pub descriptor_schema: &'static str,
    /// Source capability descriptor schema version.
    pub descriptor_schema_version: u32,
    /// Stable solver identifier.
    pub solver: &'static str,
    /// Number of capabilities represented by the descriptor.
    pub capability_count: usize,
    /// Stable capability codes in descriptor order.
    pub capability_codes: Vec<&'static str>,
    /// Stable capability codes with status `available`.
    pub available_capability_codes: Vec<&'static str>,
    /// Stable capability codes with status `blocked`.
    pub blocked_capability_codes: Vec<&'static str>,
    /// Unique public Rust API symbols named by the descriptor.
    pub api_symbols: Vec<&'static str>,
    /// Unique evidence schema identifiers named by the descriptor.
    pub evidence_schemas: Vec<&'static str>,
    /// Whether every capability row is fail-closed.
    pub all_capabilities_fail_closed: bool,
    /// Capability-specific routing contracts included in this manifest.
    pub capability_contracts: Vec<SolverCapabilityContract>,
}

impl SolverCapabilityDescriptorManifest {
    /// Render this manifest as stable JSON for sidecar/evidence sinks.
    #[must_use]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "schema_version": self.schema_version,
            "descriptor_schema": self.descriptor_schema,
            "descriptor_schema_version": self.descriptor_schema_version,
            "solver": self.solver,
            "capability_count": self.capability_count,
            "capability_codes": self.capability_codes,
            "available_capabilities": self.available_capability_codes,
            "blocked_capabilities": self.blocked_capability_codes,
            "api_symbols": self.api_symbols,
            "evidence_schemas": self.evidence_schemas,
            "all_capabilities_fail_closed": self.all_capabilities_fail_closed,
            "capability_contracts": self
                .capability_contracts
                .iter()
                .map(SolverCapabilityContract::to_json_value)
                .collect::<Vec<_>>(),
        })
    }

    /// Render this manifest as deterministic string key/value pairs.
    #[must_use]
    pub fn to_key_value_pairs(&self) -> Vec<(&'static str, String)> {
        vec![
            ("schema", self.schema.to_string()),
            ("schema_version", self.schema_version.to_string()),
            ("descriptor_schema", self.descriptor_schema.to_string()),
            (
                "descriptor_schema_version",
                self.descriptor_schema_version.to_string(),
            ),
            ("solver", self.solver.to_string()),
            ("capability_count", self.capability_count.to_string()),
            ("capability_codes", self.capability_codes.join(",")),
            (
                "available_capabilities",
                self.available_capability_codes.join(","),
            ),
            (
                "blocked_capabilities",
                self.blocked_capability_codes.join(","),
            ),
            ("api_symbols", self.api_symbols.join(",")),
            ("evidence_schemas", self.evidence_schemas.join(",")),
            (
                "all_capabilities_fail_closed",
                self.all_capabilities_fail_closed.to_string(),
            ),
            (
                "capability_contracts",
                self.capability_contracts
                    .iter()
                    .map(|contract| contract.capability_code)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            (
                "model_blocking_contract_schema",
                model_blocking_symbolic_execution_contract()
                    .schema
                    .to_string(),
            ),
            (
                "model_blocking_contract_schema_version",
                model_blocking_symbolic_execution_contract()
                    .schema_version
                    .to_string(),
            ),
            ("model_blocking_api_symbols", MODEL_BLOCKING_APIS.join(",")),
            (
                "model_blocking_evidence_schemas",
                MODEL_BLOCKING_SCHEMAS.join(","),
            ),
            (
                "model_blocking_accepted_status_codes",
                AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES.join(","),
            ),
            (
                "model_blocking_rejected_status_codes",
                AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES.join(","),
            ),
            (
                "model_blocking_accepted_reason_codes",
                AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES.join(","),
            ),
            (
                "model_blocking_rejected_reason_codes",
                AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES.join(","),
            ),
            (
                "model_blocking_consumer_responsibilities",
                AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES.join(","),
            ),
            (
                "model_blocking_fail_closed",
                model_blocking_symbolic_execution_contract()
                    .fail_closed
                    .to_string(),
            ),
            (
                "incremental_assumptions_contract_schema",
                incremental_assumptions_symbolic_execution_contract()
                    .schema
                    .to_string(),
            ),
            (
                "incremental_assumptions_contract_schema_version",
                incremental_assumptions_symbolic_execution_contract()
                    .schema_version
                    .to_string(),
            ),
            (
                "incremental_assumptions_api_symbols",
                INCREMENTAL_ASSUMPTIONS_APIS.join(","),
            ),
            (
                "incremental_assumptions_evidence_schemas",
                INCREMENTAL_ASSUMPTIONS_SCHEMAS.join(","),
            ),
            (
                "incremental_assumptions_accepted_status_codes",
                AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES.join(","),
            ),
            (
                "incremental_assumptions_rejected_status_codes",
                AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES.join(","),
            ),
            (
                "incremental_assumptions_accepted_reason_codes",
                AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES.join(","),
            ),
            (
                "incremental_assumptions_rejected_reason_codes",
                AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES.join(","),
            ),
            (
                "incremental_assumptions_consumer_responsibilities",
                AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES.join(","),
            ),
            (
                "incremental_assumptions_fail_closed",
                incremental_assumptions_symbolic_execution_contract()
                    .fail_closed
                    .to_string(),
            ),
            (
                "all_sat_enumeration_contract_schema",
                all_sat_enumeration_symbolic_execution_contract()
                    .schema
                    .to_string(),
            ),
            (
                "all_sat_enumeration_contract_schema_version",
                all_sat_enumeration_symbolic_execution_contract()
                    .schema_version
                    .to_string(),
            ),
            (
                "all_sat_enumeration_api_symbols",
                ALL_SAT_ENUMERATION_APIS.join(","),
            ),
            (
                "all_sat_enumeration_evidence_schemas",
                ALL_SAT_ENUMERATION_SCHEMAS.join(","),
            ),
            (
                "all_sat_enumeration_accepted_status_codes",
                AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES.join(","),
            ),
            (
                "all_sat_enumeration_rejected_status_codes",
                AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES.join(","),
            ),
            (
                "all_sat_enumeration_accepted_reason_codes",
                AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES.join(","),
            ),
            (
                "all_sat_enumeration_rejected_reason_codes",
                AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES.join(","),
            ),
            (
                "all_sat_enumeration_consumer_responsibilities",
                AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES.join(","),
            ),
            (
                "all_sat_enumeration_fail_closed",
                all_sat_enumeration_symbolic_execution_contract()
                    .fail_closed
                    .to_string(),
            ),
        ]
    }
}

fn push_unique(items: &mut Vec<&'static str>, item: &'static str) {
    if !items.contains(&item) {
        items.push(item);
    }
}

fn contract_manifest_key(capability_code: &'static str, field: &'static str) -> &'static str {
    match (capability_code, field) {
        ("model_blocking", "capability_name") => "model_blocking_capability_name",
        ("model_blocking", "contract_schema") => "model_blocking_contract_schema",
        ("model_blocking", "contract_schema_version") => "model_blocking_contract_schema_version",
        ("model_blocking", "contract_helper") => "model_blocking_contract_helper",
        ("model_blocking", "key_value_helper") => "model_blocking_key_value_helper",
        ("model_blocking", "accepted_status_codes") => "model_blocking_accepted_status_codes",
        ("model_blocking", "rejected_status_codes") => "model_blocking_rejected_status_codes",
        ("model_blocking", "accepted_reason_codes") => "model_blocking_accepted_reason_codes",
        ("model_blocking", "rejected_reason_codes") => "model_blocking_rejected_reason_codes",
        ("model_blocking", "fail_closed") => "model_blocking_fail_closed",
        ("incremental_assumptions", "capability_name") => "incremental_assumptions_capability_name",
        ("incremental_assumptions", "contract_schema") => "incremental_assumptions_contract_schema",
        ("incremental_assumptions", "contract_schema_version") => {
            "incremental_assumptions_contract_schema_version"
        }
        ("incremental_assumptions", "contract_helper") => "incremental_assumptions_contract_helper",
        ("incremental_assumptions", "key_value_helper") => {
            "incremental_assumptions_key_value_helper"
        }
        ("incremental_assumptions", "accepted_status_codes") => {
            "incremental_assumptions_accepted_status_codes"
        }
        ("incremental_assumptions", "rejected_status_codes") => {
            "incremental_assumptions_rejected_status_codes"
        }
        ("incremental_assumptions", "accepted_reason_codes") => {
            "incremental_assumptions_accepted_reason_codes"
        }
        ("incremental_assumptions", "rejected_reason_codes") => {
            "incremental_assumptions_rejected_reason_codes"
        }
        ("incremental_assumptions", "fail_closed") => "incremental_assumptions_fail_closed",
        ("all_sat_enumeration", "capability_name") => "all_sat_enumeration_capability_name",
        ("all_sat_enumeration", "contract_schema") => "all_sat_enumeration_contract_schema",
        ("all_sat_enumeration", "contract_schema_version") => {
            "all_sat_enumeration_contract_schema_version"
        }
        ("all_sat_enumeration", "contract_helper") => "all_sat_enumeration_contract_helper",
        ("all_sat_enumeration", "key_value_helper") => "all_sat_enumeration_key_value_helper",
        ("all_sat_enumeration", "accepted_status_codes") => {
            "all_sat_enumeration_accepted_status_codes"
        }
        ("all_sat_enumeration", "rejected_status_codes") => {
            "all_sat_enumeration_rejected_status_codes"
        }
        ("all_sat_enumeration", "accepted_reason_codes") => {
            "all_sat_enumeration_accepted_reason_codes"
        }
        ("all_sat_enumeration", "rejected_reason_codes") => {
            "all_sat_enumeration_rejected_reason_codes"
        }
        ("all_sat_enumeration", "fail_closed") => "all_sat_enumeration_fail_closed",
        _ => "unknown_symbolic_execution_contract_manifest_key",
    }
}

fn route_admission_key(capability_code: &'static str, field: &'static str) -> String {
    format!("{capability_code}_route_{field}")
}

fn route_option_value(value: Option<&str>) -> String {
    value.unwrap_or("none").to_string()
}

fn expected_symbolic_execution_contract_entry(
    capability_code: &str,
) -> Option<&'static SymbolicExecutionContractManifestEntry> {
    AY_SYMBOLIC_EXECUTION_CONTRACTS
        .iter()
        .find(|entry| entry.capability_code == capability_code)
}

fn validate_symbolic_execution_contract_entry(
    entry: &SymbolicExecutionContractManifestEntry,
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    let Some(expected) = expected_symbolic_execution_contract_entry(entry.capability_code) else {
        return;
    };

    if entry.contract_schema != expected.contract_schema {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "contract_schema",
            SymbolicExecutionContractManifestHealthReason::ContractSchemaMismatch,
            Some(expected.contract_schema.to_string()),
            Some(entry.contract_schema.to_string()),
        ));
    }
    if entry.contract_schema_version != expected.contract_schema_version {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "contract_schema_version",
            SymbolicExecutionContractManifestHealthReason::ContractVersionMismatch,
            Some(expected.contract_schema_version.to_string()),
            Some(entry.contract_schema_version.to_string()),
        ));
    }
    if entry.contract_helper != expected.contract_helper || entry.contract_helper.is_empty() {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "contract_helper",
            SymbolicExecutionContractManifestHealthReason::ContractHelperMismatch,
            Some(expected.contract_helper.to_string()),
            Some(entry.contract_helper.to_string()),
        ));
    }
    if entry.key_value_helper != expected.key_value_helper || entry.key_value_helper.is_empty() {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "key_value_helper",
            SymbolicExecutionContractManifestHealthReason::KeyValueHelperMismatch,
            Some(expected.key_value_helper.to_string()),
            Some(entry.key_value_helper.to_string()),
        ));
    }
    if entry.accepted_status_codes != expected.accepted_status_codes {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "accepted_status_codes",
            SymbolicExecutionContractManifestHealthReason::StatusCodeMismatch,
            Some(expected.accepted_status_codes.join(",")),
            Some(entry.accepted_status_codes.join(",")),
        ));
    }
    if entry.rejected_status_codes != expected.rejected_status_codes {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "rejected_status_codes",
            SymbolicExecutionContractManifestHealthReason::StatusCodeMismatch,
            Some(expected.rejected_status_codes.join(",")),
            Some(entry.rejected_status_codes.join(",")),
        ));
    }
    if entry.accepted_reason_codes != expected.accepted_reason_codes {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "accepted_reason_codes",
            SymbolicExecutionContractManifestHealthReason::ReasonCodeMismatch,
            Some(expected.accepted_reason_codes.join(",")),
            Some(entry.accepted_reason_codes.join(",")),
        ));
    }
    if entry.rejected_reason_codes != expected.rejected_reason_codes {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "rejected_reason_codes",
            SymbolicExecutionContractManifestHealthReason::ReasonCodeMismatch,
            Some(expected.rejected_reason_codes.join(",")),
            Some(entry.rejected_reason_codes.join(",")),
        ));
    }
    if !entry.fail_closed {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            Some(entry.capability_code),
            "fail_closed",
            SymbolicExecutionContractManifestHealthReason::NotFailClosed,
            Some("true".to_string()),
            Some("false".to_string()),
        ));
    }
}

fn validate_unique_symbolic_execution_contracts(
    manifest: &SymbolicExecutionContractManifest,
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    for (index, entry) in manifest.contracts.iter().enumerate() {
        if manifest.contracts[..index]
            .iter()
            .any(|candidate| candidate.capability_code == entry.capability_code)
        {
            let count = manifest
                .contracts
                .iter()
                .filter(|candidate| candidate.capability_code == entry.capability_code)
                .count();
            issues.push(SymbolicExecutionContractManifestHealthIssue::new(
                Some(entry.capability_code),
                "contract",
                SymbolicExecutionContractManifestHealthReason::DuplicateContract,
                Some("single".to_string()),
                Some(format!("{}:{count}", entry.capability_code)),
            ));
        }
    }
}

fn build_symbolic_execution_contract_manifest_health_report(
    present_capabilities: Vec<&'static str>,
    issues: Vec<SymbolicExecutionContractManifestHealthIssue>,
) -> SymbolicExecutionContractManifestHealthReport {
    let accepted_for_consumer = issues.is_empty();
    let status = if accepted_for_consumer {
        SymbolicExecutionContractManifestHealthStatus::Complete
    } else {
        SymbolicExecutionContractManifestHealthStatus::Incomplete
    };
    let reason = issues.first().map_or(
        SymbolicExecutionContractManifestHealthReason::Complete,
        |issue| issue.reason,
    );
    let all_required_present = AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        .iter()
        .all(|required| present_capabilities.contains(required));
    let all_contracts_fail_closed = all_required_present
        && !issues.iter().any(|issue| {
            issue.reason == SymbolicExecutionContractManifestHealthReason::NotFailClosed
        });

    SymbolicExecutionContractManifestHealthReport {
        schema: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA_VERSION,
        status,
        status_code: status.code(),
        reason,
        reason_code: reason.code(),
        required_capabilities: AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES,
        present_capabilities,
        accepted_for_consumer,
        all_contracts_fail_closed,
        issues,
    }
}

fn key_value_pair_value<'a>(pairs: &'a [(&str, String)], key: &str) -> Option<&'a str> {
    pairs
        .iter()
        .find(|(candidate, _)| *candidate == key)
        .map(|(_, value)| value.as_str())
}

fn csv_contains(value: &str, needle: &str) -> bool {
    value.split(',').any(|part| part == needle)
}

fn diagnostic_option_value(value: Option<&str>) -> String {
    value.unwrap_or("none").to_string()
}

fn validate_unique_key_value_pair_keys(
    pairs: &[(&str, String)],
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    for (index, (key, _)) in pairs.iter().enumerate() {
        if pairs[..index].iter().any(|(candidate, _)| candidate == key) {
            let count = pairs
                .iter()
                .filter(|(candidate, _)| candidate == key)
                .count();
            issues.push(SymbolicExecutionContractManifestHealthIssue::new(
                None,
                "key_value_pair",
                SymbolicExecutionContractManifestHealthReason::DuplicateKeyValuePair,
                Some("single".to_string()),
                Some(format!("{key}:{count}")),
            ));
        }
    }
}

fn string_key_value_pair_value<'a>(pairs: &'a [(String, String)], key: &str) -> Option<&'a str> {
    pairs
        .iter()
        .find(|(candidate, _)| candidate == key)
        .map(|(_, value)| value.as_str())
}

fn validate_unique_string_key_value_pair_keys(
    pairs: &[(String, String)],
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    for (index, (key, _)) in pairs.iter().enumerate() {
        if pairs[..index].iter().any(|(candidate, _)| candidate == key) {
            let count = pairs
                .iter()
                .filter(|(candidate, _)| candidate == key)
                .count();
            issues.push(SymbolicExecutionContractManifestHealthIssue::new(
                None,
                "diagnostic_summary_key_value_pair",
                SymbolicExecutionContractManifestHealthReason::DuplicateKeyValuePair,
                Some("single".to_string()),
                Some(format!("{key}:{count}")),
            ));
        }
    }
}

fn duplicate_string_key_value_pair(pairs: &[(String, String)]) -> Option<(String, usize)> {
    for (index, (key, _)) in pairs.iter().enumerate() {
        if pairs[..index].iter().any(|(candidate, _)| candidate == key) {
            let count = pairs
                .iter()
                .filter(|(candidate, _)| candidate == key)
                .count();
            return Some((key.clone(), count));
        }
    }
    None
}

fn prefix_static_key_value_pairs(
    prefix: &str,
    pairs: Vec<(&'static str, String)>,
) -> Vec<(String, String)> {
    pairs
        .into_iter()
        .map(|(key, value)| (format!("{prefix}_{key}"), value))
        .collect()
}

fn prefix_string_key_value_rows(
    prefix: &str,
    rows: Vec<(String, String)>,
) -> Vec<(String, String)> {
    rows.into_iter()
        .map(|(key, value)| (format!("{prefix}_{key}"), value))
        .collect()
}

fn capability_contract_helper(capability: SolverCapabilityCode) -> &'static str {
    match capability {
        SolverCapabilityCode::ModelBlocking => MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_HELPER,
        SolverCapabilityCode::IncrementalAssumptions => {
            INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_HELPER
        }
        SolverCapabilityCode::AllSatEnumeration => {
            ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_HELPER
        }
        _ => "none",
    }
}

fn capability_key_value_helper(capability: SolverCapabilityCode) -> &'static str {
    match capability {
        SolverCapabilityCode::ModelBlocking => {
            MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER
        }
        SolverCapabilityCode::IncrementalAssumptions => {
            INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER
        }
        SolverCapabilityCode::AllSatEnumeration => {
            ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER
        }
        _ => "none",
    }
}

fn capability_selected_solver_path(capability: SolverCapabilityCode) -> &'static str {
    match capability {
        SolverCapabilityCode::ModelBlocking => {
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
        }
        SolverCapabilityCode::IncrementalAssumptions => {
            "ay_dpll::api::Solver::try_check_sat_assuming_with_details"
        }
        SolverCapabilityCode::AllSatEnumeration => "ay_allsat::AllSatSolver::enumerate_with_config",
        _ => "none",
    }
}

fn ay_symbolic_execution_current_revision() -> &'static str {
    option_env!("AY_BUILD_COMMIT").unwrap_or("unknown")
}

fn blocked_symbolic_execution_capability_route_readiness(
    capability: SolverCapabilityCode,
    decision: &SymbolicExecutionRouteAdmissionDecision,
    contract: Option<SolverCapabilityContract>,
    entry: Option<SymbolicExecutionContractManifestEntry>,
    reason: SymbolicExecutionCapabilityRouteReadinessReason,
    issue_field: &str,
    issue_expected: Option<String>,
    issue_actual: Option<String>,
) -> SymbolicExecutionCapabilityRouteReadiness {
    let contract_schema = contract.map_or("none", |contract| contract.schema);
    let contract_schema_version = contract.map_or(0, |contract| contract.schema_version);
    let api_symbols = contract.map_or(&[][..], |contract| contract.api_symbols);
    let evidence_schemas = contract.map_or(&[][..], |contract| contract.evidence_schemas);
    let accepted_status_codes = contract.map_or(&[][..], |contract| contract.accepted_status_codes);
    let rejected_status_codes = contract.map_or(&[][..], |contract| contract.rejected_status_codes);
    let accepted_reason_codes = contract.map_or(&[][..], |contract| contract.accepted_reason_codes);
    let rejected_reason_codes = contract.map_or(&[][..], |contract| contract.rejected_reason_codes);
    let consumer_responsibilities =
        contract.map_or(&[][..], |contract| contract.consumer_responsibilities);

    SymbolicExecutionCapabilityRouteReadiness {
        schema: AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION,
        capability,
        capability_code: capability.code(),
        capability_name: capability.name(),
        status: SymbolicExecutionCapabilityRouteReadinessStatus::Blocked,
        status_code: SymbolicExecutionCapabilityRouteReadinessStatus::Blocked.code(),
        reason,
        reason_code: reason.code(),
        selected_solver: AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER,
        selected_solver_crate: AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE,
        selected_solver_path_kind: AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND,
        selected_solver_path: capability_selected_solver_path(capability),
        supported: false,
        unsupported_reason: reason.code(),
        accepted_for_consumer: false,
        fail_closed: true,
        required_contract_revision: AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION,
        current_ay_revision_kind: AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND,
        current_ay_revision: ay_symbolic_execution_current_revision(),
        route_admission_schema: decision.schema,
        route_admission_schema_version: decision.schema_version,
        route_admission_status: decision.status_code,
        route_admission_reason: decision.reason_code,
        manifest_schema: decision.manifest_schema,
        manifest_schema_version: decision.manifest_schema_version,
        contract_schema,
        contract_schema_version,
        contract_helper: entry.map_or_else(
            || capability_contract_helper(capability),
            |entry| entry.contract_helper,
        ),
        key_value_helper: entry.map_or_else(
            || capability_key_value_helper(capability),
            |entry| entry.key_value_helper,
        ),
        api_symbols,
        evidence_schemas,
        accepted_status_codes,
        rejected_status_codes,
        accepted_reason_codes,
        rejected_reason_codes,
        consumer_responsibilities,
        issue_field: issue_field.to_string(),
        issue_expected,
        issue_actual,
    }
}

fn blocked_symbolic_execution_capability_route_readiness_from_expected(
    expected: &SymbolicExecutionCapabilityRouteReadiness,
    reason: SymbolicExecutionCapabilityRouteReadinessReason,
    issue_field: &str,
    issue_expected: Option<String>,
    issue_actual: Option<String>,
) -> SymbolicExecutionCapabilityRouteReadiness {
    let mut readiness = expected.clone();
    readiness.status = SymbolicExecutionCapabilityRouteReadinessStatus::Blocked;
    readiness.status_code = SymbolicExecutionCapabilityRouteReadinessStatus::Blocked.code();
    readiness.reason = reason;
    readiness.reason_code = reason.code();
    readiness.supported = false;
    readiness.unsupported_reason = reason.code();
    readiness.accepted_for_consumer = false;
    readiness.fail_closed = true;
    readiness.issue_field = issue_field.to_string();
    readiness.issue_expected = issue_expected;
    readiness.issue_actual = issue_actual;
    readiness
}

fn blocked_symbolic_execution_route_admission_decision(
    reason: SymbolicExecutionRouteAdmissionReason,
    issue_field: &str,
    issue_expected: Option<String>,
    issue_actual: Option<String>,
) -> SymbolicExecutionRouteAdmissionDecision {
    let mut decision = symbolic_execution_route_admission_decision();
    decision.status = SymbolicExecutionRouteAdmissionStatus::Blocked;
    decision.status_code = SymbolicExecutionRouteAdmissionStatus::Blocked.code();
    decision.reason = reason;
    decision.reason_code = reason.code();
    decision.accepted_for_consumer = false;
    decision.fail_closed = true;
    decision.issue_field = issue_field.to_string();
    decision.issue_expected = issue_expected;
    decision.issue_actual = issue_actual;
    decision
}

fn validate_summary_key_value_row(
    rows: &[(String, String)],
    key: &str,
    expected: &str,
    mismatch_reason: SymbolicExecutionContractManifestHealthReason,
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    match string_key_value_pair_value(rows, key) {
        Some(actual) if actual == expected => {}
        Some(actual) => issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            None,
            summary_field_name(key),
            mismatch_reason,
            Some(expected.to_string()),
            Some(actual.to_string()),
        )),
        None => issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            None,
            summary_field_name(key),
            SymbolicExecutionContractManifestHealthReason::MissingKeyValuePair,
            Some(expected.to_string()),
            None,
        )),
    }
}

fn diagnostic_summary_mismatch_reason(key: &str) -> SymbolicExecutionContractManifestHealthReason {
    match key {
        "schema" | "manifest_schema" | "health_schema" => {
            SymbolicExecutionContractManifestHealthReason::ManifestSchemaMismatch
        }
        "schema_version" | "manifest_schema_version" | "health_schema_version" => {
            SymbolicExecutionContractManifestHealthReason::ManifestVersionMismatch
        }
        "fail_closed" => SymbolicExecutionContractManifestHealthReason::NotFailClosed,
        "health_status" | "health_diagnostic" => {
            SymbolicExecutionContractManifestHealthReason::StatusCodeMismatch
        }
        "health_reason" | "reason_codes" => {
            SymbolicExecutionContractManifestHealthReason::ReasonCodeMismatch
        }
        _ => SymbolicExecutionContractManifestHealthReason::KeyValueMismatch,
    }
}

fn summary_field_name(key: &str) -> &'static str {
    match key {
        "schema" => "summary_schema",
        "schema_version" => "summary_schema_version",
        "manifest_schema" => "summary_manifest_schema",
        "manifest_schema_version" => "summary_manifest_schema_version",
        "manifest_identity" => "summary_manifest_identity",
        "manifest_sha256" => "summary_manifest_sha256",
        "health_schema" => "summary_health_schema",
        "health_schema_version" => "summary_health_schema_version",
        "health_status" => "summary_health_status",
        "health_diagnostic" => "summary_health_diagnostic",
        "health_reason" => "summary_health_reason",
        "accepted_for_consumer" => "summary_accepted_for_consumer",
        "fail_closed" => "summary_fail_closed",
        "contract_count" => "summary_contract_count",
        "contract_capabilities" => "summary_contract_capabilities",
        "contract_helper_count" => "summary_contract_helper_count",
        "contract_helpers" => "summary_contract_helpers",
        "key_value_helper_count" => "summary_key_value_helper_count",
        "key_value_helpers" => "summary_key_value_helpers",
        "validator_count" => "summary_validator_count",
        "validators" => "summary_validators",
        "diagnostic_helper_count" => "summary_diagnostic_helper_count",
        "diagnostic_helpers" => "summary_diagnostic_helpers",
        "issue_count" => "summary_issue_count",
        "reason_codes" => "summary_reason_codes",
        _ => "summary_unknown_field",
    }
}

fn present_capabilities_from_csv(value: &str) -> Vec<&'static str> {
    let mut present = Vec::new();
    for required_capability in AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES {
        if csv_contains(value, required_capability) {
            push_unique(&mut present, required_capability);
        }
    }
    present
}

fn symbolic_execution_contract_manifest_identity(
    manifest: &SymbolicExecutionContractManifest,
) -> String {
    format!(
        "{}@{}:{}",
        manifest.schema,
        manifest.schema_version,
        manifest
            .contracts
            .iter()
            .map(|entry| entry.capability_code)
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn symbolic_execution_contract_manifest_sha256(
    manifest: &SymbolicExecutionContractManifest,
) -> String {
    key_value_rows_sha256(&manifest.to_key_value_pairs())
}

fn key_value_rows_sha256(rows: &[(&'static str, String)]) -> String {
    let mut bytes = Vec::new();
    for (key, value) in rows {
        bytes.extend_from_slice(key.as_bytes());
        bytes.push(b'=');
        bytes.extend_from_slice(value.as_bytes());
        bytes.push(b'\n');
    }
    sha256_bytes(&bytes)
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push(hex_digit(byte >> 4));
        out.push(hex_digit(byte & 0x0f));
    }
    out
}

fn hex_digit(nibble: u8) -> char {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    HEX[usize::from(nibble)] as char
}

fn validate_key_value_pair(
    pairs: &[(&str, String)],
    capability_code: Option<&'static str>,
    key: &'static str,
    expected: &str,
    mismatch_reason: SymbolicExecutionContractManifestHealthReason,
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    match key_value_pair_value(pairs, key) {
        Some(actual) if actual == expected => {}
        Some(actual) => issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            capability_code,
            key,
            mismatch_reason,
            Some(expected.to_string()),
            Some(actual.to_string()),
        )),
        None => issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            capability_code,
            key,
            SymbolicExecutionContractManifestHealthReason::MissingKeyValuePair,
            Some(expected.to_string()),
            None,
        )),
    }
}

fn validate_entry_key_value_pairs(
    pairs: &[(&str, String)],
    expected_entry: &SymbolicExecutionContractManifestEntry,
    issues: &mut Vec<SymbolicExecutionContractManifestHealthIssue>,
) {
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "capability_name"),
        expected_entry.capability_name,
        SymbolicExecutionContractManifestHealthReason::KeyValueMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "contract_schema"),
        expected_entry.contract_schema,
        SymbolicExecutionContractManifestHealthReason::ContractSchemaMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "contract_schema_version"),
        &expected_entry.contract_schema_version.to_string(),
        SymbolicExecutionContractManifestHealthReason::ContractVersionMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "contract_helper"),
        expected_entry.contract_helper,
        SymbolicExecutionContractManifestHealthReason::ContractHelperMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "key_value_helper"),
        expected_entry.key_value_helper,
        SymbolicExecutionContractManifestHealthReason::KeyValueHelperMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "accepted_status_codes"),
        &expected_entry.accepted_status_codes.join(","),
        SymbolicExecutionContractManifestHealthReason::StatusCodeMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "rejected_status_codes"),
        &expected_entry.rejected_status_codes.join(","),
        SymbolicExecutionContractManifestHealthReason::StatusCodeMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "accepted_reason_codes"),
        &expected_entry.accepted_reason_codes.join(","),
        SymbolicExecutionContractManifestHealthReason::ReasonCodeMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "rejected_reason_codes"),
        &expected_entry.rejected_reason_codes.join(","),
        SymbolicExecutionContractManifestHealthReason::ReasonCodeMismatch,
        issues,
    );
    validate_key_value_pair(
        pairs,
        Some(expected_entry.capability_code),
        contract_manifest_key(expected_entry.capability_code, "fail_closed"),
        "true",
        SymbolicExecutionContractManifestHealthReason::NotFailClosed,
        issues,
    );
}

const CHC_PROOF_TRANSCRIPT_SCHEMA: &str = "ay.chc-proof-transcript/v1";
const CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA: &str =
    "ay.chc-proof-transcript-consumer-evidence/v1";
const CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA: &str = "ay.chc-proof-run-model-artifact/v1";
const CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA: &str =
    "ay.chc-proof-run-replay-transcript-artifact/v1";
const CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA: &str =
    "ay.chc-bmc-unsafe-trace-assignment-contract/v1";
const CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA: &str =
    "ay.chc-bmc-unsafe-trace-assignment-completeness/v1";

const FINITE_DOMAIN_ENUMERATION_APIS: &[&str] = &[
    "ay_allsat::AllSatSolver",
    "ay_allsat::AllSatConfig",
    "ay_allsat::AllSatOutcome",
];
const MODEL_BLOCKING_APIS: &[&str] = &[
    "ay_dpll::api::Solver::try_model_blocking_clause_for_consumer",
    "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer",
    "ay_dpll::api::ModelBlockingClause",
    "ay_dpll::api::ModelBlockingClauseEvidence",
    "ay_dpll::api::ModelBlockingClauseEvidence::to_key_value_pairs",
];
const ALL_SAT_ENUMERATION_APIS: &[&str] = &[
    "ay_allsat::AllSatConfig",
    "ay_allsat::AllSatOutcome",
    "ay_allsat::AllSatStats",
    "ay_allsat::AllSatSolver::iter_with_config",
    "ay_allsat::AllSatSolver::enumerate_with_config",
    "ay_allsat::AllSatSolver::enumerate_with_callback",
    "ay_allsat::AllSatSolver::count_with_config",
    "ay_allsat::AllSatSolver::stats",
    "ay_allsat::AllSatIterator::outcome",
];
const INCREMENTAL_ASSUMPTIONS_APIS: &[&str] = &[
    "ay_dpll::api::Solver::check_sat_assuming",
    "ay_dpll::api::Solver::check_sat_assuming_with_details",
    "ay_dpll::api::Solver::try_check_sat_assuming",
    "ay_dpll::api::Solver::try_check_sat_assuming_with_details",
    "ay_dpll::api::AssumptionSolveDetails",
    "ay_dpll::api::AssumptionSolveDetails::decision_profile_summary",
    "ay_dpll::api::AssumptionSolveDetails::accept_for_consumer",
    "ay_dpll::api::Solver::unsat_assumptions",
];
const CHC_PROOF_MODEL_APIS: &[&str] = &[
    "ay_chc::engines::solve_bmc_proof",
    "ay_chc::engines::solve_pdr_proof",
    "ay_chc::ChcPdrProofRun::consumer_evidence",
];
const CHC_PROOF_ARTIFACT_APIS: &[&str] = &[
    "ay_chc::ChcPdrProofRun::proof_run_artifacts",
    "ay_chc::ChcPdrProofRun::validate_model_replay_artifact_bytes",
    "ay_chc::ChcProofRunArtifactBundleValidationErrorReason",
];
const BTOR2_TRACE_REPLAY_APIS: &[&str] = &[
    "ay_chc::bmc_unsafe_trace_assignment_completeness",
    "ay_chc::bmc_unsafe_trace_assignment_contract",
    "ay_chc::ChcBmcUnsafeTraceAssignmentCompletenessReason",
];

const MODEL_BLOCKING_SCHEMAS: &[&str] = &[
    AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
];

const INCREMENTAL_ASSUMPTIONS_SCHEMAS: &[&str] = &[
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
];

const ALL_SAT_ENUMERATION_SCHEMAS: &[&str] =
    &[AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA];

/// Status codes that represent accepted model-blocking symbolic execution routing.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES: &[&str] =
    &[AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS];

/// Status codes that represent rejected/fail-closed model-blocking symbolic execution routing.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES: &[&str] =
    &[AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS];

/// Reason codes that represent accepted model-blocking symbolic execution routing.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES: &[&str] =
    &[AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON];

/// Reason codes that represent rejected/fail-closed model-blocking symbolic execution routing.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES: &[&str] =
    &[AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON];

/// Consumer responsibility codes required for model-blocking symbolic execution routing.
pub const AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES: &[&str] = &[
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_NON_EMPTY_PROJECTION,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE,
];

/// Status codes that represent accepted incremental-assumption routing.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES: &[&str] =
    &["sat", "unsat"];

/// Status codes that represent rejected/fail-closed incremental-assumption routing.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES: &[&str] =
    &["unknown", "error"];

/// Reason codes that represent accepted incremental-assumption routing.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES: &[&str] = &[
    "ay_incremental_assumption_solve_completed",
    "ay_incremental_assumption_unsat_core_available",
];

/// Reason codes that represent rejected/fail-closed incremental-assumption routing.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES: &[&str] = &[
    "ay_incremental_assumption_solve_unknown",
    "ay_incremental_assumption_solver_error_or_panic",
];

/// Consumer responsibility codes required for incremental-assumption routing.
pub const AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES: &[&str] = &[
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_BOOLEAN_ASSUMPTIONS,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_UNSAT_CORE_ON_UNSAT,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ACCEPT_MODEL_BOUNDARY,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
];

/// Status codes that represent accepted ALL-SAT enumeration routing.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES: &[&str] =
    &["exhaustive"];

/// Status codes that represent rejected/fail-closed ALL-SAT enumeration routing.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES: &[&str] =
    &["capped", "error"];

/// Reason codes that represent accepted ALL-SAT enumeration routing.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES: &[&str] =
    &["ay_all_sat_enumeration_exhaustive"];

/// Reason codes that represent rejected/fail-closed ALL-SAT enumeration routing.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES: &[&str] = &[
    "ay_all_sat_enumeration_capped",
    "ay_all_sat_solver_error_or_panic",
];

/// Consumer responsibility codes required for ALL-SAT enumeration routing.
pub const AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES: &[&str] = &[
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CAP_BOUND,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_PROJECTION_SCOPE,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE,
];

const MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_HELPER: &str =
    "ay_dpll::api::model_blocking_symbolic_execution_contract";
const MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER: &str =
    "ay_dpll::api::model_blocking_symbolic_execution_contract_key_value_pairs";
const INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_HELPER: &str =
    "ay_dpll::api::incremental_assumptions_symbolic_execution_contract";
const INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER: &str =
    "ay_dpll::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs";
const ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_HELPER: &str =
    "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract";
const ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER: &str =
    "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract_key_value_pairs";

/// Public validators for the symbolic-execution contract diagnostic round trip.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS: &[&str] = &[
    "ay_dpll::api::validate_symbolic_execution_contract_manifest",
    "ay_dpll::api::validate_symbolic_execution_contract_manifest_key_value_pairs",
    "ay_dpll::api::validate_symbolic_execution_contract_manifest_round_trip",
    "ay_dpll::api::validate_symbolic_execution_contract_manifest_diagnostic_summary",
    "ay_dpll::api::validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows",
    "ay_dpll::api::validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines",
];

/// Public diagnostic helpers for the symbolic-execution contract round trip.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS: &[&str] = &[
    "ay_dpll::api::symbolic_execution_contract_manifest_health_report",
    "ay_dpll::api::symbolic_execution_contract_manifest_round_trip_health_report",
    "ay_dpll::api::symbolic_execution_contract_manifest_health_key_value_rows",
    "ay_dpll::api::symbolic_execution_contract_manifest_health_diagnostic_lines",
    "ay_dpll::api::symbolic_execution_contract_manifest_diagnostic_summary",
    "ay_dpll::api::symbolic_execution_contract_manifest_diagnostic_summary_json",
    "ay_dpll::api::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows",
    "ay_dpll::api::symbolic_execution_contract_manifest_diagnostic_summary_text_lines",
];

/// Public validators for the symbolic-execution route admission decision.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS: &[&str] = &[
    "ay_dpll::api::validate_symbolic_execution_route_admission_decision",
    "ay_dpll::api::validate_symbolic_execution_route_admission_decision_key_value_rows",
    "ay_dpll::api::validate_symbolic_execution_route_admission_decision_text_lines",
];

/// Public helpers for the symbolic-execution route admission decision.
pub const AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_HELPERS: &[&str] = &[
    "ay_dpll::api::symbolic_execution_route_admission_decision",
    "ay_dpll::api::symbolic_execution_route_admission_decision_for_summary",
    "ay_dpll::api::symbolic_execution_route_admission_decision_json",
    "ay_dpll::api::symbolic_execution_route_admission_decision_key_value_rows",
    "ay_dpll::api::symbolic_execution_route_admission_decision_text_lines",
];

/// Public validators for per-capability symbolic-execution route readiness.
pub const AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS: &[&str] = &[
    "ay_dpll::api::validate_symbolic_execution_capability_route_readiness",
    "ay_dpll::api::validate_symbolic_execution_capability_route_readiness_key_value_rows",
    "ay_dpll::api::validate_symbolic_execution_capability_route_readiness_text_lines",
    "ay_dpll::api::validate_symbolic_execution_all_supported_capability_route_readiness",
    "ay_dpll::api::validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows",
    "ay_dpll::api::validate_symbolic_execution_all_supported_capability_route_readiness_text_lines",
];

/// Public helpers for per-capability symbolic-execution route readiness.
pub const AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS: &[&str] = &[
    "ay_dpll::api::symbolic_execution_capability_route_readiness",
    "ay_dpll::api::symbolic_execution_capability_route_readiness_for_decision",
    "ay_dpll::api::symbolic_execution_capability_route_readiness_json",
    "ay_dpll::api::symbolic_execution_capability_route_readiness_key_value_rows",
    "ay_dpll::api::symbolic_execution_capability_route_readiness_text_lines",
    "ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness",
    "ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness_for_decision",
    "ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness_json",
    "ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness_key_value_rows",
    "ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness_text_lines",
];

/// Stable validation row groups carried by the downstream contract bundle.
pub const AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATION_ROW_GROUPS: &[&str] = &[
    "solver_capability_descriptor",
    "contract_diagnostic_summary",
    "route_admission_decision",
    "all_supported_capability_route_readiness",
];

/// Public validators for the downstream symbolic-execution contract bundle.
pub const AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATORS: &[&str] = &[
    "ay_dpll::api::validate_symbolic_execution_downstream_contract_bundle",
    "ay_dpll::api::validate_symbolic_execution_downstream_contract_bundle_key_value_rows",
    "ay_dpll::api::validate_symbolic_execution_downstream_contract_bundle_text_lines",
];

/// Public helpers for the downstream symbolic-execution contract bundle.
pub const AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_HELPERS: &[&str] = &[
    "ay_dpll::api::symbolic_execution_downstream_contract_bundle",
    "ay_dpll::api::symbolic_execution_downstream_contract_bundle_json",
    "ay_dpll::api::symbolic_execution_downstream_contract_bundle_key_value_rows",
    "ay_dpll::api::symbolic_execution_downstream_contract_bundle_text_lines",
];

/// Stable symbolic-execution contract entries for downstream routing manifests.
pub const AY_SYMBOLIC_EXECUTION_CONTRACTS: &[SymbolicExecutionContractManifestEntry] = &[
    SymbolicExecutionContractManifestEntry {
        capability_code: "model_blocking",
        capability_name: "Model blocking",
        contract_schema: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        contract_schema_version: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
        contract_helper: MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_HELPER,
        key_value_helper: MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER,
        accepted_status_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
        rejected_status_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
        accepted_reason_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
        rejected_reason_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
        fail_closed: true,
    },
    SymbolicExecutionContractManifestEntry {
        capability_code: "incremental_assumptions",
        capability_name: "Incremental assumptions",
        contract_schema: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        contract_schema_version:
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
        contract_helper: INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_HELPER,
        key_value_helper: INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER,
        accepted_status_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
        rejected_status_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
        accepted_reason_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
        rejected_reason_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
        fail_closed: true,
    },
    SymbolicExecutionContractManifestEntry {
        capability_code: "all_sat_enumeration",
        capability_name: "ALL-SAT enumeration",
        contract_schema: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        contract_schema_version: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
        contract_helper: ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_HELPER,
        key_value_helper: ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_KEY_VALUE_HELPER,
        accepted_status_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
        rejected_status_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
        accepted_reason_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
        rejected_reason_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
        fail_closed: true,
    },
];

/// Required symbolic-execution contract capability codes.
pub const AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES: &[&str] = &[
    "model_blocking",
    "incremental_assumptions",
    "all_sat_enumeration",
];
const CHC_PROOF_MODEL_SCHEMAS: &[&str] = &[
    CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA,
    CHC_PROOF_TRANSCRIPT_SCHEMA,
];
const CHC_PROOF_ARTIFACT_SCHEMAS: &[&str] = &[
    CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA,
    CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA,
];
const BTOR2_TRACE_REPLAY_SCHEMAS: &[&str] = &[
    CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA,
    CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA,
];

/// Stable public capability rows for AY solver consumers.
pub const AY_SOLVER_CAPABILITIES: &[SolverCapability] = &[
    SolverCapability::available(
        SolverCapabilityCode::FiniteDomainEnumeration,
        FINITE_DOMAIN_ENUMERATION_APIS,
        &[],
    ),
    SolverCapability::available(
        SolverCapabilityCode::ModelBlocking,
        MODEL_BLOCKING_APIS,
        MODEL_BLOCKING_SCHEMAS,
    ),
    SolverCapability::available(
        SolverCapabilityCode::AllSatEnumeration,
        ALL_SAT_ENUMERATION_APIS,
        ALL_SAT_ENUMERATION_SCHEMAS,
    ),
    SolverCapability::available(
        SolverCapabilityCode::IncrementalAssumptions,
        INCREMENTAL_ASSUMPTIONS_APIS,
        INCREMENTAL_ASSUMPTIONS_SCHEMAS,
    ),
    SolverCapability::available(
        SolverCapabilityCode::ChcProofModelProduction,
        CHC_PROOF_MODEL_APIS,
        CHC_PROOF_MODEL_SCHEMAS,
    ),
    SolverCapability::available(
        SolverCapabilityCode::ChcProofArtifactBundle,
        CHC_PROOF_ARTIFACT_APIS,
        CHC_PROOF_ARTIFACT_SCHEMAS,
    ),
    SolverCapability::available(
        SolverCapabilityCode::Btor2TraceReplayCompleteness,
        BTOR2_TRACE_REPLAY_APIS,
        BTOR2_TRACE_REPLAY_SCHEMAS,
    ),
];

/// Return the model-blocking symbolic execution routing contract.
#[must_use]
pub const fn model_blocking_symbolic_execution_contract() -> SolverCapabilityContract {
    SolverCapabilityContract {
        schema: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        schema_version: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
        capability_code: SolverCapabilityCode::ModelBlocking.code(),
        api_symbols: MODEL_BLOCKING_APIS,
        evidence_schemas: MODEL_BLOCKING_SCHEMAS,
        accepted_status_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
        rejected_status_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
        accepted_reason_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
        rejected_reason_codes: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
        consumer_responsibilities: AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
        fail_closed: true,
    }
}

/// Render the model-blocking symbolic execution routing contract as key/value pairs.
#[must_use]
pub fn model_blocking_symbolic_execution_contract_key_value_pairs() -> Vec<(&'static str, String)> {
    model_blocking_symbolic_execution_contract().to_key_value_pairs()
}

/// Return the incremental-assumptions symbolic execution routing contract.
#[must_use]
pub const fn incremental_assumptions_symbolic_execution_contract() -> SolverCapabilityContract {
    SolverCapabilityContract {
        schema: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        schema_version: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
        capability_code: SolverCapabilityCode::IncrementalAssumptions.code(),
        api_symbols: INCREMENTAL_ASSUMPTIONS_APIS,
        evidence_schemas: INCREMENTAL_ASSUMPTIONS_SCHEMAS,
        accepted_status_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
        rejected_status_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
        accepted_reason_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
        rejected_reason_codes: AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
        consumer_responsibilities:
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
        fail_closed: true,
    }
}

/// Render the incremental-assumptions symbolic execution routing contract as key/value pairs.
#[must_use]
pub fn incremental_assumptions_symbolic_execution_contract_key_value_pairs(
) -> Vec<(&'static str, String)> {
    incremental_assumptions_symbolic_execution_contract().to_key_value_pairs()
}

/// Return the ALL-SAT enumeration symbolic execution routing contract.
#[must_use]
pub const fn all_sat_enumeration_symbolic_execution_contract() -> SolverCapabilityContract {
    SolverCapabilityContract {
        schema: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        schema_version: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
        capability_code: SolverCapabilityCode::AllSatEnumeration.code(),
        api_symbols: ALL_SAT_ENUMERATION_APIS,
        evidence_schemas: ALL_SAT_ENUMERATION_SCHEMAS,
        accepted_status_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
        rejected_status_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
        accepted_reason_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
        rejected_reason_codes: AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
        consumer_responsibilities:
            AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
        fail_closed: true,
    }
}

/// Render the ALL-SAT enumeration symbolic execution routing contract as key/value pairs.
#[must_use]
pub fn all_sat_enumeration_symbolic_execution_contract_key_value_pairs(
) -> Vec<(&'static str, String)> {
    all_sat_enumeration_symbolic_execution_contract().to_key_value_pairs()
}

/// Return the aggregate symbolic-execution contract manifest.
#[must_use]
pub const fn symbolic_execution_contract_manifest() -> SymbolicExecutionContractManifest {
    SymbolicExecutionContractManifest {
        schema: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION,
        solver: "ay",
        contracts: AY_SYMBOLIC_EXECUTION_CONTRACTS,
        all_contracts_fail_closed: true,
    }
}

/// Render the aggregate symbolic-execution contract manifest as JSON.
#[must_use]
pub fn symbolic_execution_contract_manifest_json() -> serde_json::Value {
    symbolic_execution_contract_manifest().to_json_value()
}

/// Render the aggregate symbolic-execution contract manifest as key/value pairs.
#[must_use]
pub fn symbolic_execution_contract_manifest_key_value_pairs() -> Vec<(&'static str, String)> {
    symbolic_execution_contract_manifest().to_key_value_pairs()
}

/// Validate the default aggregate symbolic-execution contract manifest.
#[must_use]
pub fn symbolic_execution_contract_manifest_health_report(
) -> SymbolicExecutionContractManifestHealthReport {
    validate_symbolic_execution_contract_manifest(&symbolic_execution_contract_manifest())
}

/// Validate the default manifest and its default key/value rows as a round trip.
#[must_use]
pub fn symbolic_execution_contract_manifest_round_trip_health_report(
) -> SymbolicExecutionContractManifestHealthReport {
    validate_symbolic_execution_contract_manifest_round_trip(
        &symbolic_execution_contract_manifest(),
        &symbolic_execution_contract_manifest_key_value_pairs(),
    )
}

/// Render the default manifest health report as deterministic key/value rows.
#[must_use]
pub fn symbolic_execution_contract_manifest_health_key_value_rows() -> Vec<(String, String)> {
    symbolic_execution_contract_manifest_health_report().to_diagnostic_key_value_rows()
}

/// Render the default manifest health report as stable line-oriented diagnostics.
#[must_use]
pub fn symbolic_execution_contract_manifest_health_diagnostic_lines() -> Vec<String> {
    symbolic_execution_contract_manifest_health_report().to_diagnostic_lines()
}

/// Return the compact diagnostic summary for the default manifest round trip.
#[must_use]
pub fn symbolic_execution_contract_manifest_diagnostic_summary(
) -> SymbolicExecutionContractManifestDiagnosticSummary {
    symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip(
        &symbolic_execution_contract_manifest(),
        &symbolic_execution_contract_manifest_key_value_pairs(),
    )
}

/// Render the default diagnostic summary as stable JSON.
#[must_use]
pub fn symbolic_execution_contract_manifest_diagnostic_summary_json() -> serde_json::Value {
    symbolic_execution_contract_manifest_diagnostic_summary().to_json_value()
}

/// Render the default diagnostic summary as deterministic key/value rows.
#[must_use]
pub fn symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(
) -> Vec<(String, String)> {
    symbolic_execution_contract_manifest_diagnostic_summary().to_key_value_rows()
}

/// Render the default diagnostic summary as deterministic text lines.
#[must_use]
pub fn symbolic_execution_contract_manifest_diagnostic_summary_text_lines() -> Vec<String> {
    symbolic_execution_contract_manifest_diagnostic_summary().to_text_lines()
}

/// Return the compact diagnostic summary for a manifest/key-value round trip.
#[must_use]
pub fn symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip(
    manifest: &SymbolicExecutionContractManifest,
    pairs: &[(&str, String)],
) -> SymbolicExecutionContractManifestDiagnosticSummary {
    let health = validate_symbolic_execution_contract_manifest_round_trip(manifest, pairs);
    let reason_codes = if health.issues.is_empty() {
        vec![health.reason_code]
    } else {
        let mut codes = Vec::new();
        for issue in &health.issues {
            push_unique(&mut codes, issue.reason_code);
        }
        codes
    };
    let contract_capabilities = manifest
        .contracts
        .iter()
        .map(|entry| entry.capability_code)
        .collect::<Vec<_>>();
    let contract_helpers = manifest
        .contracts
        .iter()
        .map(|entry| entry.contract_helper)
        .collect::<Vec<_>>();
    let key_value_helpers = manifest
        .contracts
        .iter()
        .map(|entry| entry.key_value_helper)
        .collect::<Vec<_>>();

    SymbolicExecutionContractManifestDiagnosticSummary {
        schema: AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA_VERSION,
        manifest_schema: manifest.schema,
        manifest_schema_version: manifest.schema_version,
        manifest_identity: symbolic_execution_contract_manifest_identity(manifest),
        manifest_sha256: symbolic_execution_contract_manifest_sha256(manifest),
        health_schema: health.schema,
        health_schema_version: health.schema_version,
        health_status: health.status_code,
        health_diagnostic: health.diagnostic_code(),
        health_reason: health.reason_code,
        accepted_for_consumer: health.accepted_for_consumer,
        fail_closed: health.all_contracts_fail_closed,
        contract_count: manifest.contracts.len(),
        contract_capabilities,
        contract_helper_count: manifest.contracts.len(),
        contract_helpers,
        key_value_helper_count: manifest.contracts.len(),
        key_value_helpers,
        validator_count: AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS.len(),
        validators: AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS,
        diagnostic_helper_count: AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS.len(),
        diagnostic_helpers: AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS,
        issue_count: health.issues.len(),
        reason_codes,
    }
}

/// Return the aggregate symbolic-execution route admission decision.
#[must_use]
pub fn symbolic_execution_route_admission_decision() -> SymbolicExecutionRouteAdmissionDecision {
    symbolic_execution_route_admission_decision_for_summary(
        &symbolic_execution_contract_manifest_diagnostic_summary(),
    )
}

/// Return the aggregate symbolic-execution route admission decision for a summary.
#[must_use]
pub fn symbolic_execution_route_admission_decision_for_summary(
    summary: &SymbolicExecutionContractManifestDiagnosticSummary,
) -> SymbolicExecutionRouteAdmissionDecision {
    let summary_report = validate_symbolic_execution_contract_manifest_diagnostic_summary(summary);
    let (
        status,
        reason,
        accepted_for_consumer,
        fail_closed,
        issue_field,
        issue_expected,
        issue_actual,
    ) = if summary_report.accepted_for_consumer && summary.fail_closed {
        (
            SymbolicExecutionRouteAdmissionStatus::Accepted,
            SymbolicExecutionRouteAdmissionReason::AYAuthoritativeRoutes,
            true,
            true,
            "none".to_string(),
            None,
            None,
        )
    } else if !summary.fail_closed {
        (
            SymbolicExecutionRouteAdmissionStatus::Blocked,
            SymbolicExecutionRouteAdmissionReason::NotFailClosed,
            false,
            true,
            "summary_fail_closed".to_string(),
            Some("true".to_string()),
            Some("false".to_string()),
        )
    } else {
        (
            SymbolicExecutionRouteAdmissionStatus::Blocked,
            SymbolicExecutionRouteAdmissionReason::SummaryRejected,
            false,
            true,
            summary_report
                .issues
                .first()
                .map_or("summary", |issue| issue.field)
                .to_string(),
            summary_report
                .issues
                .first()
                .and_then(|issue| issue.expected.clone()),
            summary_report
                .issues
                .first()
                .and_then(|issue| issue.actual.clone()),
        )
    };

    let route_capabilities = AY_SYMBOLIC_EXECUTION_CONTRACTS
        .iter()
        .map(|entry| entry.capability_code)
        .collect::<Vec<_>>();
    let authoritative_contract_helpers = AY_SYMBOLIC_EXECUTION_CONTRACTS
        .iter()
        .map(|entry| entry.contract_helper)
        .collect::<Vec<_>>();
    let authoritative_key_value_helpers = AY_SYMBOLIC_EXECUTION_CONTRACTS
        .iter()
        .map(|entry| entry.key_value_helper)
        .collect::<Vec<_>>();
    let route_authorities = AY_SYMBOLIC_EXECUTION_CONTRACTS
        .iter()
        .map(|entry| format!("{}:{}", entry.capability_code, entry.contract_helper))
        .collect::<Vec<_>>();

    SymbolicExecutionRouteAdmissionDecision {
        schema: AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA_VERSION,
        status,
        status_code: status.code(),
        reason,
        reason_code: reason.code(),
        accepted_for_consumer,
        fail_closed,
        manifest_schema: summary.manifest_schema,
        manifest_schema_version: summary.manifest_schema_version,
        diagnostic_summary_schema: summary.schema,
        diagnostic_summary_schema_version: summary.schema_version,
        manifest_identity: summary.manifest_identity.clone(),
        manifest_sha256: summary.manifest_sha256.clone(),
        health_status: summary.health_status,
        health_diagnostic: summary.health_diagnostic,
        health_reason: summary.health_reason,
        route_count: AY_SYMBOLIC_EXECUTION_CONTRACTS.len(),
        route_capabilities,
        authoritative_contract_helpers,
        authoritative_key_value_helpers,
        route_authorities,
        validators: AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS,
        issue_field,
        issue_expected,
        issue_actual,
    }
}

/// Render the aggregate symbolic-execution route admission decision as JSON.
#[must_use]
pub fn symbolic_execution_route_admission_decision_json() -> serde_json::Value {
    symbolic_execution_route_admission_decision().to_json_value()
}

/// Render the aggregate symbolic-execution route admission decision as key/value rows.
#[must_use]
pub fn symbolic_execution_route_admission_decision_key_value_rows() -> Vec<(String, String)> {
    symbolic_execution_route_admission_decision().to_key_value_rows()
}

/// Render the aggregate symbolic-execution route admission decision as text lines.
#[must_use]
pub fn symbolic_execution_route_admission_decision_text_lines() -> Vec<String> {
    symbolic_execution_route_admission_decision().to_text_lines()
}

/// Validate a typed symbolic-execution route admission decision.
#[must_use]
pub fn validate_symbolic_execution_route_admission_decision(
    decision: &SymbolicExecutionRouteAdmissionDecision,
) -> SymbolicExecutionRouteAdmissionDecision {
    validate_symbolic_execution_route_admission_decision_key_value_rows(
        &decision.to_key_value_rows(),
    )
}

/// Validate symbolic-execution route admission key/value rows.
#[must_use]
pub fn validate_symbolic_execution_route_admission_decision_key_value_rows(
    rows: &[(String, String)],
) -> SymbolicExecutionRouteAdmissionDecision {
    let expected = symbolic_execution_route_admission_decision();

    if let Some((key, count)) = duplicate_string_key_value_pair(rows) {
        return blocked_symbolic_execution_route_admission_decision(
            SymbolicExecutionRouteAdmissionReason::DuplicateRouteRow,
            "route_key_value_pair",
            Some("single".to_string()),
            Some(format!("{key}:{count}")),
        );
    }

    let expected_rows = expected.to_key_value_rows();
    if let Some((key, _)) = rows
        .iter()
        .find(|(candidate_key, _)| !expected_rows.iter().any(|(key, _)| key == candidate_key))
    {
        return blocked_symbolic_execution_route_admission_decision(
            SymbolicExecutionRouteAdmissionReason::UnknownRouteRow,
            "route_key_value_pair",
            Some("ay_symbolic_execution_route_admission_row".to_string()),
            Some(key.clone()),
        );
    }

    if let Some(actual_capabilities) = string_key_value_pair_value(rows, "route_capabilities") {
        if let Some(unknown) = actual_capabilities.split(',').find(|capability| {
            !capability.is_empty()
                && !AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES.contains(capability)
        }) {
            return blocked_symbolic_execution_route_admission_decision(
                SymbolicExecutionRouteAdmissionReason::UnknownCapability,
                "route_capabilities",
                Some(AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES.join(",")),
                Some(unknown.to_string()),
            );
        }
    }

    for (key, expected_value) in expected_rows {
        match string_key_value_pair_value(rows, &key) {
            Some(actual_value) if actual_value == expected_value => {}
            Some(actual_value) => {
                let reason = if key == "fail_closed" || key.ends_with("_route_fail_closed") {
                    SymbolicExecutionRouteAdmissionReason::NotFailClosed
                } else {
                    SymbolicExecutionRouteAdmissionReason::StaleRouteRow
                };
                return blocked_symbolic_execution_route_admission_decision(
                    reason,
                    &key,
                    Some(expected_value),
                    Some(actual_value.to_string()),
                );
            }
            None => {
                return blocked_symbolic_execution_route_admission_decision(
                    SymbolicExecutionRouteAdmissionReason::MissingRouteRow,
                    &key,
                    Some(expected_value),
                    None,
                );
            }
        }
    }

    expected
}

/// Validate symbolic-execution route admission text lines.
#[must_use]
pub fn validate_symbolic_execution_route_admission_decision_text_lines(
    lines: &[String],
) -> SymbolicExecutionRouteAdmissionDecision {
    let mut rows = Vec::new();
    for line in lines {
        match line.split_once('=') {
            Some((key, value)) if !key.is_empty() => {
                rows.push((key.to_string(), value.to_string()));
            }
            _ => {
                return blocked_symbolic_execution_route_admission_decision(
                    SymbolicExecutionRouteAdmissionReason::MalformedRouteRow,
                    "route_admission_line",
                    Some("key=value".to_string()),
                    Some(line.clone()),
                );
            }
        }
    }
    validate_symbolic_execution_route_admission_decision_key_value_rows(&rows)
}

fn symbolic_execution_contract_for_capability(
    capability: SolverCapabilityCode,
) -> Option<SolverCapabilityContract> {
    match capability {
        SolverCapabilityCode::ModelBlocking => Some(model_blocking_symbolic_execution_contract()),
        SolverCapabilityCode::IncrementalAssumptions => {
            Some(incremental_assumptions_symbolic_execution_contract())
        }
        SolverCapabilityCode::AllSatEnumeration => {
            Some(all_sat_enumeration_symbolic_execution_contract())
        }
        _ => None,
    }
}

/// Return AY-owned route readiness for one symbolic-execution capability.
#[must_use]
pub fn symbolic_execution_capability_route_readiness(
    capability: SolverCapabilityCode,
) -> SymbolicExecutionCapabilityRouteReadiness {
    symbolic_execution_capability_route_readiness_for_decision(
        capability,
        &symbolic_execution_route_admission_decision(),
    )
}

/// Return AY-owned route readiness for one capability and route decision.
#[must_use]
pub fn symbolic_execution_capability_route_readiness_for_decision(
    capability: SolverCapabilityCode,
    decision: &SymbolicExecutionRouteAdmissionDecision,
) -> SymbolicExecutionCapabilityRouteReadiness {
    let Some(contract) = symbolic_execution_contract_for_capability(capability) else {
        return blocked_symbolic_execution_capability_route_readiness(
            capability,
            decision,
            None,
            None,
            SymbolicExecutionCapabilityRouteReadinessReason::UnknownCapability,
            "capability",
            Some(AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES.join(",")),
            Some(capability.code().to_string()),
        );
    };

    let manifest = symbolic_execution_contract_manifest();
    let Some(entry) = manifest
        .contracts
        .iter()
        .find(|entry| entry.capability_code == capability.code())
        .copied()
    else {
        return blocked_symbolic_execution_capability_route_readiness(
            capability,
            decision,
            Some(contract),
            None,
            SymbolicExecutionCapabilityRouteReadinessReason::MissingManifestEntry,
            "manifest_entry",
            Some(capability.code().to_string()),
            None,
        );
    };

    let blocked = |reason, field: &str, expected: Option<String>, actual: Option<String>| {
        blocked_symbolic_execution_capability_route_readiness(
            capability,
            decision,
            Some(contract),
            Some(entry),
            reason,
            field,
            expected,
            actual,
        )
    };

    if !decision.accepted_for_consumer {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::RouteAdmissionBlocked,
            "route_admission_status",
            Some(
                SymbolicExecutionRouteAdmissionStatus::Accepted
                    .code()
                    .to_string(),
            ),
            Some(decision.status_code.to_string()),
        );
    }
    if !decision.fail_closed {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::NotFailClosed,
            "route_admission_fail_closed",
            Some("true".to_string()),
            Some("false".to_string()),
        );
    }
    if !decision.route_capabilities.contains(&capability.code()) {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::MissingManifestEntry,
            "route_capabilities",
            Some(capability.code().to_string()),
            Some(decision.route_capabilities.join(",")),
        );
    }
    if entry.contract_schema != contract.schema {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::ContractSchemaMismatch,
            "contract_schema",
            Some(contract.schema.to_string()),
            Some(entry.contract_schema.to_string()),
        );
    }
    if entry.contract_schema_version != contract.schema_version {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::ContractVersionMismatch,
            "contract_schema_version",
            Some(contract.schema_version.to_string()),
            Some(entry.contract_schema_version.to_string()),
        );
    }
    if entry.contract_helper != capability_contract_helper(capability) {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::ContractHelperMismatch,
            "contract_helper",
            Some(capability_contract_helper(capability).to_string()),
            Some(entry.contract_helper.to_string()),
        );
    }
    if entry.key_value_helper != capability_key_value_helper(capability) {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::KeyValueHelperMismatch,
            "key_value_helper",
            Some(capability_key_value_helper(capability).to_string()),
            Some(entry.key_value_helper.to_string()),
        );
    }
    if entry.accepted_status_codes != contract.accepted_status_codes
        || entry.rejected_status_codes != contract.rejected_status_codes
    {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::StatusCodeMismatch,
            "status_codes",
            Some(format!(
                "{}|{}",
                contract.accepted_status_codes.join(","),
                contract.rejected_status_codes.join(",")
            )),
            Some(format!(
                "{}|{}",
                entry.accepted_status_codes.join(","),
                entry.rejected_status_codes.join(",")
            )),
        );
    }
    if entry.accepted_reason_codes != contract.accepted_reason_codes
        || entry.rejected_reason_codes != contract.rejected_reason_codes
    {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::ReasonCodeMismatch,
            "reason_codes",
            Some(format!(
                "{}|{}",
                contract.accepted_reason_codes.join(","),
                contract.rejected_reason_codes.join(",")
            )),
            Some(format!(
                "{}|{}",
                entry.accepted_reason_codes.join(","),
                entry.rejected_reason_codes.join(",")
            )),
        );
    }
    if !entry.fail_closed || !contract.fail_closed {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::NotFailClosed,
            "fail_closed",
            Some("true".to_string()),
            Some((entry.fail_closed && contract.fail_closed).to_string()),
        );
    }
    if ay_symbolic_execution_current_revision() == "unknown" {
        return blocked(
            SymbolicExecutionCapabilityRouteReadinessReason::RevisionEvidenceUnavailable,
            "current_ay_revision",
            Some("known_ay_build_commit".to_string()),
            Some("unknown".to_string()),
        );
    }

    SymbolicExecutionCapabilityRouteReadiness {
        schema: AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION,
        capability,
        capability_code: capability.code(),
        capability_name: capability.name(),
        status: SymbolicExecutionCapabilityRouteReadinessStatus::Ready,
        status_code: SymbolicExecutionCapabilityRouteReadinessStatus::Ready.code(),
        reason: SymbolicExecutionCapabilityRouteReadinessReason::AYAuthoritativeCapabilityRoute,
        reason_code:
            SymbolicExecutionCapabilityRouteReadinessReason::AYAuthoritativeCapabilityRoute.code(),
        selected_solver: AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER,
        selected_solver_crate: AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE,
        selected_solver_path_kind: AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND,
        selected_solver_path: capability_selected_solver_path(capability),
        supported: true,
        unsupported_reason: "none",
        accepted_for_consumer: true,
        fail_closed: true,
        required_contract_revision: AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION,
        current_ay_revision_kind: AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND,
        current_ay_revision: ay_symbolic_execution_current_revision(),
        route_admission_schema: decision.schema,
        route_admission_schema_version: decision.schema_version,
        route_admission_status: decision.status_code,
        route_admission_reason: decision.reason_code,
        manifest_schema: decision.manifest_schema,
        manifest_schema_version: decision.manifest_schema_version,
        contract_schema: contract.schema,
        contract_schema_version: contract.schema_version,
        contract_helper: entry.contract_helper,
        key_value_helper: entry.key_value_helper,
        api_symbols: contract.api_symbols,
        evidence_schemas: contract.evidence_schemas,
        accepted_status_codes: contract.accepted_status_codes,
        rejected_status_codes: contract.rejected_status_codes,
        accepted_reason_codes: contract.accepted_reason_codes,
        rejected_reason_codes: contract.rejected_reason_codes,
        consumer_responsibilities: contract.consumer_responsibilities,
        issue_field: "none".to_string(),
        issue_expected: None,
        issue_actual: None,
    }
}

/// Render AY-owned capability route readiness as JSON.
#[must_use]
pub fn symbolic_execution_capability_route_readiness_json(
    capability: SolverCapabilityCode,
) -> serde_json::Value {
    symbolic_execution_capability_route_readiness(capability).to_json_value()
}

/// Render AY-owned capability route readiness as key/value rows.
#[must_use]
pub fn symbolic_execution_capability_route_readiness_key_value_rows(
    capability: SolverCapabilityCode,
) -> Vec<(String, String)> {
    symbolic_execution_capability_route_readiness(capability).to_key_value_rows()
}

/// Render AY-owned capability route readiness as text lines.
#[must_use]
pub fn symbolic_execution_capability_route_readiness_text_lines(
    capability: SolverCapabilityCode,
) -> Vec<String> {
    symbolic_execution_capability_route_readiness(capability).to_text_lines()
}

fn supported_symbolic_execution_capability_codes() -> [SolverCapabilityCode; 3] {
    [
        SolverCapabilityCode::ModelBlocking,
        SolverCapabilityCode::IncrementalAssumptions,
        SolverCapabilityCode::AllSatEnumeration,
    ]
}

/// Return AY-owned route readiness for every supported symbolic-execution capability.
#[must_use]
pub fn symbolic_execution_all_supported_capability_route_readiness(
) -> Vec<SymbolicExecutionCapabilityRouteReadiness> {
    symbolic_execution_all_supported_capability_route_readiness_for_decision(
        &symbolic_execution_route_admission_decision(),
    )
}

/// Return route readiness for every supported capability and route decision.
#[must_use]
pub fn symbolic_execution_all_supported_capability_route_readiness_for_decision(
    decision: &SymbolicExecutionRouteAdmissionDecision,
) -> Vec<SymbolicExecutionCapabilityRouteReadiness> {
    supported_symbolic_execution_capability_codes()
        .into_iter()
        .map(|capability| {
            symbolic_execution_capability_route_readiness_for_decision(capability, decision)
        })
        .collect()
}

/// Render all supported capability route readiness decisions as JSON.
#[must_use]
pub fn symbolic_execution_all_supported_capability_route_readiness_json() -> serde_json::Value {
    serde_json::Value::Array(
        symbolic_execution_all_supported_capability_route_readiness()
            .into_iter()
            .map(|readiness| readiness.to_json_value())
            .collect(),
    )
}

fn capability_route_readiness_prefix(capability: SolverCapabilityCode) -> String {
    capability.code().to_string()
}

fn prefixed_capability_route_readiness_rows(
    readiness: &[SymbolicExecutionCapabilityRouteReadiness],
) -> Vec<(String, String)> {
    readiness
        .iter()
        .flat_map(|readiness| {
            let prefix = capability_route_readiness_prefix(readiness.capability);
            readiness
                .to_key_value_rows()
                .into_iter()
                .map(move |(key, value)| (format!("{prefix}_{key}"), value))
        })
        .collect()
}

/// Render all supported capability route readiness decisions as key/value rows.
#[must_use]
pub fn symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
) -> Vec<(String, String)> {
    prefixed_capability_route_readiness_rows(
        &symbolic_execution_all_supported_capability_route_readiness(),
    )
}

/// Render all supported capability route readiness decisions as text lines.
#[must_use]
pub fn symbolic_execution_all_supported_capability_route_readiness_text_lines() -> Vec<String> {
    symbolic_execution_all_supported_capability_route_readiness_key_value_rows()
        .into_iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect()
}

/// Validate a typed per-capability symbolic-execution route readiness decision.
#[must_use]
pub fn validate_symbolic_execution_capability_route_readiness(
    readiness: &SymbolicExecutionCapabilityRouteReadiness,
) -> SymbolicExecutionCapabilityRouteReadiness {
    validate_symbolic_execution_capability_route_readiness_key_value_rows(
        readiness.capability,
        &readiness.to_key_value_rows(),
    )
}

/// Validate per-capability symbolic-execution route readiness key/value rows.
#[must_use]
pub fn validate_symbolic_execution_capability_route_readiness_key_value_rows(
    capability: SolverCapabilityCode,
    rows: &[(String, String)],
) -> SymbolicExecutionCapabilityRouteReadiness {
    let expected = symbolic_execution_capability_route_readiness(capability);

    if let Some((key, count)) = duplicate_string_key_value_pair(rows) {
        return blocked_symbolic_execution_capability_route_readiness_from_expected(
            &expected,
            SymbolicExecutionCapabilityRouteReadinessReason::DuplicateReadinessRow,
            "readiness_key_value_pair",
            Some("single".to_string()),
            Some(format!("{key}:{count}")),
        );
    }

    let expected_rows = expected.to_key_value_rows();
    if let Some((key, _)) = rows
        .iter()
        .find(|(candidate_key, _)| !expected_rows.iter().any(|(key, _)| key == candidate_key))
    {
        return blocked_symbolic_execution_capability_route_readiness_from_expected(
            &expected,
            SymbolicExecutionCapabilityRouteReadinessReason::UnknownReadinessRow,
            "readiness_key_value_pair",
            Some("ay_symbolic_execution_capability_route_readiness_row".to_string()),
            Some(key.clone()),
        );
    }

    for (key, expected_value) in expected_rows {
        match string_key_value_pair_value(rows, &key) {
            Some(actual_value) if actual_value == expected_value => {}
            Some(actual_value) => {
                let reason = if key == "capability" {
                    SymbolicExecutionCapabilityRouteReadinessReason::UnknownCapability
                } else if key == "fail_closed" || key == "route_admission_fail_closed" {
                    SymbolicExecutionCapabilityRouteReadinessReason::NotFailClosed
                } else {
                    SymbolicExecutionCapabilityRouteReadinessReason::StaleReadinessRow
                };
                return blocked_symbolic_execution_capability_route_readiness_from_expected(
                    &expected,
                    reason,
                    &key,
                    Some(expected_value),
                    Some(actual_value.to_string()),
                );
            }
            None => {
                return blocked_symbolic_execution_capability_route_readiness_from_expected(
                    &expected,
                    SymbolicExecutionCapabilityRouteReadinessReason::MissingReadinessRow,
                    &key,
                    Some(expected_value),
                    None,
                );
            }
        }
    }

    expected
}

/// Validate per-capability symbolic-execution route readiness text lines.
#[must_use]
pub fn validate_symbolic_execution_capability_route_readiness_text_lines(
    capability: SolverCapabilityCode,
    lines: &[String],
) -> SymbolicExecutionCapabilityRouteReadiness {
    let mut rows = Vec::new();
    for line in lines {
        match line.split_once('=') {
            Some((key, value)) if !key.is_empty() => {
                rows.push((key.to_string(), value.to_string()));
            }
            _ => {
                let expected = symbolic_execution_capability_route_readiness(capability);
                return blocked_symbolic_execution_capability_route_readiness_from_expected(
                    &expected,
                    SymbolicExecutionCapabilityRouteReadinessReason::MalformedReadinessRow,
                    "readiness_line",
                    Some("key=value".to_string()),
                    Some(line.clone()),
                );
            }
        }
    }
    validate_symbolic_execution_capability_route_readiness_key_value_rows(capability, &rows)
}

fn blocked_symbolic_execution_all_supported_capability_route_readiness(
    reason: SymbolicExecutionCapabilityRouteReadinessReason,
    issue_field: &str,
    issue_expected: Option<String>,
    issue_actual: Option<String>,
) -> Vec<SymbolicExecutionCapabilityRouteReadiness> {
    symbolic_execution_all_supported_capability_route_readiness()
        .into_iter()
        .map(|expected| {
            blocked_symbolic_execution_capability_route_readiness_from_expected(
                &expected,
                reason,
                issue_field,
                issue_expected.clone(),
                issue_actual.clone(),
            )
        })
        .collect()
}

/// Validate all supported per-capability symbolic-execution route readiness decisions.
#[must_use]
pub fn validate_symbolic_execution_all_supported_capability_route_readiness(
    readiness: &[SymbolicExecutionCapabilityRouteReadiness],
) -> Vec<SymbolicExecutionCapabilityRouteReadiness> {
    validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
        &prefixed_capability_route_readiness_rows(readiness),
    )
}

/// Validate all supported capability route readiness key/value rows.
#[must_use]
pub fn validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
    rows: &[(String, String)],
) -> Vec<SymbolicExecutionCapabilityRouteReadiness> {
    let expected = symbolic_execution_all_supported_capability_route_readiness();
    let expected_rows = prefixed_capability_route_readiness_rows(&expected);

    if let Some((key, count)) = duplicate_string_key_value_pair(rows) {
        return blocked_symbolic_execution_all_supported_capability_route_readiness(
            SymbolicExecutionCapabilityRouteReadinessReason::DuplicateReadinessRow,
            "all_readiness_key_value_pair",
            Some("single".to_string()),
            Some(format!("{key}:{count}")),
        );
    }

    if let Some((key, _)) = rows
        .iter()
        .find(|(candidate_key, _)| !expected_rows.iter().any(|(key, _)| key == candidate_key))
    {
        return blocked_symbolic_execution_all_supported_capability_route_readiness(
            SymbolicExecutionCapabilityRouteReadinessReason::UnknownReadinessRow,
            "all_readiness_key_value_pair",
            Some("ay_symbolic_execution_all_supported_capability_route_readiness_row".to_string()),
            Some(key.clone()),
        );
    }

    for (key, expected_value) in expected_rows {
        match string_key_value_pair_value(rows, &key) {
            Some(actual_value) if actual_value == expected_value => {}
            Some(actual_value) => {
                let reason = if key.ends_with("_fail_closed") {
                    SymbolicExecutionCapabilityRouteReadinessReason::NotFailClosed
                } else {
                    SymbolicExecutionCapabilityRouteReadinessReason::StaleReadinessRow
                };
                return blocked_symbolic_execution_all_supported_capability_route_readiness(
                    reason,
                    &key,
                    Some(expected_value),
                    Some(actual_value.to_string()),
                );
            }
            None => {
                return blocked_symbolic_execution_all_supported_capability_route_readiness(
                    SymbolicExecutionCapabilityRouteReadinessReason::MissingReadinessRow,
                    &key,
                    Some(expected_value),
                    None,
                );
            }
        }
    }

    expected
}

/// Validate all supported capability route readiness text lines.
#[must_use]
pub fn validate_symbolic_execution_all_supported_capability_route_readiness_text_lines(
    lines: &[String],
) -> Vec<SymbolicExecutionCapabilityRouteReadiness> {
    let mut rows = Vec::new();
    for line in lines {
        match line.split_once('=') {
            Some((key, value)) if !key.is_empty() => {
                rows.push((key.to_string(), value.to_string()));
            }
            _ => {
                return blocked_symbolic_execution_all_supported_capability_route_readiness(
                    SymbolicExecutionCapabilityRouteReadinessReason::MalformedReadinessRow,
                    "all_readiness_line",
                    Some("key=value".to_string()),
                    Some(line.clone()),
                );
            }
        }
    }
    validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(&rows)
}

fn symbolic_execution_downstream_contract_bundle_with_issue(
    reason: SymbolicExecutionDownstreamContractBundleReason,
    issue_field: String,
    issue_expected: Option<String>,
    issue_actual: Option<String>,
) -> SymbolicExecutionDownstreamContractBundle {
    let descriptor = solver_capability_descriptor_manifest();
    let summary = symbolic_execution_contract_manifest_diagnostic_summary();
    let route_admission = symbolic_execution_route_admission_decision_for_summary(&summary);
    let readiness =
        symbolic_execution_all_supported_capability_route_readiness_for_decision(&route_admission);
    let accepted_for_consumer = reason
        == SymbolicExecutionDownstreamContractBundleReason::AYAuthoritativeDownstreamContractBundle;
    let status = if accepted_for_consumer {
        SymbolicExecutionDownstreamContractBundleStatus::Accepted
    } else {
        SymbolicExecutionDownstreamContractBundleStatus::Blocked
    };

    SymbolicExecutionDownstreamContractBundle {
        schema: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA_VERSION,
        status,
        status_code: status.code(),
        reason,
        reason_code: reason.code(),
        accepted_for_consumer,
        fail_closed: true,
        solver: "ay",
        solver_capability_descriptor: descriptor,
        contract_diagnostic_summary: summary,
        route_admission_decision: route_admission,
        all_supported_capability_route_readiness: readiness,
        validation_row_groups:
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATION_ROW_GROUPS,
        helper_names: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_HELPERS,
        validator_names: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATORS,
        issue_field,
        issue_expected,
        issue_actual,
    }
}

/// Return the single AY-owned bundle for downstream symbolic-execution routing.
#[must_use]
pub fn symbolic_execution_downstream_contract_bundle() -> SymbolicExecutionDownstreamContractBundle
{
    let descriptor = solver_capability_descriptor_manifest();
    let summary = symbolic_execution_contract_manifest_diagnostic_summary();
    let route_admission = symbolic_execution_route_admission_decision_for_summary(&summary);
    let readiness =
        symbolic_execution_all_supported_capability_route_readiness_for_decision(&route_admission);

    let (reason, issue_field, issue_expected, issue_actual) = if !descriptor
        .all_capabilities_fail_closed
    {
        (
            SymbolicExecutionDownstreamContractBundleReason::SolverCapabilityDescriptorRejected,
            "solver_capability_descriptor_all_capabilities_fail_closed".to_string(),
            Some("true".to_string()),
            Some("false".to_string()),
        )
    } else if !summary.accepted_for_consumer || !summary.fail_closed {
        (
            if summary.fail_closed {
                SymbolicExecutionDownstreamContractBundleReason::ContractDiagnosticSummaryRejected
            } else {
                SymbolicExecutionDownstreamContractBundleReason::NotFailClosed
            },
            "contract_diagnostic_summary".to_string(),
            Some("accepted_for_consumer=true,fail_closed=true".to_string()),
            Some(format!(
                "accepted_for_consumer={},fail_closed={}",
                summary.accepted_for_consumer, summary.fail_closed
            )),
        )
    } else if !route_admission.accepted_for_consumer || !route_admission.fail_closed {
        (
            if route_admission.fail_closed {
                SymbolicExecutionDownstreamContractBundleReason::RouteAdmissionRejected
            } else {
                SymbolicExecutionDownstreamContractBundleReason::NotFailClosed
            },
            "route_admission_decision".to_string(),
            Some("accepted_for_consumer=true,fail_closed=true".to_string()),
            Some(format!(
                "accepted_for_consumer={},fail_closed={}",
                route_admission.accepted_for_consumer, route_admission.fail_closed
            )),
        )
    } else if let Some(blocked) = readiness
        .iter()
        .find(|readiness| !readiness.accepted_for_consumer || !readiness.fail_closed)
    {
        (
            if blocked.fail_closed {
                SymbolicExecutionDownstreamContractBundleReason::CapabilityRouteReadinessRejected
            } else {
                SymbolicExecutionDownstreamContractBundleReason::NotFailClosed
            },
            format!("{}_readiness", blocked.capability_code),
            Some("accepted_for_consumer=true,fail_closed=true".to_string()),
            Some(format!(
                "accepted_for_consumer={},fail_closed={}",
                blocked.accepted_for_consumer, blocked.fail_closed
            )),
        )
    } else {
        (
                SymbolicExecutionDownstreamContractBundleReason::AYAuthoritativeDownstreamContractBundle,
                "none".to_string(),
                None,
                None,
            )
    };

    let accepted_for_consumer = reason
        == SymbolicExecutionDownstreamContractBundleReason::AYAuthoritativeDownstreamContractBundle;
    let status = if accepted_for_consumer {
        SymbolicExecutionDownstreamContractBundleStatus::Accepted
    } else {
        SymbolicExecutionDownstreamContractBundleStatus::Blocked
    };

    SymbolicExecutionDownstreamContractBundle {
        schema: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA,
        schema_version: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA_VERSION,
        status,
        status_code: status.code(),
        reason,
        reason_code: reason.code(),
        accepted_for_consumer,
        fail_closed: true,
        solver: "ay",
        solver_capability_descriptor: descriptor,
        contract_diagnostic_summary: summary,
        route_admission_decision: route_admission,
        all_supported_capability_route_readiness: readiness,
        validation_row_groups:
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATION_ROW_GROUPS,
        helper_names: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_HELPERS,
        validator_names: AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATORS,
        issue_field,
        issue_expected,
        issue_actual,
    }
}

/// Render the downstream symbolic-execution contract bundle as JSON.
#[must_use]
pub fn symbolic_execution_downstream_contract_bundle_json() -> serde_json::Value {
    symbolic_execution_downstream_contract_bundle().to_json_value()
}

/// Render the downstream symbolic-execution contract bundle as key/value rows.
#[must_use]
pub fn symbolic_execution_downstream_contract_bundle_key_value_rows() -> Vec<(String, String)> {
    symbolic_execution_downstream_contract_bundle().to_key_value_rows()
}

/// Render the downstream symbolic-execution contract bundle as text lines.
#[must_use]
pub fn symbolic_execution_downstream_contract_bundle_text_lines() -> Vec<String> {
    symbolic_execution_downstream_contract_bundle().to_text_lines()
}

/// Validate a typed downstream symbolic-execution contract bundle.
#[must_use]
pub fn validate_symbolic_execution_downstream_contract_bundle(
    bundle: &SymbolicExecutionDownstreamContractBundle,
) -> SymbolicExecutionDownstreamContractBundle {
    validate_symbolic_execution_downstream_contract_bundle_key_value_rows(
        &bundle.to_key_value_rows(),
    )
}

/// Validate downstream symbolic-execution contract bundle key/value rows.
#[must_use]
pub fn validate_symbolic_execution_downstream_contract_bundle_key_value_rows(
    rows: &[(String, String)],
) -> SymbolicExecutionDownstreamContractBundle {
    let expected = symbolic_execution_downstream_contract_bundle();
    let expected_rows = expected.to_key_value_rows();

    if let Some((key, count)) = duplicate_string_key_value_pair(rows) {
        return symbolic_execution_downstream_contract_bundle_with_issue(
            SymbolicExecutionDownstreamContractBundleReason::DuplicateBundleRow,
            "bundle_key_value_pair".to_string(),
            Some("single".to_string()),
            Some(format!("{key}:{count}")),
        );
    }

    if let Some((key, _)) = rows
        .iter()
        .find(|(candidate_key, _)| !expected_rows.iter().any(|(key, _)| key == candidate_key))
    {
        return symbolic_execution_downstream_contract_bundle_with_issue(
            SymbolicExecutionDownstreamContractBundleReason::UnknownBundleRow,
            "bundle_key_value_pair".to_string(),
            Some("ay_symbolic_execution_downstream_contract_bundle_row".to_string()),
            Some(key.clone()),
        );
    }

    for (key, expected_value) in expected_rows {
        match string_key_value_pair_value(rows, &key) {
            Some(actual_value) if actual_value == expected_value => {}
            Some(actual_value) => {
                let reason = if key == "fail_closed" || key.ends_with("_fail_closed") {
                    SymbolicExecutionDownstreamContractBundleReason::NotFailClosed
                } else if key.starts_with("descriptor_") {
                    SymbolicExecutionDownstreamContractBundleReason::SolverCapabilityDescriptorRejected
                } else if key.starts_with("diagnostic_summary_") {
                    SymbolicExecutionDownstreamContractBundleReason::ContractDiagnosticSummaryRejected
                } else if key.starts_with("route_") {
                    SymbolicExecutionDownstreamContractBundleReason::RouteAdmissionRejected
                } else if key.starts_with("readiness_") {
                    SymbolicExecutionDownstreamContractBundleReason::CapabilityRouteReadinessRejected
                } else {
                    SymbolicExecutionDownstreamContractBundleReason::StaleBundleRow
                };
                return symbolic_execution_downstream_contract_bundle_with_issue(
                    reason,
                    key,
                    Some(expected_value),
                    Some(actual_value.to_string()),
                );
            }
            None => {
                return symbolic_execution_downstream_contract_bundle_with_issue(
                    SymbolicExecutionDownstreamContractBundleReason::MissingBundleRow,
                    key,
                    Some(expected_value),
                    None,
                );
            }
        }
    }

    expected
}

/// Validate downstream symbolic-execution contract bundle text lines.
#[must_use]
pub fn validate_symbolic_execution_downstream_contract_bundle_text_lines(
    lines: &[String],
) -> SymbolicExecutionDownstreamContractBundle {
    let mut rows = Vec::new();
    for line in lines {
        match line.split_once('=') {
            Some((key, value)) if !key.is_empty() => {
                rows.push((key.to_string(), value.to_string()));
            }
            _ => {
                return symbolic_execution_downstream_contract_bundle_with_issue(
                    SymbolicExecutionDownstreamContractBundleReason::MalformedBundleRow,
                    "bundle_line".to_string(),
                    Some("key=value".to_string()),
                    Some(line.clone()),
                );
            }
        }
    }
    validate_symbolic_execution_downstream_contract_bundle_key_value_rows(&rows)
}

/// Validate an aggregate symbolic-execution contract manifest.
#[must_use]
pub fn validate_symbolic_execution_contract_manifest(
    manifest: &SymbolicExecutionContractManifest,
) -> SymbolicExecutionContractManifestHealthReport {
    let mut issues = Vec::new();

    if manifest.schema != AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            None,
            "schema",
            SymbolicExecutionContractManifestHealthReason::ManifestSchemaMismatch,
            Some(AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA.to_string()),
            Some(manifest.schema.to_string()),
        ));
    }
    if manifest.schema_version != AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            None,
            "schema_version",
            SymbolicExecutionContractManifestHealthReason::ManifestVersionMismatch,
            Some(AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION.to_string()),
            Some(manifest.schema_version.to_string()),
        ));
    }
    if !manifest.all_contracts_fail_closed {
        issues.push(SymbolicExecutionContractManifestHealthIssue::new(
            None,
            "all_contracts_fail_closed",
            SymbolicExecutionContractManifestHealthReason::NotFailClosed,
            Some("true".to_string()),
            Some("false".to_string()),
        ));
    }
    validate_unique_symbolic_execution_contracts(manifest, &mut issues);

    let mut present_capabilities = Vec::new();
    for required_capability in AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES {
        if let Some(entry) = manifest
            .contracts
            .iter()
            .find(|entry| entry.capability_code == *required_capability)
        {
            push_unique(&mut present_capabilities, entry.capability_code);
            validate_symbolic_execution_contract_entry(entry, &mut issues);
        } else {
            issues.push(SymbolicExecutionContractManifestHealthIssue::new(
                Some(*required_capability),
                "contract",
                SymbolicExecutionContractManifestHealthReason::MissingRequiredContract,
                Some((*required_capability).to_string()),
                None,
            ));
        }
    }
    for entry in manifest.contracts {
        if !entry.fail_closed
            && !issues.iter().any(|issue| {
                issue.capability_code == Some(entry.capability_code)
                    && issue.field == "fail_closed"
                    && issue.reason == SymbolicExecutionContractManifestHealthReason::NotFailClosed
            })
        {
            issues.push(SymbolicExecutionContractManifestHealthIssue::new(
                Some(entry.capability_code),
                "fail_closed",
                SymbolicExecutionContractManifestHealthReason::NotFailClosed,
                Some("true".to_string()),
                Some("false".to_string()),
            ));
        }
    }

    build_symbolic_execution_contract_manifest_health_report(present_capabilities, issues)
}

/// Validate typed manifest data and forwarded key/value rows as one admission round trip.
#[must_use]
pub fn validate_symbolic_execution_contract_manifest_round_trip(
    manifest: &SymbolicExecutionContractManifest,
    pairs: &[(&str, String)],
) -> SymbolicExecutionContractManifestHealthReport {
    let manifest_report = validate_symbolic_execution_contract_manifest(manifest);
    let pair_report = validate_symbolic_execution_contract_manifest_key_value_pairs(pairs);
    let manifest_present_capabilities = manifest_report.present_capabilities.clone();
    let pair_present_capabilities = pair_report.present_capabilities.clone();
    let mut issues = manifest_report.issues;
    for issue in pair_report.issues {
        if !issues.contains(&issue) {
            issues.push(issue);
        }
    }

    let present_capabilities = AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        .iter()
        .filter(|capability| {
            manifest_present_capabilities.contains(capability)
                && pair_present_capabilities.contains(capability)
        })
        .copied()
        .collect::<Vec<_>>();

    build_symbolic_execution_contract_manifest_health_report(present_capabilities, issues)
}

/// Validate a typed diagnostic summary against the AY-owned default summary.
#[must_use]
pub fn validate_symbolic_execution_contract_manifest_diagnostic_summary(
    summary: &SymbolicExecutionContractManifestDiagnosticSummary,
) -> SymbolicExecutionContractManifestHealthReport {
    validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(
        &summary.to_key_value_rows(),
    )
}

/// Validate diagnostic summary key/value rows against the AY-owned default summary.
#[must_use]
pub fn validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(
    rows: &[(String, String)],
) -> SymbolicExecutionContractManifestHealthReport {
    let mut issues = Vec::new();
    validate_unique_string_key_value_pair_keys(rows, &mut issues);

    let expected_summary = symbolic_execution_contract_manifest_diagnostic_summary();
    for (key, expected_value) in expected_summary.to_key_value_rows() {
        validate_summary_key_value_row(
            rows,
            &key,
            &expected_value,
            diagnostic_summary_mismatch_reason(&key),
            &mut issues,
        );
    }

    let present_capabilities = present_capabilities_from_csv(
        string_key_value_pair_value(rows, "contract_capabilities").unwrap_or_default(),
    );
    build_symbolic_execution_contract_manifest_health_report(present_capabilities, issues)
}

/// Validate diagnostic summary text lines against the AY-owned default summary.
#[must_use]
pub fn validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines(
    lines: &[String],
) -> SymbolicExecutionContractManifestHealthReport {
    let mut rows = Vec::new();
    let mut issues = Vec::new();

    for line in lines {
        match line.split_once('=') {
            Some((key, value)) if !key.is_empty() => {
                rows.push((key.to_string(), value.to_string()));
            }
            _ => issues.push(SymbolicExecutionContractManifestHealthIssue::new(
                None,
                "diagnostic_summary_line",
                SymbolicExecutionContractManifestHealthReason::MalformedDiagnosticLine,
                Some("key=value".to_string()),
                Some(line.clone()),
            )),
        }
    }

    let row_report =
        validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(&rows);
    let present_capabilities = row_report.present_capabilities.clone();
    let mut merged_issues = issues;
    for issue in row_report.issues {
        if !merged_issues.contains(&issue) {
            merged_issues.push(issue);
        }
    }

    build_symbolic_execution_contract_manifest_health_report(present_capabilities, merged_issues)
}

/// Validate aggregate symbolic-execution contract manifest key/value rows.
#[must_use]
pub fn validate_symbolic_execution_contract_manifest_key_value_pairs(
    pairs: &[(&str, String)],
) -> SymbolicExecutionContractManifestHealthReport {
    let mut issues = Vec::new();

    validate_unique_key_value_pair_keys(pairs, &mut issues);

    validate_key_value_pair(
        pairs,
        None,
        "schema",
        AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
        SymbolicExecutionContractManifestHealthReason::ManifestSchemaMismatch,
        &mut issues,
    );
    validate_key_value_pair(
        pairs,
        None,
        "schema_version",
        &AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION.to_string(),
        SymbolicExecutionContractManifestHealthReason::ManifestVersionMismatch,
        &mut issues,
    );
    validate_key_value_pair(
        pairs,
        None,
        "contract_count",
        &AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
            .len()
            .to_string(),
        SymbolicExecutionContractManifestHealthReason::KeyValueMismatch,
        &mut issues,
    );
    validate_key_value_pair(
        pairs,
        None,
        "all_contracts_fail_closed",
        "true",
        SymbolicExecutionContractManifestHealthReason::NotFailClosed,
        &mut issues,
    );

    let expected_capabilities = AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES.join(",");
    validate_key_value_pair(
        pairs,
        None,
        "contract_capabilities",
        &expected_capabilities,
        SymbolicExecutionContractManifestHealthReason::MissingRequiredContract,
        &mut issues,
    );

    let mut present_capabilities = Vec::new();
    let present_capability_value = key_value_pair_value(pairs, "contract_capabilities");
    for required_capability in AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES {
        if present_capability_value.is_some_and(|value| csv_contains(value, required_capability)) {
            push_unique(&mut present_capabilities, required_capability);
        }
    }

    for expected_entry in AY_SYMBOLIC_EXECUTION_CONTRACTS {
        validate_entry_key_value_pairs(pairs, expected_entry, &mut issues);
    }

    build_symbolic_execution_contract_manifest_health_report(present_capabilities, issues)
}

/// Return the stable AY solver capability descriptor.
#[must_use]
pub const fn solver_capability_descriptor() -> SolverCapabilityDescriptor {
    SolverCapabilityDescriptor {
        schema: AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA,
        schema_version: AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
        solver: "ay",
        capabilities: AY_SOLVER_CAPABILITIES,
    }
}

/// Render the stable AY solver capability descriptor as JSON.
#[must_use]
pub fn solver_capability_descriptor_json() -> serde_json::Value {
    solver_capability_descriptor().to_json_value()
}

/// Return the compact solver capability descriptor manifest.
#[must_use]
pub fn solver_capability_descriptor_manifest() -> SolverCapabilityDescriptorManifest {
    solver_capability_descriptor().manifest()
}

/// Render the compact solver capability descriptor manifest as key/value pairs.
#[must_use]
pub fn solver_capability_descriptor_key_value_pairs() -> Vec<(&'static str, String)> {
    solver_capability_descriptor().to_key_value_pairs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capability_descriptor_reports_required_downstream_rows_from_narrow_crate() {
        let descriptor = solver_capability_descriptor();

        assert_eq!(descriptor.schema, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA);
        assert_eq!(
            descriptor.schema_version,
            AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION
        );
        assert!(descriptor.supports(SolverCapabilityCode::FiniteDomainEnumeration));
        assert!(descriptor.supports(SolverCapabilityCode::AllSatEnumeration));
        assert!(descriptor.supports(SolverCapabilityCode::IncrementalAssumptions));
        assert!(descriptor.supports(SolverCapabilityCode::ChcProofModelProduction));
        assert!(descriptor.supports(SolverCapabilityCode::ChcProofArtifactBundle));
        assert!(descriptor.supports(SolverCapabilityCode::Btor2TraceReplayCompleteness));
        assert!(descriptor.supports(SolverCapabilityCode::ModelBlocking));

        let model_blocking = descriptor
            .capability(SolverCapabilityCode::ModelBlocking)
            .expect("model-blocking row is explicit");
        assert_eq!(model_blocking.status, SolverCapabilityStatus::Available);
        assert_eq!(
            model_blocking.reason,
            SolverCapabilityReason::AYOwnedPublicApi
        );
        assert!(model_blocking.fail_closed);
        assert!(model_blocking
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_model_blocking_clause_for_consumer"));
        assert!(model_blocking
            .evidence_schemas
            .contains(&AY_MODEL_BLOCKING_CLAUSE_SCHEMA));
        assert!(model_blocking
            .evidence_schemas
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA));
    }

    #[test]
    fn capability_descriptor_json_is_machine_readable_without_facade_dependency() {
        let json = solver_capability_descriptor_json();

        assert_eq!(json["schema"], AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA);
        assert_eq!(json["solver"], "ay");
        let capabilities = json["capabilities"]
            .as_array()
            .expect("capabilities should be a JSON array");
        assert!(capabilities.iter().any(|capability| {
            capability["capability"] == "btor2_trace_replay_completeness"
                && capability["status"] == "available"
                && capability["api_symbols"].as_array().is_some_and(|symbols| {
                    symbols
                        .iter()
                        .any(|symbol| symbol == "ay_chc::bmc_unsafe_trace_assignment_completeness")
                })
        }));
        assert!(capabilities.iter().any(|capability| {
            capability["capability"] == "model_blocking"
                && capability["status"] == "available"
                && capability["reason"] == "ay_owned_public_api"
                && capability["fail_closed"] == true
        }));
        assert!(capabilities.iter().any(|capability| {
            capability["capability"] == "incremental_assumptions"
                && capability["status"] == "available"
                && capability["api_symbols"].as_array().is_some_and(|symbols| {
                    symbols.iter().any(|symbol| {
                        symbol == "ay_dpll::api::Solver::check_sat_assuming_with_details"
                    })
                })
                && capability["evidence_schemas"]
                    .as_array()
                    .is_some_and(|schemas| {
                        schemas.iter().any(|schema| {
                            schema == AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
                        })
                    })
        }));
        assert!(capabilities.iter().any(|capability| {
            capability["capability"] == "all_sat_enumeration"
                && capability["status"] == "available"
                && capability["api_symbols"].as_array().is_some_and(|symbols| {
                    symbols
                        .iter()
                        .any(|symbol| symbol == "ay_allsat::AllSatSolver::enumerate_with_config")
                })
                && capability["evidence_schemas"]
                    .as_array()
                    .is_some_and(|schemas| {
                        schemas.iter().any(|schema| {
                            schema == AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
                        })
                    })
        }));
    }

    #[test]
    fn capability_descriptor_manifest_is_forwardable_key_value_metadata() {
        let manifest = solver_capability_descriptor_manifest();

        assert_eq!(
            manifest.schema,
            AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA
        );
        assert_eq!(
            manifest.schema_version,
            AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION
        );
        assert_eq!(
            manifest.descriptor_schema,
            AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA
        );
        assert_eq!(manifest.solver, "ay");
        assert_eq!(manifest.capability_count, AY_SOLVER_CAPABILITIES.len());
        assert!(manifest.capability_codes.contains(&"model_blocking"));
        assert!(manifest
            .available_capability_codes
            .contains(&"model_blocking"));
        assert!(manifest.blocked_capability_codes.is_empty());
        assert!(manifest
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"));
        assert!(manifest
            .evidence_schemas
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA));
        assert!(manifest.all_capabilities_fail_closed);
        let model_blocking_contract = manifest
            .capability_contracts
            .iter()
            .find(|contract| contract.capability_code == "model_blocking")
            .expect("model-blocking contract is included");
        let incremental_assumptions_contract = manifest
            .capability_contracts
            .iter()
            .find(|contract| contract.capability_code == "incremental_assumptions")
            .expect("incremental-assumptions contract is included");
        let all_sat_enumeration_contract = manifest
            .capability_contracts
            .iter()
            .find(|contract| contract.capability_code == "all_sat_enumeration")
            .expect("ALL-SAT enumeration contract is included");
        assert_eq!(
            model_blocking_contract.schema,
            AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert!(model_blocking_contract
            .accepted_status_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS));
        assert!(model_blocking_contract
            .rejected_status_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS));
        assert!(model_blocking_contract.fail_closed);
        assert_eq!(
            incremental_assumptions_contract.schema,
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert!(incremental_assumptions_contract
            .accepted_status_codes
            .contains(&"sat"));
        assert!(incremental_assumptions_contract
            .accepted_status_codes
            .contains(&"unsat"));
        assert!(incremental_assumptions_contract
            .rejected_status_codes
            .contains(&"unknown"));
        assert!(incremental_assumptions_contract.fail_closed);
        assert_eq!(
            all_sat_enumeration_contract.schema,
            AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert!(all_sat_enumeration_contract
            .api_symbols
            .contains(&"ay_allsat::AllSatSolver::enumerate_with_config"));
        assert!(all_sat_enumeration_contract
            .accepted_status_codes
            .contains(&"exhaustive"));
        assert!(all_sat_enumeration_contract
            .rejected_status_codes
            .contains(&"capped"));
        assert!(all_sat_enumeration_contract
            .consumer_responsibilities
            .contains(&AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME));
        assert!(all_sat_enumeration_contract.fail_closed);

        let json = manifest.to_json_value();
        assert_eq!(
            json["schema"],
            AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA
        );
        assert_eq!(json["capability_count"], AY_SOLVER_CAPABILITIES.len());
        assert!(json["capability_contracts"].as_array().is_some_and(|contracts| {
            contracts.iter().any(|contract| {
                contract["capability"] == "model_blocking"
                    && contract["fail_closed"] == true
                    && contract["accepted_status_codes"]
                        .as_array()
                        .is_some_and(|codes| {
                            codes.iter().any(|code| {
                                code == AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS
                            })
                        })
                    && contract["consumer_responsibilities"]
                        .as_array()
                        .is_some_and(|responsibilities| {
                            responsibilities.iter().any(|responsibility| {
                                responsibility
                                    == AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY
                            })
                        })
            })
        }));
        assert!(json["capability_contracts"].as_array().is_some_and(|contracts| {
            contracts.iter().any(|contract| {
                contract["capability"] == "incremental_assumptions"
                    && contract["fail_closed"] == true
                    && contract["accepted_status_codes"]
                        .as_array()
                        .is_some_and(|codes| codes.iter().any(|code| code == "unsat"))
                    && contract["consumer_responsibilities"]
                        .as_array()
                        .is_some_and(|responsibilities| {
                            responsibilities.iter().any(|responsibility| {
                                responsibility
                                    == AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS
                            })
                        })
            })
        }));
        assert!(json["capability_contracts"].as_array().is_some_and(|contracts| {
            contracts.iter().any(|contract| {
                contract["capability"] == "all_sat_enumeration"
                    && contract["fail_closed"] == true
                    && contract["rejected_status_codes"]
                        .as_array()
                        .is_some_and(|codes| codes.iter().any(|code| code == "capped"))
                    && contract["consumer_responsibilities"]
                        .as_array()
                        .is_some_and(|responsibilities| {
                            responsibilities.iter().any(|responsibility| {
                                responsibility
                                    == AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION
                            })
                        })
            })
        }));
        assert!(json["api_symbols"].as_array().is_some_and(|symbols| {
            symbols.iter().any(|symbol| {
                symbol == "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
            })
        }));

        let pairs = solver_capability_descriptor_key_value_pairs();
        assert_eq!(pairs[0], ("schema", manifest.schema.to_string()));
        assert!(pairs.contains(&("solver", "ay".to_string())));
        assert!(pairs.contains(&(
            "descriptor_schema",
            AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA.to_string()
        )));
        assert!(pairs
            .iter()
            .any(|(key, value)| *key == "capability_codes" && value.contains("model_blocking")));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "evidence_schemas" && value.contains(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "model_blocking_accepted_status_codes"
                && value.contains(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "model_blocking_api_symbols"
                && value
                    .contains("ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "model_blocking_evidence_schemas"
                && value.contains(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "model_blocking_rejected_reason_codes"
                && value.contains(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "model_blocking_consumer_responsibilities"
                && value.contains(AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION)
        }));
        assert!(pairs.contains(&("model_blocking_fail_closed", "true".to_string())));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "capability_contracts"
                && value.contains("model_blocking")
                && value.contains("incremental_assumptions")
                && value.contains("all_sat_enumeration")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "incremental_assumptions_api_symbols"
                && value.contains("ay_dpll::api::Solver::try_check_sat_assuming_with_details")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "incremental_assumptions_evidence_schemas"
                && value.contains(AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "incremental_assumptions_accepted_status_codes"
                && value.contains("sat")
                && value.contains("unsat")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "incremental_assumptions_rejected_reason_codes"
                && value.contains("ay_incremental_assumption_solver_error_or_panic")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "incremental_assumptions_consumer_responsibilities"
                && value.contains(
                    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
                )
        }));
        assert!(pairs.contains(&("incremental_assumptions_fail_closed", "true".to_string())));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "all_sat_enumeration_api_symbols"
                && value.contains("ay_allsat::AllSatSolver::enumerate_with_config")
                && value.contains("ay_allsat::AllSatIterator::outcome")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "all_sat_enumeration_evidence_schemas"
                && value.contains(AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "all_sat_enumeration_accepted_status_codes" && value.contains("exhaustive")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "all_sat_enumeration_rejected_reason_codes"
                && value.contains("ay_all_sat_enumeration_capped")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "all_sat_enumeration_consumer_responsibilities"
                && value.contains(AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME)
        }));
        assert!(pairs.contains(&("all_sat_enumeration_fail_closed", "true".to_string())));
    }

    #[test]
    fn model_blocking_contract_exposes_symbolic_execution_routing_vocabulary() {
        let contract = model_blocking_symbolic_execution_contract();
        let contract_pairs = model_blocking_symbolic_execution_contract_key_value_pairs();

        assert_eq!(
            contract.schema,
            AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(contract.capability_code, "model_blocking");
        assert!(contract
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_model_blocking_clause_for_consumer"));
        assert!(contract
            .api_symbols
            .contains(&"ay_dpll::api::ModelBlockingClauseEvidence::to_key_value_pairs"));
        assert!(contract
            .evidence_schemas
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA));
        assert!(contract
            .accepted_status_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS));
        assert!(contract
            .rejected_status_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS));
        assert!(contract
            .accepted_reason_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON));
        assert!(contract
            .rejected_reason_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION));
        assert!(contract.fail_closed);

        let pairs = contract.to_key_value_pairs();
        assert_eq!(pairs, contract_pairs);
        assert!(pairs.contains(&(
            "schema",
            AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA.to_string()
        )));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "rejected_status_codes"
                && value.contains(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS)
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "consumer_responsibilities"
                && value.contains(AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE)
        }));
    }

    #[test]
    fn incremental_assumptions_contract_exposes_symbolic_execution_routing_vocabulary() {
        let contract = incremental_assumptions_symbolic_execution_contract();
        let contract_pairs = incremental_assumptions_symbolic_execution_contract_key_value_pairs();

        assert_eq!(
            contract.schema,
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(contract.capability_code, "incremental_assumptions");
        assert!(contract
            .api_symbols
            .contains(&"ay_dpll::api::Solver::check_sat_assuming_with_details"));
        assert!(contract
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_check_sat_assuming_with_details"));
        assert!(contract
            .evidence_schemas
            .contains(&AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA));
        assert!(contract.accepted_status_codes.contains(&"sat"));
        assert!(contract.accepted_status_codes.contains(&"unsat"));
        assert!(contract.rejected_status_codes.contains(&"unknown"));
        assert!(contract.rejected_status_codes.contains(&"error"));
        assert!(contract
            .accepted_reason_codes
            .contains(&"ay_incremental_assumption_solve_completed"));
        assert!(contract
            .rejected_reason_codes
            .contains(&"ay_incremental_assumption_solver_error_or_panic"));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_BOOLEAN_ASSUMPTIONS));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION));
        assert!(contract.fail_closed);

        let pairs = contract.to_key_value_pairs();
        assert_eq!(pairs, contract_pairs);
        assert!(pairs.contains(&(
            "schema",
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA.to_string()
        )));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "accepted_status_codes" && value.contains("sat") && value.contains("unsat")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "consumer_responsibilities"
                && value.contains(
                    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ACCEPT_MODEL_BOUNDARY,
                )
        }));
        assert!(pairs.contains(&("fail_closed", "true".to_string())));
    }

    #[test]
    fn all_sat_enumeration_contract_exposes_symbolic_execution_routing_vocabulary() {
        let contract = all_sat_enumeration_symbolic_execution_contract();
        let contract_pairs = all_sat_enumeration_symbolic_execution_contract_key_value_pairs();

        assert_eq!(
            contract.schema,
            AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(contract.capability_code, "all_sat_enumeration");
        assert!(contract
            .api_symbols
            .contains(&"ay_allsat::AllSatSolver::enumerate_with_config"));
        assert!(contract
            .api_symbols
            .contains(&"ay_allsat::AllSatIterator::outcome"));
        assert!(contract
            .evidence_schemas
            .contains(&AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA));
        assert!(contract.accepted_status_codes.contains(&"exhaustive"));
        assert!(contract.rejected_status_codes.contains(&"capped"));
        assert!(contract.rejected_status_codes.contains(&"error"));
        assert!(contract
            .accepted_reason_codes
            .contains(&"ay_all_sat_enumeration_exhaustive"));
        assert!(contract
            .rejected_reason_codes
            .contains(&"ay_all_sat_enumeration_capped"));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CAP_BOUND));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME));
        assert!(contract
            .consumer_responsibilities
            .contains(&AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION));
        assert!(contract.fail_closed);

        let pairs = contract.to_key_value_pairs();
        assert_eq!(pairs, contract_pairs);
        assert!(pairs.contains(&(
            "schema",
            AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA.to_string()
        )));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "accepted_status_codes" && value.contains("exhaustive")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "consumer_responsibilities"
                && value
                    .contains(AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE)
        }));
        assert!(pairs.contains(&("fail_closed", "true".to_string())));
    }

    #[test]
    fn symbolic_execution_contract_manifest_aggregates_routing_contracts() {
        let manifest = symbolic_execution_contract_manifest();

        assert_eq!(
            manifest.schema,
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA
        );
        assert_eq!(
            manifest.schema_version,
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION
        );
        assert_eq!(manifest.solver, "ay");
        assert_eq!(manifest.contracts, AY_SYMBOLIC_EXECUTION_CONTRACTS);
        assert_eq!(manifest.contracts.len(), 3);
        assert!(manifest.all_contracts_fail_closed);

        let model_blocking = manifest
            .contracts
            .iter()
            .find(|entry| entry.capability_code == "model_blocking")
            .expect("model-blocking contract entry is present");
        let incremental = manifest
            .contracts
            .iter()
            .find(|entry| entry.capability_code == "incremental_assumptions")
            .expect("incremental-assumptions contract entry is present");
        let all_sat = manifest
            .contracts
            .iter()
            .find(|entry| entry.capability_code == "all_sat_enumeration")
            .expect("ALL-SAT contract entry is present");

        assert_eq!(model_blocking.capability_name, "Model blocking");
        assert_eq!(
            model_blocking.contract_schema,
            AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            model_blocking.contract_helper,
            "ay_dpll::api::model_blocking_symbolic_execution_contract"
        );
        assert!(model_blocking
            .accepted_status_codes
            .contains(&AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS));
        assert!(model_blocking.fail_closed);

        assert_eq!(incremental.capability_name, "Incremental assumptions");
        assert_eq!(
            incremental.contract_schema,
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            incremental.key_value_helper,
            "ay_dpll::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs"
        );
        assert!(incremental.accepted_status_codes.contains(&"sat"));
        assert!(incremental.rejected_status_codes.contains(&"unknown"));
        assert!(incremental.fail_closed);

        assert_eq!(all_sat.capability_name, "ALL-SAT enumeration");
        assert_eq!(
            all_sat.contract_schema,
            AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            all_sat.contract_helper,
            "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
        );
        assert!(all_sat.accepted_status_codes.contains(&"exhaustive"));
        assert!(all_sat.rejected_status_codes.contains(&"capped"));
        assert!(all_sat.fail_closed);

        let json = symbolic_execution_contract_manifest_json();
        assert_eq!(
            json["schema"],
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA
        );
        assert_eq!(json["contract_count"], 3);
        assert_eq!(json["all_contracts_fail_closed"], true);
        assert!(json["contracts"].as_array().is_some_and(|contracts| {
            contracts.iter().any(|contract| {
                contract["capability"] == "all_sat_enumeration"
                    && contract["contract_schema"]
                        == AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
                    && contract["contract_helper"]
                        == "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
                    && contract["rejected_status_codes"]
                        .as_array()
                        .is_some_and(|codes| codes.iter().any(|code| code == "capped"))
            })
        }));

        let pairs = symbolic_execution_contract_manifest_key_value_pairs();
        assert!(pairs.contains(&(
            "schema",
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA.to_string()
        )));
        assert!(pairs.contains(&("contract_count", "3".to_string())));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "contract_capabilities"
                && value.contains("model_blocking")
                && value.contains("incremental_assumptions")
                && value.contains("all_sat_enumeration")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "contract_helpers"
                && value.contains("ay_dpll::api::model_blocking_symbolic_execution_contract")
                && value
                    .contains("ay_dpll::api::incremental_assumptions_symbolic_execution_contract")
                && value.contains("ay_dpll::api::all_sat_enumeration_symbolic_execution_contract")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "contract_schemas"
                && value.contains(AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA)
                && value.contains(AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA)
                && value.contains(AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA)
        }));
        assert!(pairs.contains(&("all_contracts_fail_closed", "true".to_string())));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "model_blocking_contract_helper"
                && value == "ay_dpll::api::model_blocking_symbolic_execution_contract"
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "incremental_assumptions_accepted_status_codes"
                && value.contains("sat")
                && value.contains("unsat")
        }));
        assert!(pairs.iter().any(|(key, value)| {
            *key == "all_sat_enumeration_rejected_status_codes" && value.contains("capped")
        }));
    }

    #[test]
    fn symbolic_execution_contract_manifest_health_report_accepts_complete_manifest() {
        let report = symbolic_execution_contract_manifest_health_report();
        let manifest_report =
            validate_symbolic_execution_contract_manifest(&symbolic_execution_contract_manifest());
        let key_value_report = validate_symbolic_execution_contract_manifest_key_value_pairs(
            &symbolic_execution_contract_manifest_key_value_pairs(),
        );

        assert_eq!(report, manifest_report);
        assert_eq!(
            report.schema,
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA
        );
        assert_eq!(
            report.schema_version,
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA_VERSION
        );
        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Complete
        );
        assert_eq!(report.status_code, "complete");
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::Complete
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::Healthy
        );
        assert_eq!(report.diagnostic_code(), "healthy");
        assert_eq!(
            report.required_capabilities,
            AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        );
        assert_eq!(
            report.present_capabilities,
            AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        );
        assert!(report.accepted_for_consumer);
        assert!(report.all_contracts_fail_closed);
        assert!(report.issues.is_empty());

        let json = report.to_json_value();
        assert_eq!(
            json["schema"],
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA
        );
        assert_eq!(json["status"], "complete");
        assert_eq!(json["diagnostic"], "healthy");
        assert_eq!(json["accepted_for_consumer"], true);
        assert_eq!(json["issue_count"], 0);

        let pairs = report.to_key_value_pairs();
        assert!(pairs.contains(&("status", "complete".to_string())));
        assert!(pairs.contains(&("diagnostic", "healthy".to_string())));
        assert!(pairs.contains(&("accepted_for_consumer", "true".to_string())));
        assert!(pairs.contains(&("issue_count", "0".to_string())));

        let diagnostic_rows = symbolic_execution_contract_manifest_health_key_value_rows();
        assert!(diagnostic_rows.contains(&("diagnostic".to_string(), "healthy".to_string())));
        assert!(
            diagnostic_rows.contains(&("accepted_for_consumer".to_string(), "true".to_string()))
        );
        let diagnostic_lines = symbolic_execution_contract_manifest_health_diagnostic_lines();
        assert!(diagnostic_lines.contains(&"diagnostic=healthy".to_string()));
        assert!(diagnostic_lines.contains(&"issue_count=0".to_string()));

        let round_trip_report = symbolic_execution_contract_manifest_round_trip_health_report();
        assert_eq!(round_trip_report.status, report.status);
        assert_eq!(round_trip_report.diagnostic(), report.diagnostic());
        assert!(round_trip_report.accepted_for_consumer);
        assert!(round_trip_report.issues.is_empty());

        assert_eq!(key_value_report.status, report.status);
        assert!(key_value_report.accepted_for_consumer);
        assert!(key_value_report.issues.is_empty());
    }

    #[test]
    fn symbolic_execution_contract_diagnostic_summary_matches_health_and_rows() {
        let manifest = symbolic_execution_contract_manifest();
        let health = symbolic_execution_contract_manifest_round_trip_health_report();
        let summary = symbolic_execution_contract_manifest_diagnostic_summary();

        assert_eq!(
            summary.schema,
            AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA
        );
        assert_eq!(
            summary.schema_version,
            AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA_VERSION
        );
        assert_eq!(summary.manifest_schema, manifest.schema);
        assert_eq!(summary.manifest_schema_version, manifest.schema_version);
        assert_eq!(
            summary.manifest_identity,
            symbolic_execution_contract_manifest_identity(&manifest)
        );
        assert_eq!(
            summary.manifest_sha256,
            symbolic_execution_contract_manifest_sha256(&manifest)
        );
        assert_eq!(summary.manifest_sha256.len(), 64);
        assert_eq!(summary.health_schema, health.schema);
        assert_eq!(summary.health_status, health.status_code);
        assert_eq!(summary.health_diagnostic, health.diagnostic_code());
        assert_eq!(summary.health_reason, health.reason_code);
        assert_eq!(summary.accepted_for_consumer, health.accepted_for_consumer);
        assert_eq!(summary.fail_closed, health.all_contracts_fail_closed);
        assert_eq!(summary.contract_count, manifest.contracts.len());
        assert_eq!(
            summary.contract_helper_count,
            summary.contract_helpers.len()
        );
        assert_eq!(
            summary.key_value_helper_count,
            summary.key_value_helpers.len()
        );
        assert_eq!(
            summary.validator_count,
            AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS.len()
        );
        assert_eq!(
            summary.diagnostic_helper_count,
            AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS.len()
        );
        assert_eq!(summary.issue_count, health.issues.len());
        assert_eq!(summary.reason_codes, vec![health.reason_code]);

        let json = symbolic_execution_contract_manifest_diagnostic_summary_json();
        assert_eq!(
            json["schema"],
            AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA
        );
        assert_eq!(json["health_status"], health.status_code);
        assert_eq!(json["fail_closed"], true);
        assert_eq!(json["contract_count"], manifest.contracts.len());

        let rows = symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows();
        assert_eq!(rows, summary.to_key_value_rows());
        assert!(rows.contains(&(
            "schema".to_string(),
            AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA.to_string()
        )));
        assert!(rows.contains(&(
            "manifest_sha256".to_string(),
            summary.manifest_sha256.clone()
        )));
        assert!(rows.contains(&("health_status".to_string(), "complete".to_string())));
        assert!(rows.contains(&("fail_closed".to_string(), "true".to_string())));

        let lines = symbolic_execution_contract_manifest_diagnostic_summary_text_lines();
        assert_eq!(lines, summary.to_text_lines());
        assert!(lines.contains(&format!("manifest_sha256={}", summary.manifest_sha256)));
        assert!(lines.contains(&"health_status=complete".to_string()));
        assert!(lines.contains(&"fail_closed=true".to_string()));

        assert!(
            validate_symbolic_execution_contract_manifest_diagnostic_summary(&summary)
                .accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(&rows)
                .accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines(&lines)
                .accepted_for_consumer
        );
    }

    #[test]
    fn symbolic_execution_contract_diagnostic_summary_rejects_stale_version() {
        let mut summary = symbolic_execution_contract_manifest_diagnostic_summary();
        summary.schema_version = 0;

        let report = validate_symbolic_execution_contract_manifest_diagnostic_summary(&summary);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::ManifestVersionMismatch
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.issues.iter().any(|issue| {
            issue.field == "summary_schema_version"
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::ManifestVersionMismatch
                && issue.expected.as_deref() == Some("1")
                && issue.actual.as_deref() == Some("0")
        }));
    }

    #[test]
    fn symbolic_execution_contract_diagnostic_summary_rejects_mismatched_rows() {
        let mut rows = symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows();
        for (key, value) in &mut rows {
            if key == "manifest_sha256" {
                *value = "stale-digest".to_string();
            }
        }

        let report =
            validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(&rows);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::KeyValueMismatch
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.issues.iter().any(|issue| {
            issue.field == "summary_manifest_sha256"
                && issue.reason == SymbolicExecutionContractManifestHealthReason::KeyValueMismatch
                && issue.actual.as_deref() == Some("stale-digest")
        }));
    }

    #[test]
    fn symbolic_execution_contract_diagnostic_summary_rejects_malformed_text() {
        let mut lines = symbolic_execution_contract_manifest_diagnostic_summary_text_lines();
        lines.push("malformed-summary-line".to_string());

        let report =
            validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines(&lines);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::MalformedDiagnosticLine
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.issues.iter().any(|issue| {
            issue.field == "diagnostic_summary_line"
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::MalformedDiagnosticLine
                && issue.actual.as_deref() == Some("malformed-summary-line")
        }));
    }

    #[test]
    fn symbolic_execution_contract_diagnostic_summary_rejects_unclosed_summary() {
        let mut summary = symbolic_execution_contract_manifest_diagnostic_summary();
        summary.fail_closed = false;

        let report = validate_symbolic_execution_contract_manifest_diagnostic_summary(&summary);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::NotFailClosed
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::FailClosedViolation
        );
        assert!(!report.accepted_for_consumer);
        assert!(!report.all_contracts_fail_closed);
    }

    #[test]
    fn symbolic_execution_route_admission_accepts_authoritative_routes() {
        let decision = symbolic_execution_route_admission_decision();

        assert_eq!(
            decision.schema,
            AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA
        );
        assert_eq!(
            decision.schema_version,
            AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA_VERSION
        );
        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Accepted
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::AYAuthoritativeRoutes
        );
        assert!(decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(decision.route_count, 3);
        assert_eq!(
            decision.route_capabilities,
            AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        );
        assert!(decision.route_authorities.contains(
            &"model_blocking:ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
        ));
        assert!(decision.route_authorities.contains(
            &"incremental_assumptions:ay_dpll::api::incremental_assumptions_symbolic_execution_contract".to_string()
        ));
        assert!(decision.route_authorities.contains(
            &"all_sat_enumeration:ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
                .to_string()
        ));
        assert_eq!(decision.issue_field, "none");

        let json = symbolic_execution_route_admission_decision_json();
        assert_eq!(json["schema"], AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA);
        assert_eq!(json["status"], "accepted");
        assert_eq!(json["reason"], "ay_authoritative_routes");
        assert_eq!(json["fail_closed"], true);

        let rows = symbolic_execution_route_admission_decision_key_value_rows();
        assert_eq!(rows, decision.to_key_value_rows());
        assert!(rows.contains(&("status".to_string(), "accepted".to_string())));
        assert!(rows.contains(&(
            "route_capabilities".to_string(),
            "model_blocking,incremental_assumptions,all_sat_enumeration".to_string()
        )));
        assert!(rows.contains(&(
            "model_blocking_route_contract_helper".to_string(),
            "ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
        )));
        assert!(rows.contains(&(
            "incremental_assumptions_route_key_value_helper".to_string(),
            "ay_dpll::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs"
                .to_string()
        )));
        assert!(rows.contains(&(
            "all_sat_enumeration_route_fail_closed".to_string(),
            "true".to_string()
        )));

        let lines = symbolic_execution_route_admission_decision_text_lines();
        assert_eq!(lines, decision.to_text_lines());
        assert!(lines.contains(&"reason=ay_authoritative_routes".to_string()));
        assert!(lines.contains(&"model_blocking_route_fail_closed=true".to_string()));

        assert!(
            validate_symbolic_execution_route_admission_decision(&decision).accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_route_admission_decision_key_value_rows(&rows)
                .accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_route_admission_decision_text_lines(&lines)
                .accepted_for_consumer
        );
    }

    #[test]
    fn symbolic_execution_capability_route_readiness_accepts_model_blocking_route() {
        let readiness =
            symbolic_execution_capability_route_readiness(SolverCapabilityCode::ModelBlocking);

        assert_eq!(
            readiness.schema,
            AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA
        );
        assert_eq!(
            readiness.schema_version,
            AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION
        );
        assert_eq!(readiness.capability, SolverCapabilityCode::ModelBlocking);
        assert_eq!(
            readiness.status,
            SymbolicExecutionCapabilityRouteReadinessStatus::Ready
        );
        assert_eq!(
            readiness.reason,
            SymbolicExecutionCapabilityRouteReadinessReason::AYAuthoritativeCapabilityRoute
        );
        assert_eq!(
            readiness.selected_solver,
            AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER
        );
        assert_eq!(
            readiness.selected_solver_crate,
            AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE
        );
        assert_eq!(
            readiness.selected_solver_path_kind,
            AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND
        );
        assert_eq!(
            readiness.selected_solver_path,
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
        );
        assert!(readiness.supported);
        assert_eq!(readiness.unsupported_reason, "none");
        assert!(readiness.accepted_for_consumer);
        assert!(readiness.fail_closed);
        assert_eq!(
            readiness.required_contract_revision,
            AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION
        );
        assert_eq!(
            readiness.current_ay_revision_kind,
            AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND
        );
        assert_ne!(readiness.current_ay_revision, "unknown");
        assert_eq!(
            readiness.route_admission_schema,
            AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA
        );
        assert_eq!(
            readiness.contract_schema,
            AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            readiness.contract_helper,
            "ay_dpll::api::model_blocking_symbolic_execution_contract"
        );
        assert!(readiness
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"));
        assert!(readiness
            .consumer_responsibilities
            .contains(&AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE));

        let json =
            symbolic_execution_capability_route_readiness_json(SolverCapabilityCode::ModelBlocking);
        assert_eq!(
            json["schema"],
            AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA
        );
        assert_eq!(json["status"], "ready");
        assert_eq!(json["reason"], "ay_authoritative_capability_route");
        assert_eq!(
            json["selected_solver"],
            AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER
        );
        assert_eq!(
            json["selected_solver_path"],
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
        );
        assert_eq!(json["supported"], true);
        assert_eq!(json["unsupported_reason"], "none");
        assert_eq!(
            json["required_contract_revision"],
            AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION
        );
        assert_eq!(
            json["current_ay_revision_kind"],
            AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND
        );

        let rows = symbolic_execution_capability_route_readiness_key_value_rows(
            SolverCapabilityCode::ModelBlocking,
        );
        assert_eq!(rows, readiness.to_key_value_rows());
        assert!(rows.contains(&("status".to_string(), "ready".to_string())));
        assert!(rows.contains(&(
            "contract_helper".to_string(),
            "ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
        )));
        assert!(rows.contains(&(
            "selected_solver_path".to_string(),
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer".to_string()
        )));
        assert!(rows.contains(&("supported".to_string(), "true".to_string())));
        assert!(rows.contains(&(
            "required_contract_revision".to_string(),
            AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION.to_string()
        )));

        let lines = symbolic_execution_capability_route_readiness_text_lines(
            SolverCapabilityCode::ModelBlocking,
        );
        assert_eq!(lines, readiness.to_text_lines());
        assert!(lines.contains(&"reason=ay_authoritative_capability_route".to_string()));
        assert!(lines.contains(
            &"selected_solver_path=ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
                .to_string()
        ));

        assert!(
            validate_symbolic_execution_capability_route_readiness(&readiness)
                .accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_capability_route_readiness_key_value_rows(
                SolverCapabilityCode::ModelBlocking,
                &rows
            )
            .accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_capability_route_readiness_text_lines(
                SolverCapabilityCode::ModelBlocking,
                &lines
            )
            .accepted_for_consumer
        );
        assert!(AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS
            .contains(&"ay_dpll::api::symbolic_execution_capability_route_readiness"));
        assert!(AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_capability_route_readiness_key_value_rows"
        ));
    }

    #[test]
    fn symbolic_execution_capability_route_readiness_blocks_route_rejection() {
        let mut summary = symbolic_execution_contract_manifest_diagnostic_summary();
        summary.fail_closed = false;
        let route_admission = symbolic_execution_route_admission_decision_for_summary(&summary);

        let readiness = symbolic_execution_capability_route_readiness_for_decision(
            SolverCapabilityCode::ModelBlocking,
            &route_admission,
        );

        assert_eq!(
            readiness.status,
            SymbolicExecutionCapabilityRouteReadinessStatus::Blocked
        );
        assert_eq!(
            readiness.reason,
            SymbolicExecutionCapabilityRouteReadinessReason::RouteAdmissionBlocked
        );
        assert!(!readiness.supported);
        assert_eq!(readiness.unsupported_reason, "route_admission_blocked");
        assert!(!readiness.accepted_for_consumer);
        assert!(readiness.fail_closed);
        assert_eq!(readiness.issue_field, "route_admission_status");
    }

    #[test]
    fn symbolic_execution_capability_route_readiness_blocks_unknown_capability() {
        let readiness = symbolic_execution_capability_route_readiness(
            SolverCapabilityCode::FiniteDomainEnumeration,
        );

        assert_eq!(
            readiness.status,
            SymbolicExecutionCapabilityRouteReadinessStatus::Blocked
        );
        assert_eq!(
            readiness.reason,
            SymbolicExecutionCapabilityRouteReadinessReason::UnknownCapability
        );
        assert!(!readiness.supported);
        assert_eq!(readiness.unsupported_reason, "unknown_capability");
        assert_eq!(readiness.selected_solver_path, "none");
        assert!(!readiness.accepted_for_consumer);
        assert!(readiness.fail_closed);
        assert_eq!(readiness.issue_field, "capability");
        assert_eq!(
            readiness.issue_actual.as_deref(),
            Some("finite_domain_enumeration")
        );
    }

    #[test]
    fn symbolic_execution_capability_route_readiness_validator_blocks_bad_rows() {
        let mut rows = symbolic_execution_capability_route_readiness_key_value_rows(
            SolverCapabilityCode::ModelBlocking,
        );
        for (key, value) in &mut rows {
            if key == "contract_helper" {
                *value = "tla_check::local_model_blocking_route".to_string();
            }
        }

        let readiness = validate_symbolic_execution_capability_route_readiness_key_value_rows(
            SolverCapabilityCode::ModelBlocking,
            &rows,
        );

        assert_eq!(
            readiness.status,
            SymbolicExecutionCapabilityRouteReadinessStatus::Blocked
        );
        assert_eq!(
            readiness.reason,
            SymbolicExecutionCapabilityRouteReadinessReason::StaleReadinessRow
        );
        assert!(!readiness.accepted_for_consumer);
        assert!(readiness.fail_closed);
        assert_eq!(readiness.issue_field, "contract_helper");

        let mut missing_rows = symbolic_execution_capability_route_readiness_key_value_rows(
            SolverCapabilityCode::ModelBlocking,
        );
        missing_rows.retain(|(key, _)| key != "key_value_helper");
        let missing = validate_symbolic_execution_capability_route_readiness_key_value_rows(
            SolverCapabilityCode::ModelBlocking,
            &missing_rows,
        );
        assert_eq!(
            missing.reason,
            SymbolicExecutionCapabilityRouteReadinessReason::MissingReadinessRow
        );
        assert_eq!(missing.issue_field, "key_value_helper");

        let mut lines = symbolic_execution_capability_route_readiness_text_lines(
            SolverCapabilityCode::ModelBlocking,
        );
        lines.push("malformed-readiness-line".to_string());
        let malformed = validate_symbolic_execution_capability_route_readiness_text_lines(
            SolverCapabilityCode::ModelBlocking,
            &lines,
        );
        assert_eq!(
            malformed.reason,
            SymbolicExecutionCapabilityRouteReadinessReason::MalformedReadinessRow
        );
        assert_eq!(malformed.issue_field, "readiness_line");
    }

    #[test]
    fn symbolic_execution_all_supported_capability_route_readiness_covers_routes() {
        let readiness = symbolic_execution_all_supported_capability_route_readiness();

        assert_eq!(readiness.len(), AY_SYMBOLIC_EXECUTION_CONTRACTS.len());
        assert_eq!(
            readiness
                .iter()
                .map(|readiness| readiness.capability_code)
                .collect::<Vec<_>>(),
            AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        );
        assert!(readiness
            .iter()
            .all(|readiness| readiness.status
                == SymbolicExecutionCapabilityRouteReadinessStatus::Ready));
        assert!(readiness
            .iter()
            .all(|readiness| readiness.accepted_for_consumer));
        assert!(readiness.iter().all(|readiness| readiness.supported));
        assert!(readiness
            .iter()
            .all(|readiness| readiness.selected_solver
                == AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER));
        assert!(readiness.iter().all(|readiness| {
            readiness.current_ay_revision_kind == AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND
                && readiness.current_ay_revision != "unknown"
        }));
        assert!(readiness.iter().all(|readiness| readiness.fail_closed));

        let json = symbolic_execution_all_supported_capability_route_readiness_json();
        assert_eq!(
            json.as_array().expect("readiness JSON array").len(),
            AY_SYMBOLIC_EXECUTION_CONTRACTS.len()
        );
        assert_eq!(json[0]["status"], "ready");

        let rows = symbolic_execution_all_supported_capability_route_readiness_key_value_rows();
        assert!(rows.contains(&("model_blocking_status".to_string(), "ready".to_string())));
        assert!(rows.contains(&(
            "incremental_assumptions_status".to_string(),
            "ready".to_string()
        )));
        assert!(rows.contains(&(
            "all_sat_enumeration_contract_helper".to_string(),
            "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract".to_string()
        )));
        assert!(rows.contains(&(
            "model_blocking_selected_solver_path".to_string(),
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer".to_string()
        )));
        assert!(rows.contains(&(
            "incremental_assumptions_selected_solver_path".to_string(),
            "ay_dpll::api::Solver::try_check_sat_assuming_with_details".to_string()
        )));
        assert!(rows.contains(&(
            "all_sat_enumeration_selected_solver_path".to_string(),
            "ay_allsat::AllSatSolver::enumerate_with_config".to_string()
        )));

        let lines = symbolic_execution_all_supported_capability_route_readiness_text_lines();
        assert!(
            lines.contains(&"model_blocking_reason=ay_authoritative_capability_route".to_string())
        );
        assert!(lines.contains(&"all_sat_enumeration_fail_closed=true".to_string()));
        assert!(lines.contains(&format!(
            "model_blocking_required_contract_revision={AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION}"
        )));

        assert!(
            validate_symbolic_execution_all_supported_capability_route_readiness(&readiness)
                .iter()
                .all(|readiness| readiness.accepted_for_consumer)
        );
        assert!(
            validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
                &rows
            )
            .iter()
            .all(|readiness| readiness.accepted_for_consumer)
        );
        assert!(
            validate_symbolic_execution_all_supported_capability_route_readiness_text_lines(&lines)
                .iter()
                .all(|readiness| readiness.accepted_for_consumer)
        );
        assert!(
            AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS.contains(
                &"ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness"
            )
        );
        assert!(AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows"
        ));
    }

    #[test]
    fn symbolic_execution_all_supported_capability_route_readiness_validator_blocks_bad_rows() {
        let mut rows = symbolic_execution_all_supported_capability_route_readiness_key_value_rows();
        for (key, value) in &mut rows {
            if key == "model_blocking_contract_helper" {
                *value = "tla_check::local_symbolic_route".to_string();
            }
        }

        let blocked =
            validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
                &rows,
            );
        assert!(blocked.iter().all(|readiness| readiness.status
            == SymbolicExecutionCapabilityRouteReadinessStatus::Blocked));
        assert!(blocked.iter().all(|readiness| readiness.reason
            == SymbolicExecutionCapabilityRouteReadinessReason::StaleReadinessRow));
        assert!(blocked.iter().all(|readiness| readiness.fail_closed));
        assert!(blocked
            .iter()
            .all(|readiness| !readiness.accepted_for_consumer));
        assert!(blocked
            .iter()
            .all(|readiness| readiness.issue_field == "model_blocking_contract_helper"));

        let mut missing_rows =
            symbolic_execution_all_supported_capability_route_readiness_key_value_rows();
        missing_rows.retain(|(key, _)| key != "all_sat_enumeration_key_value_helper");
        let missing =
            validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
                &missing_rows,
            );
        assert!(missing.iter().all(|readiness| {
            readiness.reason == SymbolicExecutionCapabilityRouteReadinessReason::MissingReadinessRow
        }));
        assert!(missing
            .iter()
            .all(|readiness| readiness.issue_field == "all_sat_enumeration_key_value_helper"));

        let mut lines = symbolic_execution_all_supported_capability_route_readiness_text_lines();
        lines.push("malformed-all-readiness-line".to_string());
        let malformed =
            validate_symbolic_execution_all_supported_capability_route_readiness_text_lines(&lines);
        assert!(malformed.iter().all(|readiness| {
            readiness.reason
                == SymbolicExecutionCapabilityRouteReadinessReason::MalformedReadinessRow
        }));
        assert!(malformed
            .iter()
            .all(|readiness| readiness.issue_field == "all_readiness_line"));
    }

    #[test]
    fn symbolic_execution_downstream_contract_bundle_covers_routing_surfaces() {
        let bundle = symbolic_execution_downstream_contract_bundle();

        assert_eq!(
            bundle.schema,
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA
        );
        assert_eq!(
            bundle.schema_version,
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA_VERSION
        );
        assert_eq!(
            bundle.status,
            SymbolicExecutionDownstreamContractBundleStatus::Accepted
        );
        assert_eq!(
            bundle.reason,
            SymbolicExecutionDownstreamContractBundleReason::AYAuthoritativeDownstreamContractBundle
        );
        assert!(bundle.accepted_for_consumer);
        assert!(bundle.fail_closed);
        assert_eq!(
            bundle.solver_capability_descriptor.schema,
            AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA
        );
        assert_eq!(
            bundle.route_admission_decision.schema,
            AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA
        );
        assert_eq!(
            bundle.all_supported_capability_route_readiness.len(),
            AY_SYMBOLIC_EXECUTION_CONTRACTS.len()
        );
        assert_eq!(
            bundle.readiness_capabilities(),
            AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        );
        assert!(bundle
            .all_supported_capability_route_readiness
            .iter()
            .all(|readiness| readiness.accepted_for_consumer && readiness.fail_closed));

        let json = symbolic_execution_downstream_contract_bundle_json();
        assert_eq!(
            json["schema"],
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA
        );
        assert_eq!(json["status"], "accepted");
        assert_eq!(
            json["solver_capability_descriptor"]["schema"],
            AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA
        );
        assert_eq!(json["route_admission_decision"]["status"], "accepted");
        assert_eq!(
            json["all_supported_capability_route_readiness"]
                .as_array()
                .expect("readiness array")
                .len(),
            AY_SYMBOLIC_EXECUTION_CONTRACTS.len()
        );

        let rows = symbolic_execution_downstream_contract_bundle_key_value_rows();
        assert_eq!(rows, bundle.to_key_value_rows());
        assert!(rows.contains(&("status".to_string(), "accepted".to_string())));
        assert!(rows.contains(&(
            "validation_row_groups".to_string(),
            "solver_capability_descriptor,contract_diagnostic_summary,route_admission_decision,all_supported_capability_route_readiness"
                .to_string()
        )));
        assert!(rows.contains(&(
            "descriptor_schema".to_string(),
            AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA.to_string()
        )));
        assert!(rows.contains(&(
            "route_status".to_string(),
            SymbolicExecutionRouteAdmissionStatus::Accepted
                .code()
                .to_string()
        )));
        assert!(rows.contains(&(
            "readiness_model_blocking_selected_solver_path".to_string(),
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer".to_string()
        )));
        assert!(rows.contains(&(
            "validator_names".to_string(),
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATORS.join(",")
        )));

        let lines = symbolic_execution_downstream_contract_bundle_text_lines();
        assert_eq!(lines, bundle.to_text_lines());
        assert!(lines.contains(&"reason=ay_authoritative_downstream_contract_bundle".to_string()));
        assert!(lines.contains(&"readiness_model_blocking_fail_closed=true".to_string()));

        assert!(
            validate_symbolic_execution_downstream_contract_bundle(&bundle).accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_downstream_contract_bundle_key_value_rows(&rows)
                .accepted_for_consumer
        );
        assert!(
            validate_symbolic_execution_downstream_contract_bundle_text_lines(&lines)
                .accepted_for_consumer
        );
    }

    #[test]
    fn symbolic_execution_downstream_contract_bundle_validator_blocks_bad_rows() {
        let mut rows = symbolic_execution_downstream_contract_bundle_key_value_rows();
        for (key, value) in &mut rows {
            if key == "readiness_model_blocking_selected_solver_path" {
                *value = "tla_check::local_symbolic_route".to_string();
            }
        }
        let blocked = validate_symbolic_execution_downstream_contract_bundle_key_value_rows(&rows);
        assert_eq!(
            blocked.status,
            SymbolicExecutionDownstreamContractBundleStatus::Blocked
        );
        assert_eq!(
            blocked.reason,
            SymbolicExecutionDownstreamContractBundleReason::CapabilityRouteReadinessRejected
        );
        assert!(!blocked.accepted_for_consumer);
        assert!(blocked.fail_closed);
        assert_eq!(
            blocked.issue_field,
            "readiness_model_blocking_selected_solver_path"
        );

        let mut missing_rows = symbolic_execution_downstream_contract_bundle_key_value_rows();
        missing_rows.retain(|(key, _)| key != "route_status");
        let missing =
            validate_symbolic_execution_downstream_contract_bundle_key_value_rows(&missing_rows);
        assert_eq!(
            missing.reason,
            SymbolicExecutionDownstreamContractBundleReason::MissingBundleRow
        );
        assert_eq!(missing.issue_field, "route_status");

        let mut fail_open_rows = symbolic_execution_downstream_contract_bundle_key_value_rows();
        for (key, value) in &mut fail_open_rows {
            if key == "readiness_model_blocking_fail_closed" {
                *value = "false".to_string();
            }
        }
        let fail_open =
            validate_symbolic_execution_downstream_contract_bundle_key_value_rows(&fail_open_rows);
        assert_eq!(
            fail_open.reason,
            SymbolicExecutionDownstreamContractBundleReason::NotFailClosed
        );
        assert_eq!(
            fail_open.issue_field,
            "readiness_model_blocking_fail_closed"
        );

        let mut lines = symbolic_execution_downstream_contract_bundle_text_lines();
        lines.push("malformed-downstream-bundle-line".to_string());
        let malformed = validate_symbolic_execution_downstream_contract_bundle_text_lines(&lines);
        assert_eq!(
            malformed.reason,
            SymbolicExecutionDownstreamContractBundleReason::MalformedBundleRow
        );
        assert_eq!(malformed.issue_field, "bundle_line");
    }

    #[test]
    fn symbolic_execution_route_admission_blocks_unknown_capability_rows() {
        let mut rows = symbolic_execution_route_admission_decision_key_value_rows();
        for (key, value) in &mut rows {
            if key == "route_capabilities" {
                value.push_str(",experimental_local_route");
            }
        }

        let decision = validate_symbolic_execution_route_admission_decision_key_value_rows(&rows);

        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Blocked
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::UnknownCapability
        );
        assert!(!decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(decision.issue_field, "route_capabilities");
        assert_eq!(
            decision.issue_actual.as_deref(),
            Some("experimental_local_route")
        );
    }

    #[test]
    fn symbolic_execution_route_admission_blocks_unknown_route_rows() {
        let mut rows = symbolic_execution_route_admission_decision_key_value_rows();
        rows.push((
            "local_solver_route_authority".to_string(),
            "model-checker-local".to_string(),
        ));

        let decision = validate_symbolic_execution_route_admission_decision_key_value_rows(&rows);

        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Blocked
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::UnknownRouteRow
        );
        assert_eq!(decision.reason_code, "unknown_route_row");
        assert!(!decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(decision.issue_field, "route_key_value_pair");
        assert_eq!(
            decision.issue_expected.as_deref(),
            Some("ay_symbolic_execution_route_admission_row")
        );
        assert_eq!(
            decision.issue_actual.as_deref(),
            Some("local_solver_route_authority")
        );
    }

    #[test]
    fn symbolic_execution_route_admission_blocks_missing_rows() {
        let mut rows = symbolic_execution_route_admission_decision_key_value_rows();
        rows.retain(|(key, _)| key != "all_sat_enumeration_route_contract_helper");

        let decision = validate_symbolic_execution_route_admission_decision_key_value_rows(&rows);

        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Blocked
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::MissingRouteRow
        );
        assert!(!decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(
            decision.issue_field,
            "all_sat_enumeration_route_contract_helper"
        );
    }

    #[test]
    fn symbolic_execution_route_admission_blocks_stale_rows() {
        let mut rows = symbolic_execution_route_admission_decision_key_value_rows();
        for (key, value) in &mut rows {
            if key == "model_blocking_route_contract_helper" {
                *value = "local::weaker_model_blocking".to_string();
            }
        }

        let decision = validate_symbolic_execution_route_admission_decision_key_value_rows(&rows);

        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Blocked
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::StaleRouteRow
        );
        assert!(!decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(decision.issue_field, "model_blocking_route_contract_helper");
        assert_eq!(
            decision.issue_actual.as_deref(),
            Some("local::weaker_model_blocking")
        );
    }

    #[test]
    fn symbolic_execution_route_admission_blocks_fail_open_rows() {
        let mut rows = symbolic_execution_route_admission_decision_key_value_rows();
        for (key, value) in &mut rows {
            if key == "model_blocking_route_fail_closed" {
                *value = "false".to_string();
            }
        }

        let decision = validate_symbolic_execution_route_admission_decision_key_value_rows(&rows);

        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Blocked
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::NotFailClosed
        );
        assert!(!decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(decision.issue_field, "model_blocking_route_fail_closed");
    }

    #[test]
    fn symbolic_execution_route_admission_blocks_malformed_text_lines() {
        let mut lines = symbolic_execution_route_admission_decision_text_lines();
        lines.push("malformed-route-line".to_string());

        let decision = validate_symbolic_execution_route_admission_decision_text_lines(&lines);

        assert_eq!(
            decision.status,
            SymbolicExecutionRouteAdmissionStatus::Blocked
        );
        assert_eq!(
            decision.reason,
            SymbolicExecutionRouteAdmissionReason::MalformedRouteRow
        );
        assert!(!decision.accepted_for_consumer);
        assert!(decision.fail_closed);
        assert_eq!(decision.issue_field, "route_admission_line");
        assert_eq!(
            decision.issue_actual.as_deref(),
            Some("malformed-route-line")
        );
    }

    #[test]
    fn symbolic_execution_contract_manifest_health_report_rejects_missing_contract() {
        let incomplete_contracts: &'static [SymbolicExecutionContractManifestEntry] = Box::leak(
            vec![
                AY_SYMBOLIC_EXECUTION_CONTRACTS[0],
                AY_SYMBOLIC_EXECUTION_CONTRACTS[1],
            ]
            .into_boxed_slice(),
        );
        let incomplete_manifest = SymbolicExecutionContractManifest {
            schema: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
            schema_version: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION,
            solver: "ay",
            contracts: incomplete_contracts,
            all_contracts_fail_closed: true,
        };

        let report = validate_symbolic_execution_contract_manifest(&incomplete_manifest);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(report.status_code, "incomplete");
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::MissingRequiredContract
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::Incomplete
        );
        assert_eq!(report.reason_code, "missing_required_contract");
        assert!(!report.accepted_for_consumer);
        assert!(!report.all_contracts_fail_closed);
        assert!(report.present_capabilities.contains(&"model_blocking"));
        assert!(report
            .present_capabilities
            .contains(&"incremental_assumptions"));
        assert!(!report.present_capabilities.contains(&"all_sat_enumeration"));
        assert!(report.issues.iter().any(|issue| {
            issue.capability_code == Some("all_sat_enumeration")
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::MissingRequiredContract
        }));
    }

    #[test]
    fn symbolic_execution_contract_manifest_health_report_rejects_unclosed_extra_contract() {
        let mut extra_entry = AY_SYMBOLIC_EXECUTION_CONTRACTS[0];
        extra_entry.capability_code = "experimental_unclosed_contract";
        extra_entry.capability_name = "Experimental unclosed contract";
        extra_entry.fail_closed = false;
        let contracts: &'static [SymbolicExecutionContractManifestEntry] = Box::leak(
            vec![
                AY_SYMBOLIC_EXECUTION_CONTRACTS[0],
                AY_SYMBOLIC_EXECUTION_CONTRACTS[1],
                AY_SYMBOLIC_EXECUTION_CONTRACTS[2],
                extra_entry,
            ]
            .into_boxed_slice(),
        );
        let manifest = SymbolicExecutionContractManifest {
            schema: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
            schema_version: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION,
            solver: "ay",
            contracts,
            all_contracts_fail_closed: true,
        };

        let report = validate_symbolic_execution_contract_manifest(&manifest);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::NotFailClosed
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::FailClosedViolation
        );
        assert!(!report.accepted_for_consumer);
        assert!(!report.all_contracts_fail_closed);
        assert!(report.issues.iter().any(|issue| {
            issue.capability_code == Some("experimental_unclosed_contract")
                && issue.field == "fail_closed"
                && issue.reason == SymbolicExecutionContractManifestHealthReason::NotFailClosed
        }));
    }

    #[test]
    fn symbolic_execution_contract_key_value_health_report_rejects_missing_helper() {
        let mut pairs = symbolic_execution_contract_manifest_key_value_pairs();
        pairs.retain(|(key, _)| *key != "all_sat_enumeration_contract_helper");

        let report = validate_symbolic_execution_contract_manifest_key_value_pairs(&pairs);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::MissingKeyValuePair
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::Incomplete
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.all_contracts_fail_closed);
        assert!(report.issues.iter().any(|issue| {
            issue.capability_code == Some("all_sat_enumeration")
                && issue.field == "all_sat_enumeration_contract_helper"
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::MissingKeyValuePair
        }));
    }

    #[test]
    fn symbolic_execution_contract_key_value_health_report_rejects_missing_capability_row() {
        let mut pairs = symbolic_execution_contract_manifest_key_value_pairs();
        for (key, value) in &mut pairs {
            if *key == "contract_capabilities" {
                *value = "model_blocking,incremental_assumptions".to_string();
            }
        }

        let report = validate_symbolic_execution_contract_manifest_key_value_pairs(&pairs);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::MissingRequiredContract
        );
        assert!(!report.accepted_for_consumer);
        assert!(!report.all_contracts_fail_closed);
        assert!(!report.present_capabilities.contains(&"all_sat_enumeration"));
        assert!(report
            .issues
            .iter()
            .any(|issue| issue.field == "contract_capabilities"
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::MissingRequiredContract));
    }

    #[test]
    fn symbolic_execution_contract_key_value_health_report_rejects_duplicate_rows() {
        let mut pairs = symbolic_execution_contract_manifest_key_value_pairs();
        pairs.push((
            "schema",
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA.to_string(),
        ));

        let report = validate_symbolic_execution_contract_manifest_key_value_pairs(&pairs);

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::DuplicateKeyValuePair
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.all_contracts_fail_closed);
        assert!(report.issues.iter().any(|issue| {
            issue.field == "key_value_pair"
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::DuplicateKeyValuePair
                && issue.actual.as_deref() == Some("schema:2")
        }));
        let diagnostic_rows = report.to_diagnostic_key_value_rows();
        assert!(diagnostic_rows
            .contains(&("diagnostic".to_string(), "stale_or_mismatched".to_string())));
        assert!(diagnostic_rows.contains(&(
            "issue_0_reason".to_string(),
            "duplicate_key_value_pair".to_string()
        )));
        assert!(report
            .to_diagnostic_lines()
            .contains(&"issue_0_actual=schema:2".to_string()));
    }

    #[test]
    fn symbolic_execution_contract_round_trip_rejects_mismatched_rows() {
        let mut pairs = symbolic_execution_contract_manifest_key_value_pairs();
        for (key, value) in &mut pairs {
            if *key == "model_blocking_contract_schema_version" {
                *value = "0".to_string();
            }
        }

        let report = validate_symbolic_execution_contract_manifest_round_trip(
            &symbolic_execution_contract_manifest(),
            &pairs,
        );

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::ContractVersionMismatch
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.all_contracts_fail_closed);
        assert!(report.issues.iter().any(|issue| {
            issue.capability_code == Some("model_blocking")
                && issue.field == "model_blocking_contract_schema_version"
                && issue.reason
                    == SymbolicExecutionContractManifestHealthReason::ContractVersionMismatch
                && issue.expected.as_deref() == Some("1")
                && issue.actual.as_deref() == Some("0")
        }));
    }

    #[test]
    fn symbolic_execution_contract_round_trip_rejects_duplicate_contracts() {
        let duplicate_contracts: &'static [SymbolicExecutionContractManifestEntry] = Box::leak(
            vec![
                AY_SYMBOLIC_EXECUTION_CONTRACTS[0],
                AY_SYMBOLIC_EXECUTION_CONTRACTS[0],
                AY_SYMBOLIC_EXECUTION_CONTRACTS[1],
                AY_SYMBOLIC_EXECUTION_CONTRACTS[2],
            ]
            .into_boxed_slice(),
        );
        let duplicate_manifest = SymbolicExecutionContractManifest {
            schema: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
            schema_version: AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION,
            solver: "ay",
            contracts: duplicate_contracts,
            all_contracts_fail_closed: true,
        };

        let report = validate_symbolic_execution_contract_manifest_round_trip(
            &duplicate_manifest,
            &symbolic_execution_contract_manifest_key_value_pairs(),
        );

        assert_eq!(
            report.status,
            SymbolicExecutionContractManifestHealthStatus::Incomplete
        );
        assert_eq!(
            report.reason,
            SymbolicExecutionContractManifestHealthReason::DuplicateContract
        );
        assert_eq!(
            report.diagnostic(),
            SymbolicExecutionContractManifestHealthDiagnostic::StaleOrMismatched
        );
        assert!(!report.accepted_for_consumer);
        assert!(report.all_contracts_fail_closed);
        assert!(report.issues.iter().any(|issue| {
            issue.capability_code == Some("model_blocking")
                && issue.field == "contract"
                && issue.reason == SymbolicExecutionContractManifestHealthReason::DuplicateContract
                && issue.actual.as_deref() == Some("model_blocking:2")
        }));
    }
}
