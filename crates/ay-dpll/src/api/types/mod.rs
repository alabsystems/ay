// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the AY Solver API.
//!
//! This module re-exports all public API types from focused submodules.
//! The public surface is source-compatible with the former single-file layout.

pub(crate) mod annotated_core;
mod capabilities;
mod cross_check;
mod error;
mod explanation;
mod handles;
mod incremental;
mod interpolant;
mod logic;
pub(crate) mod maxsmt;
mod model;
mod model_blocking;
mod model_provenance;
mod model_value;
mod model_value_display;
mod native_replay;
mod objective;
mod results;
mod verification;

// Re-export all public types to preserve the existing `types::*` surface.
pub use annotated_core::{
    AnnotatedCoreLiteral, AnnotatedUnsatCore, CongruenceReason, CongruenceStep,
    InstantiationMethod, TheoryAttribution,
};
pub use capabilities::{
    all_sat_enumeration_symbolic_execution_contract,
    all_sat_enumeration_symbolic_execution_contract_key_value_pairs,
    incremental_assumptions_symbolic_execution_contract,
    incremental_assumptions_symbolic_execution_contract_key_value_pairs,
    model_blocking_symbolic_execution_contract,
    model_blocking_symbolic_execution_contract_key_value_pairs, solver_capability_descriptor,
    solver_capability_descriptor_json, solver_capability_descriptor_key_value_pairs,
    solver_capability_descriptor_manifest,
    symbolic_execution_all_supported_capability_route_readiness,
    symbolic_execution_all_supported_capability_route_readiness_for_decision,
    symbolic_execution_all_supported_capability_route_readiness_json,
    symbolic_execution_all_supported_capability_route_readiness_key_value_rows,
    symbolic_execution_all_supported_capability_route_readiness_text_lines,
    symbolic_execution_capability_route_readiness,
    symbolic_execution_capability_route_readiness_for_decision,
    symbolic_execution_capability_route_readiness_json,
    symbolic_execution_capability_route_readiness_key_value_rows,
    symbolic_execution_capability_route_readiness_text_lines, symbolic_execution_contract_manifest,
    symbolic_execution_contract_manifest_diagnostic_summary,
    symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip,
    symbolic_execution_contract_manifest_diagnostic_summary_json,
    symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows,
    symbolic_execution_contract_manifest_diagnostic_summary_text_lines,
    symbolic_execution_contract_manifest_health_diagnostic_lines,
    symbolic_execution_contract_manifest_health_key_value_rows,
    symbolic_execution_contract_manifest_health_report, symbolic_execution_contract_manifest_json,
    symbolic_execution_contract_manifest_key_value_pairs,
    symbolic_execution_contract_manifest_round_trip_health_report,
    symbolic_execution_downstream_contract_bundle,
    symbolic_execution_downstream_contract_bundle_json,
    symbolic_execution_downstream_contract_bundle_key_value_rows,
    symbolic_execution_downstream_contract_bundle_text_lines,
    symbolic_execution_route_admission_decision,
    symbolic_execution_route_admission_decision_for_summary,
    symbolic_execution_route_admission_decision_json,
    symbolic_execution_route_admission_decision_key_value_rows,
    symbolic_execution_route_admission_decision_text_lines,
    validate_symbolic_execution_all_supported_capability_route_readiness,
    validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows,
    validate_symbolic_execution_all_supported_capability_route_readiness_text_lines,
    validate_symbolic_execution_capability_route_readiness,
    validate_symbolic_execution_capability_route_readiness_key_value_rows,
    validate_symbolic_execution_capability_route_readiness_text_lines,
    validate_symbolic_execution_contract_manifest,
    validate_symbolic_execution_contract_manifest_diagnostic_summary,
    validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows,
    validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines,
    validate_symbolic_execution_contract_manifest_key_value_pairs,
    validate_symbolic_execution_contract_manifest_round_trip,
    validate_symbolic_execution_downstream_contract_bundle,
    validate_symbolic_execution_downstream_contract_bundle_key_value_rows,
    validate_symbolic_execution_downstream_contract_bundle_text_lines,
    validate_symbolic_execution_route_admission_decision,
    validate_symbolic_execution_route_admission_decision_key_value_rows,
    validate_symbolic_execution_route_admission_decision_text_lines, SolverCapability,
    SolverCapabilityCode, SolverCapabilityContract, SolverCapabilityDescriptor,
    SolverCapabilityDescriptorManifest, SolverCapabilityReason, SolverCapabilityStatus,
    SymbolicExecutionCapabilityRouteReadiness, SymbolicExecutionCapabilityRouteReadinessReason,
    SymbolicExecutionCapabilityRouteReadinessStatus, SymbolicExecutionContractManifest,
    SymbolicExecutionContractManifestDiagnosticSummary, SymbolicExecutionContractManifestEntry,
    SymbolicExecutionContractManifestHealthDiagnostic,
    SymbolicExecutionContractManifestHealthIssue, SymbolicExecutionContractManifestHealthReason,
    SymbolicExecutionContractManifestHealthReport, SymbolicExecutionContractManifestHealthStatus,
    SymbolicExecutionDownstreamContractBundle, SymbolicExecutionDownstreamContractBundleReason,
    SymbolicExecutionDownstreamContractBundleStatus, SymbolicExecutionRouteAdmissionDecision,
    SymbolicExecutionRouteAdmissionReason, SymbolicExecutionRouteAdmissionStatus,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CAP_BOUND,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_PROJECTION_SCOPE,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ACCEPT_MODEL_BOUNDARY,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_BOOLEAN_ASSUMPTIONS,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_UNSAT_CORE_ON_UNSAT,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_NON_EMPTY_PROJECTION,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES, AY_SOLVER_CAPABILITIES,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS, AY_SYMBOLIC_EXECUTION_CONTRACTS,
    AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS,
    AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES,
    AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_HELPERS,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATION_ROW_GROUPS,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATORS,
    AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_HELPERS, AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA,
    AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS,
    AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND,
    AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION,
    AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER, AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE,
    AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND,
};
pub use cross_check::{CrossCheckDisagreement, CrossCheckReport, CrossCheckRun, CrossCheckVariant};
pub use error::SolverError;
pub use explanation::{
    CoreConstraintExplanation, ExplanationKind, ExplanationReport, ModelAssignmentExplanation,
    SatExplanation, UnknownExplanation, UnsatCoreSource, UnsatExplanation,
};
pub use handles::{FuncDecl, Term};
pub use incremental::{CoreEvolutionTracker, IncrementalCoreEvolution};
pub use interpolant::{InterpolantResult, InterpolantStrength, PathInterpolantResult};
pub use logic::{split_leading_set_logic, Logic, SortExt};
pub use maxsmt::{MaxSmtResult, MaxSmtStatus};
pub use model::{Model, VerifiedModel};
pub use model_blocking::{
    ModelBlockingAssignment, ModelBlockingClause, ModelBlockingClauseEvidence,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION, AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION,
};
pub use model_provenance::{AssignmentReason, ModelProvenance, VariableProvenance};
pub use model_value::{FpSpecialKind, ModelValue};
pub use native_replay::{
    NativeReplayArtifact, NativeReplayAssertion, NativeReplayCheckedReplaySummary,
    NativeReplayDeclaration, NativeReplayEvent, NativeReplayEventKind,
    NativeReplayEvidenceManifest, NativeReplayFunctionDeclaration, NativeReplayMetadata,
    NativeReplayModelSummary, NativeReplayProofSummary, NativeReplayResourceUsage,
    NativeReplaySolveSummary, NativeReplaySolverIdentity, NativeReplayStatistics,
    NativeReplayTermNode, NativeReplayUnknownProgress, NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA,
    NATIVE_REPLAY_SCHEMA,
};
pub use objective::ObjectiveValue;
pub use results::{ConsumerAcceptanceError, SmtProofCertificate, SolveResult, VerifiedSolveResult};
pub use verification::{
    raw_smt_solve_profile_summary_from_process, raw_smt_solve_profile_summary_from_typed_details,
    raw_smt_solve_profile_summary_from_typed_summary, validate_raw_smt_solve_profile_summary,
    validate_raw_smt_solve_profile_summary_key_value_rows,
    validate_raw_smt_solve_profile_summary_text_lines, AssumptionSolveDetails, LimitKind,
    RawSmtProcessSolveProfileInput, RawSmtSolveProfileReason, RawSmtSolveProfileSource,
    RawSmtSolveProfileStatus, RawSmtSolveProfileSummary, RawSmtSolveProfileValidationIssue,
    RawSmtSolveProfileValidationReason, RawSmtSolveProfileValidationReport,
    RawSmtSolveProfileValidationStatus, ResourceUsage, SolveDecision,
    SolveDecisionProfileModelConsumerDecision, SolveDecisionProfileModelConsumerReason,
    SolveDecisionProfileModelConsumerStatus, SolveDecisionProfileSummary, SolveDetails,
    SolveProfileSummary, SolveUnknownSummary, UnknownDiagnostic, VerificationLevel,
    VerificationSummary, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA, AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION,
};
