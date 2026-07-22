// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compatibility re-export for the stable solver capability descriptor.
//!
//! The descriptor is owned by `ay-dpll` so downstream consumers that only need
//! capability metadata and model-blocking primitives can avoid the broad `ay`
//! facade dependency. Existing `ay::capabilities` and root re-exports remain
//! source-compatible.

pub use ay_dpll::api::{
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn facade_capability_descriptor_matches_dpll_owner() {
        let descriptor = solver_capability_descriptor();

        assert_eq!(descriptor.schema, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA);
        assert_eq!(descriptor.capabilities, AY_SOLVER_CAPABILITIES);
        assert!(descriptor.supports(SolverCapabilityCode::ModelBlocking));
        assert!(descriptor
            .capability(SolverCapabilityCode::ModelBlocking)
            .expect("model-blocking row")
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"));
        assert_eq!(
            solver_capability_descriptor_key_value_pairs()[0],
            (
                "schema",
                AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA.to_string()
            )
        );
        assert_eq!(
            model_blocking_symbolic_execution_contract().schema,
            AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            incremental_assumptions_symbolic_execution_contract().schema,
            AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            all_sat_enumeration_symbolic_execution_contract().schema,
            AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert_eq!(
            symbolic_execution_contract_manifest().schema,
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA
        );
        assert_eq!(
            symbolic_execution_contract_manifest().contracts,
            AY_SYMBOLIC_EXECUTION_CONTRACTS
        );
        assert_eq!(
            symbolic_execution_contract_manifest_health_report().schema,
            AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA
        );
        assert!(symbolic_execution_contract_manifest_health_report().accepted_for_consumer);
        assert_eq!(
            symbolic_execution_capability_route_readiness(SolverCapabilityCode::ModelBlocking)
                .schema,
            AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA
        );
        assert_eq!(
            symbolic_execution_capability_route_readiness(SolverCapabilityCode::ModelBlocking)
                .selected_solver,
            AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER
        );
        assert_eq!(
            symbolic_execution_capability_route_readiness(SolverCapabilityCode::ModelBlocking)
                .selected_solver_path,
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
        );
        assert_eq!(
            symbolic_execution_capability_route_readiness(SolverCapabilityCode::ModelBlocking)
                .required_contract_revision,
            AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION
        );
        assert_ne!(
            symbolic_execution_capability_route_readiness(SolverCapabilityCode::ModelBlocking)
                .current_ay_revision,
            "unknown"
        );
        assert!(
            validate_symbolic_execution_capability_route_readiness_key_value_rows(
                SolverCapabilityCode::ModelBlocking,
                &symbolic_execution_capability_route_readiness_key_value_rows(
                    SolverCapabilityCode::ModelBlocking
                )
            )
            .accepted_for_consumer
        );
        assert_eq!(
            symbolic_execution_all_supported_capability_route_readiness().len(),
            AY_SYMBOLIC_EXECUTION_CONTRACTS.len()
        );
        assert!(
            validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
                &symbolic_execution_all_supported_capability_route_readiness_key_value_rows()
            )
            .iter()
            .all(|readiness| readiness.accepted_for_consumer)
        );
        assert_eq!(
            symbolic_execution_downstream_contract_bundle().schema,
            AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA
        );
        assert!(symbolic_execution_downstream_contract_bundle().accepted_for_consumer);
        assert!(
            symbolic_execution_downstream_contract_bundle_key_value_rows()
                .iter()
                .any(|(key, value)| key == "route_status" && value == "accepted")
        );
        assert!(
            validate_symbolic_execution_downstream_contract_bundle_key_value_rows(
                &symbolic_execution_downstream_contract_bundle_key_value_rows()
            )
            .accepted_for_consumer
        );
    }
}
