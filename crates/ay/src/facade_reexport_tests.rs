// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

#[test]
fn stat_value_accessible_through_root_api_and_prelude() {
    let _: fn() -> Option<crate::StatValue> = || None;
    let _: fn() -> Option<crate::api::StatValue> = || None;
    let _: fn() -> Option<crate::prelude::StatValue> = || None;
}

#[test]
fn solve_decision_profile_model_consumer_surface_reexported() {
    let _: fn() -> Option<crate::SolveDecisionProfileSummary> = || None;
    let _: fn() -> Option<crate::SolveDecisionProfileModelConsumerDecision> = || None;
    let _: fn() -> Option<crate::SolveDecisionProfileModelConsumerStatus> = || None;
    let _: fn() -> Option<crate::SolveDecisionProfileModelConsumerReason> = || None;
    let _: fn() -> Option<crate::api::SolveDecisionProfileModelConsumerDecision> = || None;
    let _: fn() -> Option<crate::prelude::SolveDecisionProfileModelConsumerDecision> = || None;
    let _: fn(
        &crate::SolveDecisionProfileSummary,
    ) -> crate::SolveDecisionProfileModelConsumerDecision =
        crate::SolveDecisionProfileSummary::model_consumer_decision;
    assert_eq!(
        crate::AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
        "ay.solve-decision-profile-model-consumer.v1"
    );
    assert_eq!(
        crate::AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
        1
    );
}

#[test]
fn raw_smt_solve_profile_summary_surface_reexported() {
    let _: fn() -> Option<crate::RawSmtSolveProfileSummary> = || None;
    let _: fn() -> Option<crate::RawSmtProcessSolveProfileInput> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileSource> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileStatus> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileReason> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileValidationReport> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileValidationStatus> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileValidationReason> = || None;
    let _: fn() -> Option<crate::RawSmtSolveProfileValidationIssue> = || None;
    let _: fn() -> Option<crate::api::RawSmtSolveProfileSummary> = || None;
    let _: fn() -> Option<crate::prelude::RawSmtSolveProfileSummary> = || None;
    let _: fn(crate::RawSmtProcessSolveProfileInput) -> crate::RawSmtSolveProfileSummary =
        crate::raw_smt_solve_profile_summary_from_process;
    let _: fn(&crate::RawSmtSolveProfileSummary) -> crate::RawSmtSolveProfileValidationReport =
        crate::validate_raw_smt_solve_profile_summary;
    let _: fn(&[(String, String)]) -> crate::RawSmtSolveProfileValidationReport =
        crate::validate_raw_smt_solve_profile_summary_key_value_rows;
    let _: fn(&[String]) -> crate::RawSmtSolveProfileValidationReport =
        crate::validate_raw_smt_solve_profile_summary_text_lines;

    assert_eq!(
        crate::AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
        "ay.raw-smt-solve-profile-summary.v1"
    );
    assert_eq!(crate::AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION, 1);
    assert!(
        crate::AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS.contains(&"profile_wall_time_ms")
    );

    let summary = crate::raw_smt_solve_profile_summary_from_process(
        crate::RawSmtProcessSolveProfileInput::new("ay", Some("QF_UF"), "sat\n", "", Some(0))
            .with_wall_time_ms(9),
    );
    assert_eq!(summary.source_code, "raw_process_execution");
    assert_eq!(summary.status_code, "available");
    assert_eq!(summary.reason_code, "raw_process_status");
    assert_eq!(summary.to_json_value()["profile"]["wall_time_ms"], 9);
    assert!(crate::api::validate_raw_smt_solve_profile_summary(&summary).accepted());
    assert!(
        crate::prelude::validate_raw_smt_solve_profile_summary_text_lines(&summary.to_text_lines())
            .accepted()
    );
}

#[test]
fn solver_capability_descriptor_surface_reexported() {
    let _: fn() -> Option<crate::SolverCapabilityDescriptor> = || None;
    let _: fn() -> Option<crate::SolverCapabilityDescriptorManifest> = || None;
    let _: fn() -> Option<crate::SolverCapabilityContract> = || None;
    let _: fn() -> Option<crate::SolverCapability> = || None;
    let _: fn() -> Option<crate::SolverCapabilityCode> = || None;
    let _: fn() -> Option<crate::SolverCapabilityStatus> = || None;
    let _: fn() -> Option<crate::SolverCapabilityReason> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifest> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestEntry> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestHealthReport> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestHealthIssue> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestHealthStatus> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestHealthReason> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestHealthDiagnostic> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionContractManifestDiagnosticSummary> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionRouteAdmissionDecision> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionRouteAdmissionStatus> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionRouteAdmissionReason> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionDownstreamContractBundle> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionDownstreamContractBundleStatus> = || None;
    let _: fn() -> Option<crate::SymbolicExecutionDownstreamContractBundleReason> = || None;
    let _: fn() -> Option<crate::ModelBlockingClause> = || None;
    let _: fn() -> Option<crate::ModelBlockingAssignment> = || None;
    let _: fn() -> Option<crate::ModelBlockingClauseEvidence> = || None;
    let _: fn() -> Option<crate::api::SolverCapabilityDescriptor> = || None;
    let _: fn() -> Option<crate::api::SolverCapabilityDescriptorManifest> = || None;
    let _: fn() -> Option<crate::api::SolverCapabilityContract> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionContractManifest> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionContractManifestHealthReport> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionContractManifestDiagnosticSummary> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionRouteAdmissionDecision> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionRouteAdmissionStatus> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionRouteAdmissionReason> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionDownstreamContractBundle> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionDownstreamContractBundleStatus> = || None;
    let _: fn() -> Option<crate::api::SymbolicExecutionDownstreamContractBundleReason> = || None;
    let _: fn() -> Option<crate::api::ModelBlockingClause> = || None;
    let _: fn() -> Option<crate::api::ModelBlockingClauseEvidence> = || None;
    let _: fn() -> Option<crate::prelude::SolverCapabilityDescriptor> = || None;
    let _: fn() -> Option<crate::prelude::SolverCapabilityDescriptorManifest> = || None;
    let _: fn() -> Option<crate::prelude::SolverCapabilityContract> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionContractManifest> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionContractManifestHealthReport> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionContractManifestDiagnosticSummary> =
        || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionRouteAdmissionDecision> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionRouteAdmissionStatus> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionRouteAdmissionReason> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionDownstreamContractBundle> = || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionDownstreamContractBundleStatus> =
        || None;
    let _: fn() -> Option<crate::prelude::SymbolicExecutionDownstreamContractBundleReason> =
        || None;
    let _: fn() -> Option<crate::prelude::ModelBlockingClause> = || None;
    let _: fn() -> Option<crate::prelude::ModelBlockingClauseEvidence> = || None;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::solver_capability_descriptor_key_value_pairs;
    let _: fn() -> crate::SymbolicExecutionContractManifest =
        crate::symbolic_execution_contract_manifest;
    let _: fn() -> crate::api::SymbolicExecutionContractManifest =
        crate::api::symbolic_execution_contract_manifest;
    let _: fn() -> crate::prelude::SymbolicExecutionContractManifest =
        crate::prelude::symbolic_execution_contract_manifest;
    let _: fn() -> serde_json::Value = crate::symbolic_execution_contract_manifest_json;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::symbolic_execution_contract_manifest_key_value_pairs;
    let _: fn() -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::symbolic_execution_contract_manifest_health_report;
    let _: fn() -> crate::api::SymbolicExecutionContractManifestHealthReport =
        crate::api::symbolic_execution_contract_manifest_health_report;
    let _: fn() -> crate::prelude::SymbolicExecutionContractManifestHealthReport =
        crate::prelude::symbolic_execution_contract_manifest_health_report;
    let _: fn(
        &crate::SymbolicExecutionContractManifest,
    ) -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::validate_symbolic_execution_contract_manifest;
    let _: fn(&[(&str, String)]) -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::validate_symbolic_execution_contract_manifest_key_value_pairs;
    let _: fn(
        &crate::SymbolicExecutionContractManifest,
        &[(&str, String)],
    ) -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::validate_symbolic_execution_contract_manifest_round_trip;
    let _: fn() -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::symbolic_execution_contract_manifest_round_trip_health_report;
    let _: fn() -> Vec<(String, String)> =
        crate::symbolic_execution_contract_manifest_health_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::symbolic_execution_contract_manifest_health_diagnostic_lines;
    let _: fn() -> crate::SymbolicExecutionContractManifestDiagnosticSummary =
        crate::symbolic_execution_contract_manifest_diagnostic_summary;
    let _: fn(
        &crate::SymbolicExecutionContractManifest,
        &[(&str, String)],
    ) -> crate::SymbolicExecutionContractManifestDiagnosticSummary =
        crate::symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip;
    let _: fn() -> serde_json::Value =
        crate::symbolic_execution_contract_manifest_diagnostic_summary_json;
    let _: fn() -> Vec<(String, String)> =
        crate::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::symbolic_execution_contract_manifest_diagnostic_summary_text_lines;
    let _: fn(
        &crate::SymbolicExecutionContractManifestDiagnosticSummary,
    ) -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::validate_symbolic_execution_contract_manifest_diagnostic_summary;
    let _: fn(&[(String, String)]) -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows;
    let _: fn(&[String]) -> crate::SymbolicExecutionContractManifestHealthReport =
        crate::validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines;
    let _: fn() -> crate::api::SymbolicExecutionContractManifestDiagnosticSummary =
        crate::api::symbolic_execution_contract_manifest_diagnostic_summary;
    let _: fn() -> crate::prelude::SymbolicExecutionContractManifestDiagnosticSummary =
        crate::prelude::symbolic_execution_contract_manifest_diagnostic_summary;
    let _: fn() -> Vec<(String, String)> =
        crate::prelude::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::prelude::symbolic_execution_contract_manifest_diagnostic_summary_text_lines;
    let _: fn() -> crate::SymbolicExecutionRouteAdmissionDecision =
        crate::symbolic_execution_route_admission_decision;
    let _: fn(
        &crate::SymbolicExecutionContractManifestDiagnosticSummary,
    ) -> crate::SymbolicExecutionRouteAdmissionDecision =
        crate::symbolic_execution_route_admission_decision_for_summary;
    let _: fn() -> serde_json::Value = crate::symbolic_execution_route_admission_decision_json;
    let _: fn() -> Vec<(String, String)> =
        crate::symbolic_execution_route_admission_decision_key_value_rows;
    let _: fn() -> Vec<String> = crate::symbolic_execution_route_admission_decision_text_lines;
    let _: fn(
        &crate::SymbolicExecutionRouteAdmissionDecision,
    ) -> crate::SymbolicExecutionRouteAdmissionDecision =
        crate::validate_symbolic_execution_route_admission_decision;
    let _: fn(&[(String, String)]) -> crate::SymbolicExecutionRouteAdmissionDecision =
        crate::validate_symbolic_execution_route_admission_decision_key_value_rows;
    let _: fn(&[String]) -> crate::SymbolicExecutionRouteAdmissionDecision =
        crate::validate_symbolic_execution_route_admission_decision_text_lines;
    let _: fn() -> crate::api::SymbolicExecutionRouteAdmissionDecision =
        crate::api::symbolic_execution_route_admission_decision;
    let _: fn() -> crate::prelude::SymbolicExecutionRouteAdmissionDecision =
        crate::prelude::symbolic_execution_route_admission_decision;
    let _: fn() -> Vec<(String, String)> =
        crate::prelude::symbolic_execution_route_admission_decision_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::prelude::symbolic_execution_route_admission_decision_text_lines;
    let _: fn(crate::SolverCapabilityCode) -> crate::SymbolicExecutionCapabilityRouteReadiness =
        crate::symbolic_execution_capability_route_readiness;
    let _: fn(
        crate::SolverCapabilityCode,
        &crate::SymbolicExecutionRouteAdmissionDecision,
    ) -> crate::SymbolicExecutionCapabilityRouteReadiness =
        crate::symbolic_execution_capability_route_readiness_for_decision;
    let _: fn(crate::SolverCapabilityCode) -> serde_json::Value =
        crate::symbolic_execution_capability_route_readiness_json;
    let _: fn(crate::SolverCapabilityCode) -> Vec<(String, String)> =
        crate::symbolic_execution_capability_route_readiness_key_value_rows;
    let _: fn(crate::SolverCapabilityCode) -> Vec<String> =
        crate::symbolic_execution_capability_route_readiness_text_lines;
    let _: fn(
        &crate::SymbolicExecutionCapabilityRouteReadiness,
    ) -> crate::SymbolicExecutionCapabilityRouteReadiness =
        crate::validate_symbolic_execution_capability_route_readiness;
    let _: fn(
        crate::SolverCapabilityCode,
        &[(String, String)],
    ) -> crate::SymbolicExecutionCapabilityRouteReadiness =
        crate::validate_symbolic_execution_capability_route_readiness_key_value_rows;
    let _: fn(
        crate::SolverCapabilityCode,
        &[String],
    ) -> crate::SymbolicExecutionCapabilityRouteReadiness =
        crate::validate_symbolic_execution_capability_route_readiness_text_lines;
    let _: fn(
        crate::SolverCapabilityCode,
    ) -> crate::api::SymbolicExecutionCapabilityRouteReadiness =
        crate::api::symbolic_execution_capability_route_readiness;
    let _: fn(
        crate::SolverCapabilityCode,
    ) -> crate::prelude::SymbolicExecutionCapabilityRouteReadiness =
        crate::prelude::symbolic_execution_capability_route_readiness;
    let _: fn(crate::SolverCapabilityCode) -> Vec<(String, String)> =
        crate::prelude::symbolic_execution_capability_route_readiness_key_value_rows;
    let _: fn(crate::SolverCapabilityCode) -> Vec<String> =
        crate::prelude::symbolic_execution_capability_route_readiness_text_lines;
    let _: fn() -> Vec<crate::SymbolicExecutionCapabilityRouteReadiness> =
        crate::symbolic_execution_all_supported_capability_route_readiness;
    let _: fn(
        &crate::SymbolicExecutionRouteAdmissionDecision,
    ) -> Vec<crate::SymbolicExecutionCapabilityRouteReadiness> =
        crate::symbolic_execution_all_supported_capability_route_readiness_for_decision;
    let _: fn() -> serde_json::Value =
        crate::symbolic_execution_all_supported_capability_route_readiness_json;
    let _: fn() -> Vec<(String, String)> =
        crate::symbolic_execution_all_supported_capability_route_readiness_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::symbolic_execution_all_supported_capability_route_readiness_text_lines;
    let _: fn(
        &[crate::SymbolicExecutionCapabilityRouteReadiness],
    ) -> Vec<crate::SymbolicExecutionCapabilityRouteReadiness> =
        crate::validate_symbolic_execution_all_supported_capability_route_readiness;
    let _: fn(&[(String, String)]) -> Vec<crate::SymbolicExecutionCapabilityRouteReadiness> =
        crate::validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows;
    let _: fn(&[String]) -> Vec<crate::SymbolicExecutionCapabilityRouteReadiness> =
        crate::validate_symbolic_execution_all_supported_capability_route_readiness_text_lines;
    let _: fn() -> crate::SymbolicExecutionDownstreamContractBundle =
        crate::symbolic_execution_downstream_contract_bundle;
    let _: fn() -> serde_json::Value = crate::symbolic_execution_downstream_contract_bundle_json;
    let _: fn() -> Vec<(String, String)> =
        crate::symbolic_execution_downstream_contract_bundle_key_value_rows;
    let _: fn() -> Vec<String> = crate::symbolic_execution_downstream_contract_bundle_text_lines;
    let _: fn(
        &crate::SymbolicExecutionDownstreamContractBundle,
    ) -> crate::SymbolicExecutionDownstreamContractBundle =
        crate::validate_symbolic_execution_downstream_contract_bundle;
    let _: fn(&[(String, String)]) -> crate::SymbolicExecutionDownstreamContractBundle =
        crate::validate_symbolic_execution_downstream_contract_bundle_key_value_rows;
    let _: fn(&[String]) -> crate::SymbolicExecutionDownstreamContractBundle =
        crate::validate_symbolic_execution_downstream_contract_bundle_text_lines;
    let _: fn() -> crate::api::SymbolicExecutionDownstreamContractBundle =
        crate::api::symbolic_execution_downstream_contract_bundle;
    let _: fn() -> Vec<(String, String)> =
        crate::prelude::symbolic_execution_downstream_contract_bundle_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::prelude::symbolic_execution_downstream_contract_bundle_text_lines;
    let _: fn() -> Vec<crate::api::SymbolicExecutionCapabilityRouteReadiness> =
        crate::api::symbolic_execution_all_supported_capability_route_readiness;
    let _: fn() -> Vec<crate::prelude::SymbolicExecutionCapabilityRouteReadiness> =
        crate::prelude::symbolic_execution_all_supported_capability_route_readiness;
    let _: fn() -> Vec<(String, String)> =
        crate::prelude::symbolic_execution_all_supported_capability_route_readiness_key_value_rows;
    let _: fn() -> Vec<String> =
        crate::prelude::symbolic_execution_all_supported_capability_route_readiness_text_lines;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::api::symbolic_execution_contract_manifest_key_value_pairs;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::prelude::symbolic_execution_contract_manifest_key_value_pairs;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::all_sat_enumeration_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::api::all_sat_enumeration_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::prelude::all_sat_enumeration_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> crate::SolverCapabilityContract =
        crate::all_sat_enumeration_symbolic_execution_contract;
    let _: fn() -> crate::api::SolverCapabilityContract =
        crate::api::all_sat_enumeration_symbolic_execution_contract;
    let _: fn() -> crate::prelude::SolverCapabilityContract =
        crate::prelude::all_sat_enumeration_symbolic_execution_contract;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::incremental_assumptions_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::prelude::incremental_assumptions_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> crate::SolverCapabilityContract =
        crate::incremental_assumptions_symbolic_execution_contract;
    let _: fn() -> Vec<(&'static str, String)> =
        crate::model_blocking_symbolic_execution_contract_key_value_pairs;
    let _: fn() -> crate::SolverCapabilityContract =
        crate::model_blocking_symbolic_execution_contract;
    let descriptor = crate::solver_capability_descriptor();
    let manifest = crate::solver_capability_descriptor_manifest();
    let symbolic_manifest = crate::symbolic_execution_contract_manifest();
    let symbolic_manifest_health = crate::symbolic_execution_contract_manifest_health_report();
    let symbolic_manifest_summary =
        crate::symbolic_execution_contract_manifest_diagnostic_summary();
    let route_admission = crate::symbolic_execution_route_admission_decision();
    let model_blocking_readiness = crate::symbolic_execution_capability_route_readiness(
        crate::SolverCapabilityCode::ModelBlocking,
    );
    let all_supported_readiness =
        crate::symbolic_execution_all_supported_capability_route_readiness();
    let downstream_bundle = crate::symbolic_execution_downstream_contract_bundle();
    let all_sat_contract = crate::all_sat_enumeration_symbolic_execution_contract();
    let incremental_contract = crate::incremental_assumptions_symbolic_execution_contract();
    let model_blocking_contract = crate::model_blocking_symbolic_execution_contract();

    assert_eq!(
        descriptor.schema,
        crate::AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA
    );
    assert_eq!(descriptor.capabilities, crate::AY_SOLVER_CAPABILITIES);
    assert!(descriptor.supports(crate::SolverCapabilityCode::ChcProofModelProduction));
    assert!(descriptor.supports(crate::SolverCapabilityCode::Btor2TraceReplayCompleteness));
    assert!(descriptor.supports(crate::SolverCapabilityCode::AllSatEnumeration));
    assert!(descriptor.supports(crate::SolverCapabilityCode::IncrementalAssumptions));
    assert!(descriptor.supports(crate::SolverCapabilityCode::ModelBlocking));
    assert_eq!(
        descriptor
            .capability(crate::SolverCapabilityCode::ModelBlocking)
            .expect("model-blocking row")
            .reason_code,
        "ay_owned_public_api"
    );
    assert!(
        descriptor
            .capability(crate::SolverCapabilityCode::ModelBlocking)
            .expect("model-blocking row")
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"),
        "facade descriptor should expose the narrow ay-dpll model-blocking primitive"
    );
    assert!(
        descriptor
            .capability(crate::SolverCapabilityCode::IncrementalAssumptions)
            .expect("incremental-assumptions row")
            .api_symbols
            .contains(&"ay_dpll::api::Solver::check_sat_assuming_with_details"),
        "facade descriptor should expose the narrow ay-dpll incremental-assumptions primitive"
    );
    assert_eq!(
        crate::AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
        "ay.model-blocking-clause.v1"
    );
    assert_eq!(
        crate::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
        "ay.model-blocking-clause-evidence.v1"
    );
    assert_eq!(
        manifest.schema,
        crate::AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA
    );
    assert_eq!(
        symbolic_manifest.schema,
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA
    );
    assert_eq!(
        symbolic_manifest.contracts,
        crate::AY_SYMBOLIC_EXECUTION_CONTRACTS
    );
    assert_eq!(symbolic_manifest.contracts.len(), 3);
    assert!(symbolic_manifest.all_contracts_fail_closed);
    assert!(symbolic_manifest.contracts.iter().any(|entry| {
        entry.capability_code == "model_blocking"
            && entry.contract_helper == "ay_dpll::api::model_blocking_symbolic_execution_contract"
    }));
    assert!(symbolic_manifest.contracts.iter().any(|entry| {
        entry.capability_code == "incremental_assumptions"
            && entry.key_value_helper
                == "ay_dpll::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs"
            && entry.accepted_status_codes.contains(&"unsat")
    }));
    assert!(symbolic_manifest.contracts.iter().any(|entry| {
        entry.capability_code == "all_sat_enumeration"
            && entry.contract_helper
                == "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
            && entry.rejected_status_codes.contains(&"capped")
    }));
    assert_eq!(
        symbolic_manifest_health.schema,
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA
    );
    assert_eq!(
        symbolic_manifest_health.status,
        crate::SymbolicExecutionContractManifestHealthStatus::Complete
    );
    assert_eq!(
        symbolic_manifest_health.reason,
        crate::SymbolicExecutionContractManifestHealthReason::Complete
    );
    assert_eq!(
        symbolic_manifest_health.diagnostic(),
        crate::SymbolicExecutionContractManifestHealthDiagnostic::Healthy
    );
    assert_eq!(
        symbolic_manifest_health.required_capabilities,
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
    );
    assert!(symbolic_manifest_health.accepted_for_consumer);
    assert!(symbolic_manifest_health.all_contracts_fail_closed);
    assert!(symbolic_manifest_health.issues.is_empty());
    assert_eq!(
        crate::validate_symbolic_execution_contract_manifest(&symbolic_manifest),
        symbolic_manifest_health
    );
    assert!(
        crate::validate_symbolic_execution_contract_manifest_key_value_pairs(
            &crate::symbolic_execution_contract_manifest_key_value_pairs()
        )
        .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_contract_manifest_round_trip(
            &symbolic_manifest,
            &crate::symbolic_execution_contract_manifest_key_value_pairs()
        )
        .accepted_for_consumer
    );
    assert!(
        crate::symbolic_execution_contract_manifest_round_trip_health_report()
            .accepted_for_consumer
    );
    assert!(manifest.capability_codes.contains(&"model_blocking"));
    assert!(manifest
        .capability_codes
        .contains(&"incremental_assumptions"));
    assert!(manifest.capability_codes.contains(&"all_sat_enumeration"));
    assert_eq!(
        all_sat_contract.schema,
        crate::AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
    );
    assert!(all_sat_contract
        .api_symbols
        .contains(&"ay_allsat::AllSatSolver::enumerate_with_config"));
    assert!(all_sat_contract
        .accepted_status_codes
        .contains(&"exhaustive"));
    assert!(all_sat_contract.rejected_status_codes.contains(&"capped"));
    assert!(all_sat_contract
        .consumer_responsibilities
        .contains(&crate::AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME));
    assert!(all_sat_contract.fail_closed);
    assert_eq!(
        incremental_contract.schema,
        crate::AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
    );
    assert!(incremental_contract.accepted_status_codes.contains(&"sat"));
    assert!(incremental_contract
        .accepted_status_codes
        .contains(&"unsat"));
    assert!(incremental_contract
        .rejected_status_codes
        .contains(&"unknown"));
    assert!(incremental_contract
        .consumer_responsibilities
        .contains(&crate::AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS));
    assert!(incremental_contract.fail_closed);
    assert_eq!(
        model_blocking_contract.schema,
        crate::AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
    );
    assert!(model_blocking_contract
        .accepted_status_codes
        .contains(&crate::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS));
    assert!(model_blocking_contract
        .rejected_status_codes
        .contains(&crate::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS));
    assert!(model_blocking_contract
        .consumer_responsibilities
        .contains(&crate::AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE));
    assert!(model_blocking_contract.fail_closed);
    assert!(
        crate::model_blocking_symbolic_execution_contract_key_value_pairs()
            .contains(&("fail_closed", "true".to_string()))
    );
    assert!(
        crate::incremental_assumptions_symbolic_execution_contract_key_value_pairs()
            .contains(&("fail_closed", "true".to_string()))
    );
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| *key == "capability_codes" && value.contains("model_blocking")));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| *key == "capability_codes" && value.contains("all_sat_enumeration")));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "capability_contracts"
                && value.contains("model_blocking")
                && value.contains("incremental_assumptions")
                && value.contains("all_sat_enumeration")
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "all_sat_enumeration_api_symbols"
                && value.contains("ay_allsat::AllSatIterator::outcome")
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "all_sat_enumeration_consumer_responsibilities"
                && value.contains(
                    crate::AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
                )
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .contains(&("all_sat_enumeration_fail_closed", "true".to_string())));
    assert!(
        crate::symbolic_execution_contract_manifest_key_value_pairs()
            .contains(&("contract_count", "3".to_string()))
    );
    assert!(
        crate::symbolic_execution_contract_manifest_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "contract_capabilities"
                    && value.contains("model_blocking")
                    && value.contains("incremental_assumptions")
                    && value.contains("all_sat_enumeration")
            })
    );
    assert!(
        crate::symbolic_execution_contract_manifest_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "contract_helpers"
                    && value.contains("ay_dpll::api::model_blocking_symbolic_execution_contract")
                    && value
                        .contains("ay_dpll::api::all_sat_enumeration_symbolic_execution_contract")
            })
    );
    assert!(
        crate::symbolic_execution_contract_manifest_key_value_pairs()
            .contains(&("all_contracts_fail_closed", "true".to_string()))
    );
    assert!(
        crate::symbolic_execution_contract_manifest_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "all_sat_enumeration_contract_helper"
                    && value == "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
            })
    );
    assert!(crate::symbolic_execution_contract_manifest_health_report()
        .to_key_value_pairs()
        .contains(&("status", "complete".to_string())));
    assert!(crate::symbolic_execution_contract_manifest_health_report()
        .to_key_value_pairs()
        .contains(&("accepted_for_consumer", "true".to_string())));
    assert!(
        crate::symbolic_execution_contract_manifest_health_key_value_rows()
            .contains(&("diagnostic".to_string(), "healthy".to_string()))
    );
    assert!(
        crate::symbolic_execution_contract_manifest_health_diagnostic_lines()
            .contains(&"diagnostic=healthy".to_string())
    );
    assert_eq!(
        symbolic_manifest_summary.schema,
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA
    );
    assert_eq!(
        symbolic_manifest_summary.health_status,
        symbolic_manifest_health.status_code
    );
    assert_eq!(
        symbolic_manifest_summary.contract_count,
        symbolic_manifest.contracts.len()
    );
    assert!(symbolic_manifest_summary.accepted_for_consumer);
    assert!(symbolic_manifest_summary.fail_closed);
    assert!(
        crate::validate_symbolic_execution_contract_manifest_diagnostic_summary(
            &symbolic_manifest_summary
        )
        .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(
            &crate::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows()
        )
        .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines(
            &crate::symbolic_execution_contract_manifest_diagnostic_summary_text_lines()
        )
        .accepted_for_consumer
    );
    assert_eq!(
        crate::symbolic_execution_contract_manifest_diagnostic_summary_json()["schema"],
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA
    );
    assert!(
        crate::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows()
            .contains(&("health_status".to_string(), "complete".to_string()))
    );
    assert!(
        crate::symbolic_execution_contract_manifest_diagnostic_summary_text_lines()
            .contains(&"fail_closed=true".to_string())
    );
    assert!(
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_contract_manifest_diagnostic_summary"
        )
    );
    assert!(
        crate::AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS.contains(
            &"ay_dpll::api::symbolic_execution_contract_manifest_diagnostic_summary_text_lines"
        )
    );
    assert_eq!(
        route_admission.schema,
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA
    );
    assert_eq!(
        route_admission.status,
        crate::SymbolicExecutionRouteAdmissionStatus::Accepted
    );
    assert_eq!(
        route_admission.reason,
        crate::SymbolicExecutionRouteAdmissionReason::AYAuthoritativeRoutes
    );
    assert!(route_admission.accepted_for_consumer);
    assert!(route_admission.fail_closed);
    assert!(route_admission.route_authorities.contains(
        &"model_blocking:ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
    ));
    assert!(route_admission.route_authorities.contains(
        &"incremental_assumptions:ay_dpll::api::incremental_assumptions_symbolic_execution_contract"
            .to_string()
    ));
    assert!(route_admission.route_authorities.contains(
        &"all_sat_enumeration:ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
            .to_string()
    ));
    assert!(
        crate::validate_symbolic_execution_route_admission_decision(&route_admission)
            .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_route_admission_decision_key_value_rows(
            &crate::symbolic_execution_route_admission_decision_key_value_rows()
        )
        .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_route_admission_decision_text_lines(
            &crate::symbolic_execution_route_admission_decision_text_lines()
        )
        .accepted_for_consumer
    );
    assert_eq!(
        crate::symbolic_execution_route_admission_decision_json()["reason"],
        "ay_authoritative_routes"
    );
    assert!(
        crate::symbolic_execution_route_admission_decision_key_value_rows().contains(&(
            "model_blocking_route_contract_helper".to_string(),
            "ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
        ))
    );
    assert!(
        crate::symbolic_execution_route_admission_decision_text_lines()
            .contains(&"all_sat_enumeration_route_fail_closed=true".to_string())
    );
    assert!(
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_route_admission_decision_key_value_rows"
        )
    );
    assert!(crate::AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_HELPERS
        .contains(&"ay_dpll::api::symbolic_execution_route_admission_decision_text_lines"));
    assert_eq!(
        model_blocking_readiness.schema,
        crate::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA
    );
    assert_eq!(
        model_blocking_readiness.status,
        crate::SymbolicExecutionCapabilityRouteReadinessStatus::Ready
    );
    assert_eq!(
        model_blocking_readiness.reason,
        crate::SymbolicExecutionCapabilityRouteReadinessReason::AYAuthoritativeCapabilityRoute
    );
    assert_eq!(
        model_blocking_readiness.selected_solver,
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER
    );
    assert_eq!(
        model_blocking_readiness.selected_solver_crate,
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE
    );
    assert_eq!(
        model_blocking_readiness.selected_solver_path_kind,
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND
    );
    assert_eq!(
        model_blocking_readiness.selected_solver_path,
        "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
    );
    assert!(model_blocking_readiness.supported);
    assert_eq!(model_blocking_readiness.unsupported_reason, "none");
    assert_eq!(
        model_blocking_readiness.required_contract_revision,
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION
    );
    assert_eq!(
        model_blocking_readiness.current_ay_revision_kind,
        crate::AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND
    );
    assert_ne!(model_blocking_readiness.current_ay_revision, "unknown");
    assert!(model_blocking_readiness.accepted_for_consumer);
    assert!(model_blocking_readiness.fail_closed);
    assert_eq!(
        model_blocking_readiness.contract_schema,
        crate::AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
    );
    assert!(
        crate::validate_symbolic_execution_capability_route_readiness(&model_blocking_readiness)
            .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_capability_route_readiness_key_value_rows(
            crate::SolverCapabilityCode::ModelBlocking,
            &crate::symbolic_execution_capability_route_readiness_key_value_rows(
                crate::SolverCapabilityCode::ModelBlocking
            )
        )
        .accepted_for_consumer
    );
    assert!(
        crate::validate_symbolic_execution_capability_route_readiness_text_lines(
            crate::SolverCapabilityCode::ModelBlocking,
            &crate::symbolic_execution_capability_route_readiness_text_lines(
                crate::SolverCapabilityCode::ModelBlocking
            )
        )
        .accepted_for_consumer
    );
    assert_eq!(
        crate::symbolic_execution_capability_route_readiness_json(
            crate::SolverCapabilityCode::ModelBlocking
        )["reason"],
        "ay_authoritative_capability_route"
    );
    assert!(
        crate::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS
            .contains(&"ay_dpll::api::symbolic_execution_capability_route_readiness")
    );
    assert!(
        crate::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_capability_route_readiness_key_value_rows"
        )
    );
    assert_eq!(
        all_supported_readiness.len(),
        crate::AY_SYMBOLIC_EXECUTION_CONTRACTS.len()
    );
    assert!(all_supported_readiness
        .iter()
        .all(|readiness| readiness.accepted_for_consumer));
    assert!(
        crate::validate_symbolic_execution_all_supported_capability_route_readiness(
            &all_supported_readiness
        )
        .iter()
        .all(|readiness| readiness.accepted_for_consumer)
    );
    assert!(
        crate::validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
            &crate::symbolic_execution_all_supported_capability_route_readiness_key_value_rows()
        )
        .iter()
        .all(|readiness| readiness.accepted_for_consumer)
    );
    assert!(
        crate::symbolic_execution_all_supported_capability_route_readiness_text_lines()
            .contains(&"model_blocking_status=ready".to_string())
    );
    assert!(
        crate::symbolic_execution_all_supported_capability_route_readiness_key_value_rows()
            .contains(&(
                "model_blocking_selected_solver_path".to_string(),
                "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer".to_string()
            ))
    );
    assert!(
        crate::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS
            .contains(&"ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness")
    );
    assert_eq!(
        downstream_bundle.schema,
        crate::AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA
    );
    assert_eq!(
        downstream_bundle.status,
        crate::SymbolicExecutionDownstreamContractBundleStatus::Accepted
    );
    assert!(downstream_bundle.accepted_for_consumer);
    assert_eq!(downstream_bundle.route_admission_decision, route_admission);
    assert_eq!(
        downstream_bundle.all_supported_capability_route_readiness,
        all_supported_readiness
    );
    assert!(
        crate::symbolic_execution_downstream_contract_bundle_key_value_rows()
            .iter()
            .any(
                |(key, value)| key == "readiness_model_blocking_selected_solver_path"
                    && value
                        == "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
            )
    );
    assert!(
        crate::validate_symbolic_execution_downstream_contract_bundle_key_value_rows(
            &crate::symbolic_execution_downstream_contract_bundle_key_value_rows()
        )
        .accepted_for_consumer
    );
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "incremental_assumptions_api_symbols"
                && value.contains("ay_dpll::api::Solver::check_sat_assuming_with_details")
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "incremental_assumptions_consumer_responsibilities"
                && value.contains(
                    crate::AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
                )
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .contains(&("incremental_assumptions_fail_closed", "true".to_string())));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "model_blocking_rejected_status_codes"
                && value.contains(crate::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS)
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "model_blocking_api_symbols"
                && value
                    .contains("ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer")
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .iter()
        .any(|(key, value)| {
            *key == "model_blocking_evidence_schemas"
                && value.contains(crate::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA)
        }));
    assert!(crate::solver_capability_descriptor_key_value_pairs()
        .contains(&("model_blocking_fail_closed", "true".to_string())));
}

#[test]
fn chc_detail_types_accessible_through_facade() {
    let _: fn() -> Option<crate::chc::CounterexampleStep> = || None;
    let _: fn() -> Option<crate::chc::PredicateInterpretation> = || None;
    let _: fn(
        &crate::chc::ChcProofTranscriptConsumerEvidence,
        u64,
        u64,
    ) -> crate::chc::ChcBmcUnsafeTraceAssignmentCompleteness =
        crate::chc::bmc_unsafe_trace_assignment_completeness;
    let _: fn() -> Option<crate::chc::ChcBmcUnsafeTraceAssignmentCompletenessStatus> = || None;
    let _: fn() -> Option<crate::chc::ChcBmcUnsafeTraceAssignmentCompletenessReason> = || None;
    assert_eq!(
        crate::chc::CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA,
        "ay.chc-bmc-unsafe-trace-assignment-completeness/v1"
    );
}

// =========================================================================
// #8690: EXTERNAL_CODEGEN API surface — Logic::QfAbvfp, try_forall, try_exists
// =========================================================================

#[test]
fn external_codegen_logic_qf_abvfp_accessible_from_facade() {
    // EXTERNAL_CODEGEN needs Logic::QfAbvfp for ANE floating-point precision proofs
    // that combine arrays, bitvectors, and floating-point.
    let solver = crate::Solver::try_new(crate::Logic::QfAbvfp);
    assert!(
        solver.is_ok(),
        "QfAbvfp logic must be constructible from facade"
    );
}

#[test]
fn external_codegen_try_forall_accessible_from_facade() {
    // EXTERNAL_CODEGEN needs try_forall for bounded universal quantifier in memory proofs.
    // Verify the method is callable through ay::Solver (not just ay_dpll::api::Solver).
    let mut solver = crate::Solver::new(crate::Logic::All);
    let x = solver.declare_const("x", crate::Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.ge(x, zero);
    let quantified = solver.try_forall(&[x], body);
    assert!(
        quantified.is_ok(),
        "try_forall must be callable from facade"
    );
}

#[test]
fn external_codegen_try_forall_int_range_accessible_from_facade() {
    // EXTERNAL_CODEGEN array-range proofs use `forall i. 0 <= i < N => P(i)`.
    let mut solver = crate::Solver::new(crate::Logic::All);
    let i = solver.declare_const("i", crate::Sort::Int);
    let mem_a = solver.declare_const(
        "mem_a",
        crate::Sort::array(crate::Sort::Int, crate::Sort::Int),
    );
    let mem_b = solver.declare_const(
        "mem_b",
        crate::Sort::array(crate::Sort::Int, crate::Sort::Int),
    );
    let read_a = solver.try_select(mem_a, i).unwrap();
    let read_b = solver.try_select(mem_b, i).unwrap();
    let body = solver.try_eq(read_a, read_b).unwrap();

    let quantified = solver.try_forall_int_range(i, 0, 4, body);

    assert!(
        quantified.is_ok(),
        "try_forall_int_range must be callable from facade"
    );
}

#[test]
fn external_codegen_try_exists_accessible_from_facade() {
    // EXTERNAL_CODEGEN needs try_exists for bounded existential quantifier in memory proofs.
    let mut solver = crate::Solver::new(crate::Logic::All);
    let x = solver.declare_const("x", crate::Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.ge(x, zero);
    let quantified = solver.try_exists(&[x], body);
    assert!(
        quantified.is_ok(),
        "try_exists must be callable from facade"
    );
}

#[test]
fn external_codegen_declare_const_returns_term_usable_in_try_forall() {
    // Acceptance criterion: Solver::declare_const returns Term usable as bound variable.
    let mut solver = crate::Solver::new(crate::Logic::All);
    let bv_x = solver.declare_const("x", crate::Sort::bitvec(32));
    let bv_zero = solver.try_bv_const_u64(0, 32).unwrap();
    let body = solver.bvuge(bv_x, bv_zero);
    let forall = solver.try_forall(&[bv_x], body);
    assert!(
        forall.is_ok(),
        "declare_const Term must work as try_forall bound variable"
    );
    // Assert the quantified formula to verify it is a valid Bool term
    solver.assert_term(forall.unwrap());
    // Note: We only verify API accessibility here, not quantified BV solving
    // correctness. Quantified BV may return Unknown depending on solver config.
    let result = solver.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "quantified BV formula should be SAT or Unknown (not UNSAT)"
    );
}

#[test]
fn external_codegen_api_module_reexports_cover_quantifiers() {
    // Verify all EXTERNAL_CODEGEN-needed types are accessible through ay::api::{...}
    let mut solver = crate::api::Solver::new(crate::api::Logic::QfAbvfp);
    let fp_x = solver.declare_const("fp_x", crate::api::Sort::FloatingPoint(8, 24));
    assert_eq!(solver.sort_of(fp_x), crate::api::Sort::FloatingPoint(8, 24));
}

#[test]
fn external_codegen_prelude_reexports_cover_quantifiers() {
    // Verify all EXTERNAL_CODEGEN-needed types are accessible through ay::prelude::*
    use crate::prelude::*;
    let mut solver = Solver::new(Logic::QfAbvfp);
    let bv_x = solver.declare_const("x", Sort::bitvec(32));
    assert_eq!(solver.sort_of(bv_x), Sort::bitvec(32));
}

#[test]
fn external_codegen_sort_of_public_facade_covers_requested_sorts() {
    let mut solver = crate::Solver::new(crate::Logic::All);

    let bool_term = solver.bool_const(true);
    let int_term = solver.int_const(7);
    let real_term = solver.rational_const(3, 2);
    let bv_term = solver.try_bv_const_u64(0x2a, 8).unwrap();
    let fp_term = solver
        .try_fp_const_from_bits(0x3ff0_0000_0000_0000, 11, 53)
        .unwrap();
    let array_sort = crate::Sort::array(crate::Sort::bitvec(8), crate::Sort::Int);
    let array_term = solver.declare_const("mem", array_sort.clone());
    let datatype = crate::DatatypeSort::new(
        "EXTERNAL_CODEGENSortOfOption",
        vec![
            crate::DatatypeConstructor::unit("none"),
            crate::DatatypeConstructor::new(
                "some",
                vec![crate::DatatypeField::new("value", crate::Sort::Int)],
            ),
        ],
    );
    solver.try_declare_datatype(&datatype).unwrap();
    let datatype_sort = crate::Sort::Datatype(datatype);
    let datatype_term = solver.declare_const("opt", datatype_sort.clone());

    assert_eq!(solver.sort_of(bool_term), crate::Sort::Bool);
    assert_eq!(solver.sort_of(int_term), crate::Sort::Int);
    assert_eq!(solver.sort_of(real_term), crate::Sort::Real);
    assert_eq!(solver.sort_of(bv_term), crate::Sort::bitvec(8));
    assert_eq!(solver.sort_of(fp_term), crate::Sort::FloatingPoint(11, 53));
    assert_eq!(solver.sort_of(array_term), array_sort);
    assert_eq!(solver.sort_of(datatype_term), datatype_sort);
}
