// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! API-health regressions for error visibility and fallible comparison parity.

mod solver_capability_descriptor_surface {
    #[test]
    fn narrow_dpll_api_and_root_reexports() {
        let _: fn() -> Option<crate::SolverCapabilityDescriptor> = || None;
        let _: fn() -> Option<crate::SolverCapabilityDescriptorManifest> = || None;
        let _: fn() -> Option<crate::SolverCapabilityContract> = || None;
        let _: fn() -> Option<crate::SolverCapabilityCode> = || None;
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
        let _: fn() -> Option<crate::SymbolicExecutionCapabilityRouteReadiness> = || None;
        let _: fn() -> Option<crate::SymbolicExecutionCapabilityRouteReadinessStatus> = || None;
        let _: fn() -> Option<crate::SymbolicExecutionCapabilityRouteReadinessReason> = || None;
        let _: fn() -> Option<crate::SymbolicExecutionDownstreamContractBundle> = || None;
        let _: fn() -> Option<crate::SymbolicExecutionDownstreamContractBundleStatus> = || None;
        let _: fn() -> Option<crate::SymbolicExecutionDownstreamContractBundleReason> = || None;
        let _: fn() -> Option<crate::api::SolverCapabilityDescriptor> = || None;
        let _: fn() -> Option<crate::api::SolverCapabilityDescriptorManifest> = || None;
        let _: fn() -> Option<crate::api::SolverCapabilityContract> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionContractManifest> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionContractManifestHealthReport> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionContractManifestDiagnosticSummary> =
            || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionRouteAdmissionDecision> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionRouteAdmissionStatus> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionRouteAdmissionReason> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionCapabilityRouteReadiness> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionCapabilityRouteReadinessStatus> =
            || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionCapabilityRouteReadinessReason> =
            || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionDownstreamContractBundle> = || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionDownstreamContractBundleStatus> =
            || None;
        let _: fn() -> Option<crate::api::SymbolicExecutionDownstreamContractBundleReason> =
            || None;
        let _: fn() -> Option<crate::api::ModelBlockingClauseEvidence> = || None;
        let _: fn() -> crate::SymbolicExecutionContractManifest =
            crate::symbolic_execution_contract_manifest;
        let _: fn() -> crate::api::SymbolicExecutionContractManifest =
            crate::api::symbolic_execution_contract_manifest;
        let _: fn() -> serde_json::Value = crate::api::symbolic_execution_contract_manifest_json;
        let _: fn() -> Vec<(&'static str, String)> =
            crate::api::symbolic_execution_contract_manifest_key_value_pairs;
        let _: fn() -> crate::SymbolicExecutionContractManifestHealthReport =
            crate::symbolic_execution_contract_manifest_health_report;
        let _: fn() -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::symbolic_execution_contract_manifest_health_report;
        let _: fn(
            &crate::api::SymbolicExecutionContractManifest,
        ) -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::validate_symbolic_execution_contract_manifest;
        let _: fn(&[(&str, String)]) -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::validate_symbolic_execution_contract_manifest_key_value_pairs;
        let _: fn(
            &crate::api::SymbolicExecutionContractManifest,
            &[(&str, String)],
        ) -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::validate_symbolic_execution_contract_manifest_round_trip;
        let _: fn() -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::symbolic_execution_contract_manifest_round_trip_health_report;
        let _: fn() -> Vec<(String, String)> =
            crate::api::symbolic_execution_contract_manifest_health_key_value_rows;
        let _: fn() -> Vec<String> =
            crate::api::symbolic_execution_contract_manifest_health_diagnostic_lines;
        let _: fn() -> crate::api::SymbolicExecutionContractManifestDiagnosticSummary =
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary;
        let _: fn(
            &crate::api::SymbolicExecutionContractManifest,
            &[(&str, String)],
        ) -> crate::api::SymbolicExecutionContractManifestDiagnosticSummary =
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip;
        let _: fn() -> serde_json::Value =
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_json;
        let _: fn() -> Vec<(String, String)> =
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows;
        let _: fn() -> Vec<String> =
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_text_lines;
        let _: fn(
            &crate::api::SymbolicExecutionContractManifestDiagnosticSummary,
        ) -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::validate_symbolic_execution_contract_manifest_diagnostic_summary;
        let _: fn(&[(String, String)]) -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows;
        let _: fn(&[String]) -> crate::api::SymbolicExecutionContractManifestHealthReport =
            crate::api::validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines;
        let _: fn() -> crate::api::SymbolicExecutionRouteAdmissionDecision =
            crate::api::symbolic_execution_route_admission_decision;
        let _: fn(
            &crate::api::SymbolicExecutionContractManifestDiagnosticSummary,
        ) -> crate::api::SymbolicExecutionRouteAdmissionDecision =
            crate::api::symbolic_execution_route_admission_decision_for_summary;
        let _: fn() -> serde_json::Value =
            crate::api::symbolic_execution_route_admission_decision_json;
        let _: fn() -> Vec<(String, String)> =
            crate::api::symbolic_execution_route_admission_decision_key_value_rows;
        let _: fn() -> Vec<String> =
            crate::api::symbolic_execution_route_admission_decision_text_lines;
        let _: fn(
            &crate::api::SymbolicExecutionRouteAdmissionDecision,
        ) -> crate::api::SymbolicExecutionRouteAdmissionDecision =
            crate::api::validate_symbolic_execution_route_admission_decision;
        let _: fn(&[(String, String)]) -> crate::api::SymbolicExecutionRouteAdmissionDecision =
            crate::api::validate_symbolic_execution_route_admission_decision_key_value_rows;
        let _: fn(&[String]) -> crate::api::SymbolicExecutionRouteAdmissionDecision =
            crate::api::validate_symbolic_execution_route_admission_decision_text_lines;
        let _: fn(
            crate::api::SolverCapabilityCode,
        ) -> crate::api::SymbolicExecutionCapabilityRouteReadiness =
            crate::api::symbolic_execution_capability_route_readiness;
        let _: fn(
            crate::api::SolverCapabilityCode,
            &crate::api::SymbolicExecutionRouteAdmissionDecision,
        ) -> crate::api::SymbolicExecutionCapabilityRouteReadiness =
            crate::api::symbolic_execution_capability_route_readiness_for_decision;
        let _: fn(crate::api::SolverCapabilityCode) -> serde_json::Value =
            crate::api::symbolic_execution_capability_route_readiness_json;
        let _: fn(crate::api::SolverCapabilityCode) -> Vec<(String, String)> =
            crate::api::symbolic_execution_capability_route_readiness_key_value_rows;
        let _: fn(crate::api::SolverCapabilityCode) -> Vec<String> =
            crate::api::symbolic_execution_capability_route_readiness_text_lines;
        let _: fn(
            &crate::api::SymbolicExecutionCapabilityRouteReadiness,
        ) -> crate::api::SymbolicExecutionCapabilityRouteReadiness =
            crate::api::validate_symbolic_execution_capability_route_readiness;
        let _: fn(
            crate::api::SolverCapabilityCode,
            &[(String, String)],
        ) -> crate::api::SymbolicExecutionCapabilityRouteReadiness =
            crate::api::validate_symbolic_execution_capability_route_readiness_key_value_rows;
        let _: fn(
            crate::api::SolverCapabilityCode,
            &[String],
        ) -> crate::api::SymbolicExecutionCapabilityRouteReadiness =
            crate::api::validate_symbolic_execution_capability_route_readiness_text_lines;
        let _: fn() -> Vec<crate::api::SymbolicExecutionCapabilityRouteReadiness> =
            crate::api::symbolic_execution_all_supported_capability_route_readiness;
        let _: fn(
            &crate::api::SymbolicExecutionRouteAdmissionDecision,
        ) -> Vec<crate::api::SymbolicExecutionCapabilityRouteReadiness> =
            crate::api::symbolic_execution_all_supported_capability_route_readiness_for_decision;
        let _: fn() -> serde_json::Value =
            crate::api::symbolic_execution_all_supported_capability_route_readiness_json;
        let _: fn() -> Vec<(String, String)> =
            crate::api::symbolic_execution_all_supported_capability_route_readiness_key_value_rows;
        let _: fn() -> Vec<String> =
            crate::api::symbolic_execution_all_supported_capability_route_readiness_text_lines;
        let _: fn(
            &[crate::api::SymbolicExecutionCapabilityRouteReadiness],
        ) -> Vec<crate::api::SymbolicExecutionCapabilityRouteReadiness> =
            crate::api::validate_symbolic_execution_all_supported_capability_route_readiness;
        let _: fn(&[(String, String)])
            -> Vec<crate::api::SymbolicExecutionCapabilityRouteReadiness> =
            crate::api::validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows;
        let _: fn(&[String]) -> Vec<crate::api::SymbolicExecutionCapabilityRouteReadiness> =
            crate::api::validate_symbolic_execution_all_supported_capability_route_readiness_text_lines;
        let _: fn() -> crate::api::SymbolicExecutionDownstreamContractBundle =
            crate::api::symbolic_execution_downstream_contract_bundle;
        let _: fn() -> serde_json::Value =
            crate::api::symbolic_execution_downstream_contract_bundle_json;
        let _: fn() -> Vec<(String, String)> =
            crate::api::symbolic_execution_downstream_contract_bundle_key_value_rows;
        let _: fn() -> Vec<String> =
            crate::api::symbolic_execution_downstream_contract_bundle_text_lines;
        let _: fn(
            &crate::api::SymbolicExecutionDownstreamContractBundle,
        ) -> crate::api::SymbolicExecutionDownstreamContractBundle =
            crate::api::validate_symbolic_execution_downstream_contract_bundle;
        let _: fn(&[(String, String)]) -> crate::api::SymbolicExecutionDownstreamContractBundle =
            crate::api::validate_symbolic_execution_downstream_contract_bundle_key_value_rows;
        let _: fn(&[String]) -> crate::api::SymbolicExecutionDownstreamContractBundle =
            crate::api::validate_symbolic_execution_downstream_contract_bundle_text_lines;
        let _: fn() -> crate::SolverCapabilityContract =
            crate::all_sat_enumeration_symbolic_execution_contract;
        let _: fn() -> crate::api::SolverCapabilityContract =
            crate::api::all_sat_enumeration_symbolic_execution_contract;
        let _: fn() -> Vec<(&'static str, String)> =
            crate::api::all_sat_enumeration_symbolic_execution_contract_key_value_pairs;
        let _: fn() -> crate::SolverCapabilityContract =
            crate::incremental_assumptions_symbolic_execution_contract;
        let _: fn() -> crate::api::SolverCapabilityContract =
            crate::api::incremental_assumptions_symbolic_execution_contract;
        let _: fn() -> Vec<(&'static str, String)> =
            crate::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs;
        let _: fn() -> crate::api::SolverCapabilityContract =
            crate::api::model_blocking_symbolic_execution_contract;
        let _: fn() -> Vec<(&'static str, String)> =
            crate::api::model_blocking_symbolic_execution_contract_key_value_pairs;
        let _: fn() -> Vec<(&'static str, String)> =
            crate::api::solver_capability_descriptor_key_value_pairs;
        let descriptor = crate::api::solver_capability_descriptor();
        let manifest = crate::api::solver_capability_descriptor_manifest();
        let symbolic_manifest = crate::api::symbolic_execution_contract_manifest();
        let symbolic_manifest_health =
            crate::api::symbolic_execution_contract_manifest_health_report();
        let symbolic_manifest_summary =
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary();
        let route_admission = crate::api::symbolic_execution_route_admission_decision();
        let model_blocking_readiness = crate::api::symbolic_execution_capability_route_readiness(
            crate::api::SolverCapabilityCode::ModelBlocking,
        );
        let all_supported_readiness =
            crate::api::symbolic_execution_all_supported_capability_route_readiness();
        let downstream_bundle = crate::api::symbolic_execution_downstream_contract_bundle();
        let incremental_contract =
            crate::api::incremental_assumptions_symbolic_execution_contract();
        let all_sat_contract = crate::api::all_sat_enumeration_symbolic_execution_contract();
        let model_blocking_contract = crate::api::model_blocking_symbolic_execution_contract();

        assert_eq!(
            descriptor.schema,
            crate::api::AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA
        );
        assert_eq!(descriptor.capabilities, crate::api::AY_SOLVER_CAPABILITIES);
        assert!(descriptor.supports(crate::api::SolverCapabilityCode::ModelBlocking));
        assert!(descriptor
            .capability(crate::api::SolverCapabilityCode::ModelBlocking)
            .expect("model-blocking row")
            .api_symbols
            .contains(&"ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"));
        assert!(descriptor
            .capability(crate::api::SolverCapabilityCode::ModelBlocking)
            .expect("model-blocking row")
            .evidence_schemas
            .contains(&crate::api::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA));
        assert_eq!(
            crate::solver_capability_descriptor_json()["schema"],
            crate::api::AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA
        );
        assert_eq!(
            manifest.schema,
            crate::api::AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA
        );
        assert_eq!(
            symbolic_manifest.schema,
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA
        );
        assert_eq!(
            symbolic_manifest.contracts,
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACTS
        );
        assert_eq!(symbolic_manifest.contracts.len(), 3);
        assert!(symbolic_manifest.all_contracts_fail_closed);
        assert!(symbolic_manifest.contracts.iter().any(|entry| {
            entry.capability_code == "model_blocking"
                && entry.contract_helper
                    == "ay_dpll::api::model_blocking_symbolic_execution_contract"
        }));
        assert!(symbolic_manifest.contracts.iter().any(|entry| {
            entry.capability_code == "incremental_assumptions"
                && entry.key_value_helper
                    == "ay_dpll::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs"
                && entry.accepted_status_codes.contains(&"unsat")
        }));
        assert!(symbolic_manifest.contracts.iter().any(|entry| {
            entry.capability_code == "all_sat_enumeration"
                && entry.contract_schema
                    == crate::api::AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
                && entry.rejected_status_codes.contains(&"capped")
        }));
        assert_eq!(
            symbolic_manifest_health.schema,
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA
        );
        assert_eq!(
            symbolic_manifest_health.status,
            crate::api::SymbolicExecutionContractManifestHealthStatus::Complete
        );
        assert_eq!(
            symbolic_manifest_health.reason,
            crate::api::SymbolicExecutionContractManifestHealthReason::Complete
        );
        assert_eq!(
            symbolic_manifest_health.diagnostic(),
            crate::api::SymbolicExecutionContractManifestHealthDiagnostic::Healthy
        );
        assert_eq!(
            symbolic_manifest_health.required_capabilities,
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES
        );
        assert!(symbolic_manifest_health.accepted_for_consumer);
        assert!(symbolic_manifest_health.all_contracts_fail_closed);
        assert!(symbolic_manifest_health.issues.is_empty());
        assert_eq!(
            crate::api::validate_symbolic_execution_contract_manifest(&symbolic_manifest),
            symbolic_manifest_health
        );
        assert!(
            crate::api::validate_symbolic_execution_contract_manifest_key_value_pairs(
                &crate::api::symbolic_execution_contract_manifest_key_value_pairs()
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_contract_manifest_round_trip(
                &symbolic_manifest,
                &crate::api::symbolic_execution_contract_manifest_key_value_pairs()
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_round_trip_health_report()
                .accepted_for_consumer
        );
        assert!(manifest.capability_codes.contains(&"model_blocking"));
        assert!(descriptor.supports(crate::api::SolverCapabilityCode::IncrementalAssumptions));
        assert!(descriptor.supports(crate::api::SolverCapabilityCode::AllSatEnumeration));
        assert_eq!(
            incremental_contract.schema,
            crate::api::AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert!(incremental_contract.accepted_status_codes.contains(&"sat"));
        assert!(incremental_contract
            .accepted_status_codes
            .contains(&"unsat"));
        assert!(incremental_contract
            .rejected_status_codes
            .contains(&"unknown"));
        assert!(incremental_contract.consumer_responsibilities.contains(
            &crate::api::AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS
        ));
        assert!(incremental_contract.fail_closed);
        assert_eq!(
            all_sat_contract.schema,
            crate::api::AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
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
            .contains(&crate::api::AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME));
        assert!(all_sat_contract.fail_closed);
        assert_eq!(
            model_blocking_contract.schema,
            crate::api::AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert!(model_blocking_contract
            .accepted_status_codes
            .contains(&crate::api::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS));
        assert!(model_blocking_contract
            .rejected_status_codes
            .contains(&crate::api::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS));
        assert!(model_blocking_contract.consumer_responsibilities.contains(
            &crate::api::AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION
        ));
        assert!(model_blocking_contract.fail_closed);
        assert!(
            crate::api::incremental_assumptions_symbolic_execution_contract_key_value_pairs()
                .contains(&("fail_closed", "true".to_string()))
        );
        assert!(
            crate::api::model_blocking_symbolic_execution_contract_key_value_pairs()
                .contains(&("fail_closed", "true".to_string()))
        );
        assert_eq!(
            downstream_bundle.schema,
            crate::api::AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA
        );
        assert_eq!(
            downstream_bundle.status,
            crate::api::SymbolicExecutionDownstreamContractBundleStatus::Accepted
        );
        assert!(downstream_bundle.accepted_for_consumer);
        assert_eq!(downstream_bundle.route_admission_decision, route_admission);
        assert_eq!(
            downstream_bundle.all_supported_capability_route_readiness,
            all_supported_readiness
        );
        assert!(
            crate::api::symbolic_execution_downstream_contract_bundle_key_value_rows()
                .iter()
                .any(|(key, value)| {
                    key == "readiness_model_blocking_selected_solver_path"
                        && value
                            == "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
                })
        );
        assert!(
            crate::api::validate_symbolic_execution_downstream_contract_bundle_key_value_rows(
                &crate::api::symbolic_execution_downstream_contract_bundle_key_value_rows()
            )
            .accepted_for_consumer
        );
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| *key == "capability_codes" && value.contains("model_blocking")));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "capability_contracts"
                    && value.contains("model_blocking")
                    && value.contains("incremental_assumptions")
                    && value.contains("all_sat_enumeration")
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "all_sat_enumeration_api_symbols"
                    && value.contains("ay_allsat::AllSatIterator::outcome")
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "all_sat_enumeration_consumer_responsibilities"
                    && value.contains(
                        crate::api::AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION
                    )
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .contains(&("all_sat_enumeration_fail_closed", "true".to_string())));
        assert!(
            crate::api::symbolic_execution_contract_manifest_key_value_pairs()
                .contains(&("contract_count", "3".to_string()))
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_key_value_pairs()
                .iter()
                .any(|(key, value)| {
                    *key == "contract_capabilities"
                        && value.contains("model_blocking")
                        && value.contains("incremental_assumptions")
                        && value.contains("all_sat_enumeration")
                })
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_key_value_pairs()
                .iter()
                .any(|(key, value)| {
                    *key == "contract_helpers"
                        && value.contains(
                            "ay_dpll::api::all_sat_enumeration_symbolic_execution_contract",
                        )
                })
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_key_value_pairs()
                .iter()
                .any(|(key, value)| {
                    *key == "all_sat_enumeration_rejected_status_codes" && value.contains("capped")
                })
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_health_report()
                .to_key_value_pairs()
                .contains(&("status", "complete".to_string()))
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_health_report()
                .to_key_value_pairs()
                .contains(&("accepted_for_consumer", "true".to_string()))
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_health_key_value_rows()
                .contains(&("diagnostic".to_string(), "healthy".to_string()))
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_health_diagnostic_lines()
                .contains(&"diagnostic=healthy".to_string())
        );
        assert_eq!(
            symbolic_manifest_summary.schema,
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA
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
            crate::api::validate_symbolic_execution_contract_manifest_diagnostic_summary(
                &symbolic_manifest_summary
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows(
                &crate::api::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows()
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines(
                &crate::api::symbolic_execution_contract_manifest_diagnostic_summary_text_lines()
            )
            .accepted_for_consumer
        );
        assert_eq!(
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_json()["schema"],
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows()
                .contains(&("health_status".to_string(), "complete".to_string()))
        );
        assert!(
            crate::api::symbolic_execution_contract_manifest_diagnostic_summary_text_lines()
                .contains(&"fail_closed=true".to_string())
        );
        assert!(
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS.contains(
                &"ay_dpll::api::validate_symbolic_execution_contract_manifest_diagnostic_summary"
            )
        );
        assert!(
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS.contains(
                &"ay_dpll::api::symbolic_execution_contract_manifest_diagnostic_summary_text_lines"
            )
        );
        assert_eq!(
            route_admission.schema,
            crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA
        );
        assert_eq!(
            route_admission.status,
            crate::api::SymbolicExecutionRouteAdmissionStatus::Accepted
        );
        assert_eq!(
            route_admission.reason,
            crate::api::SymbolicExecutionRouteAdmissionReason::AYAuthoritativeRoutes
        );
        assert!(route_admission.accepted_for_consumer);
        assert!(route_admission.fail_closed);
        assert!(route_admission.route_authorities.contains(
            &"model_blocking:ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
        ));
        assert!(route_admission.route_authorities.contains(
            &"incremental_assumptions:ay_dpll::api::incremental_assumptions_symbolic_execution_contract".to_string()
        ));
        assert!(route_admission.route_authorities.contains(
            &"all_sat_enumeration:ay_dpll::api::all_sat_enumeration_symbolic_execution_contract"
                .to_string()
        ));
        assert!(
            crate::api::validate_symbolic_execution_route_admission_decision(&route_admission)
                .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_route_admission_decision_key_value_rows(
                &crate::api::symbolic_execution_route_admission_decision_key_value_rows()
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_route_admission_decision_text_lines(
                &crate::api::symbolic_execution_route_admission_decision_text_lines()
            )
            .accepted_for_consumer
        );
        assert_eq!(
            crate::api::symbolic_execution_route_admission_decision_json()["reason"],
            "ay_authoritative_routes"
        );
        assert!(
            crate::api::symbolic_execution_route_admission_decision_key_value_rows().contains(&(
                "model_blocking_route_contract_helper".to_string(),
                "ay_dpll::api::model_blocking_symbolic_execution_contract".to_string()
            ))
        );
        assert!(
            crate::api::symbolic_execution_route_admission_decision_text_lines()
                .contains(&"all_sat_enumeration_route_fail_closed=true".to_string())
        );
        assert!(crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_route_admission_decision_key_value_rows"
        ));
        assert!(crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_HELPERS
            .contains(&"ay_dpll::api::symbolic_execution_route_admission_decision_text_lines"));
        assert_eq!(
            model_blocking_readiness.schema,
            crate::api::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA
        );
        assert_eq!(
            model_blocking_readiness.status,
            crate::api::SymbolicExecutionCapabilityRouteReadinessStatus::Ready
        );
        assert_eq!(
            model_blocking_readiness.reason,
            crate::api::SymbolicExecutionCapabilityRouteReadinessReason::AYAuthoritativeCapabilityRoute
        );
        assert_eq!(
            model_blocking_readiness.selected_solver,
            crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER
        );
        assert_eq!(
            model_blocking_readiness.selected_solver_crate,
            crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE
        );
        assert_eq!(
            model_blocking_readiness.selected_solver_path_kind,
            crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND
        );
        assert_eq!(
            model_blocking_readiness.selected_solver_path,
            "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer"
        );
        assert!(model_blocking_readiness.supported);
        assert_eq!(model_blocking_readiness.unsupported_reason, "none");
        assert_eq!(
            model_blocking_readiness.required_contract_revision,
            crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION
        );
        assert_eq!(
            model_blocking_readiness.current_ay_revision_kind,
            crate::api::AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND
        );
        assert_ne!(model_blocking_readiness.current_ay_revision, "unknown");
        assert!(model_blocking_readiness.accepted_for_consumer);
        assert!(model_blocking_readiness.fail_closed);
        assert_eq!(
            model_blocking_readiness.contract_schema,
            crate::api::AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA
        );
        assert!(
            crate::api::validate_symbolic_execution_capability_route_readiness(
                &model_blocking_readiness
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_capability_route_readiness_key_value_rows(
                crate::api::SolverCapabilityCode::ModelBlocking,
                &crate::api::symbolic_execution_capability_route_readiness_key_value_rows(
                    crate::api::SolverCapabilityCode::ModelBlocking
                )
            )
            .accepted_for_consumer
        );
        assert!(
            crate::api::validate_symbolic_execution_capability_route_readiness_text_lines(
                crate::api::SolverCapabilityCode::ModelBlocking,
                &crate::api::symbolic_execution_capability_route_readiness_text_lines(
                    crate::api::SolverCapabilityCode::ModelBlocking
                )
            )
            .accepted_for_consumer
        );
        assert_eq!(
            crate::api::symbolic_execution_capability_route_readiness_json(
                crate::api::SolverCapabilityCode::ModelBlocking
            )["reason"],
            "ay_authoritative_capability_route"
        );
        assert!(
            crate::api::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS
                .contains(&"ay_dpll::api::symbolic_execution_capability_route_readiness")
        );
        assert!(crate::api::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS.contains(
            &"ay_dpll::api::validate_symbolic_execution_capability_route_readiness_key_value_rows"
        ));
        assert_eq!(
            all_supported_readiness.len(),
            crate::api::AY_SYMBOLIC_EXECUTION_CONTRACTS.len()
        );
        assert!(all_supported_readiness
            .iter()
            .all(|readiness| readiness.accepted_for_consumer));
        assert!(
            crate::api::validate_symbolic_execution_all_supported_capability_route_readiness(
                &all_supported_readiness
            )
            .iter()
            .all(|readiness| readiness.accepted_for_consumer)
        );
        assert!(
            crate::api::validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
                &crate::api::symbolic_execution_all_supported_capability_route_readiness_key_value_rows()
            )
            .iter()
            .all(|readiness| readiness.accepted_for_consumer)
        );
        assert!(
            crate::api::symbolic_execution_all_supported_capability_route_readiness_json()
                .as_array()
                .is_some_and(|rows| rows.len() == crate::api::AY_SYMBOLIC_EXECUTION_CONTRACTS.len())
        );
        assert!(
            crate::api::symbolic_execution_all_supported_capability_route_readiness_text_lines()
                .contains(&"model_blocking_status=ready".to_string())
        );
        assert!(
            crate::api::symbolic_execution_all_supported_capability_route_readiness_key_value_rows(
            )
            .contains(&(
                "model_blocking_selected_solver_path".to_string(),
                "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer".to_string()
            ))
        );
        assert!(
            crate::api::AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS.contains(
                &"ay_dpll::api::symbolic_execution_all_supported_capability_route_readiness"
            )
        );
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "incremental_assumptions_api_symbols"
                    && value.contains("ay_dpll::api::Solver::check_sat_assuming_with_details")
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "incremental_assumptions_consumer_responsibilities"
                    && value.contains(
                        crate::api::AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION
                    )
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .contains(&("incremental_assumptions_fail_closed", "true".to_string())));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "model_blocking_consumer_responsibilities"
                    && value.contains(
                        crate::api::AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY
                    )
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "model_blocking_api_symbols"
                    && value.contains(
                        "ay_dpll::api::Solver::try_assert_model_blocking_clause_for_consumer",
                    )
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .iter()
            .any(|(key, value)| {
                *key == "model_blocking_evidence_schemas"
                    && value.contains(crate::api::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA)
            }));
        assert!(crate::api::solver_capability_descriptor_key_value_pairs()
            .contains(&("model_blocking_fail_closed", "true".to_string())));
        assert_eq!(
            crate::api::AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
            "ay.model-blocking-clause-evidence.v1"
        );
    }
}

use crate::api::*;

#[test]
#[should_panic(
    expected = "sort mismatch in lt: expected same arithmetic sort (Int,Int) or (Real,Real), got Bool, Bool"
)]
fn test_lt_panics_on_non_arithmetic_sort() {
    let mut solver = Solver::new(Logic::QfLia);
    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);

    let _ = solver.lt(p, q);
}

#[test]
#[should_panic(
    expected = "sort mismatch in ge: expected same arithmetic sort (Int,Int) or (Real,Real), got Int, Real"
)]
fn test_ge_panics_on_mixed_int_real() {
    let mut solver = Solver::new(Logic::QfLira);
    let i = solver.declare_const("i", Sort::Int);
    let r = solver.declare_const("r", Sort::Real);

    let _ = solver.ge(i, r);
}

#[test]
fn test_check_sat_assuming_records_internal_error_for_non_bool_assumption() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    let result = solver.check_sat_assuming(&[x]);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::InternalError));
    assert_eq!(
        solver.get_reason_unknown().as_deref(),
        Some("internal-error")
    );
    // The executor error detail is preserved (#4663)
    assert!(solver.executor_error().is_some());
}

#[test]
fn test_unknown_reason_clears_after_successful_solve_and_reset() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    let first = solver.check_sat_assuming(&[x]);
    assert_eq!(first, SolveResult::Unknown);
    assert!(solver.unknown_reason().is_some());

    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    let second = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(second, SolveResult::Sat);
    assert!(solver.unknown_reason().is_none());

    let _ = solver.check_sat_assuming(&[x]);
    assert!(solver.unknown_reason().is_some());
    solver.reset();
    assert!(solver.unknown_reason().is_none());
}

/// Verify that try_reset clears soft_constraints so they do not leak into
/// the next solving session (#8617 audit).
#[test]
fn test_try_reset_clears_solver_state_completely() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");
    solver.try_assert_term(x_gt_0).expect("boolean assertion");

    // Push a scope to verify scope_level resets
    solver.try_push().expect("push should succeed");
    assert_eq!(solver.num_scopes(), 1);

    // Solve to populate internal state
    let result = solver.try_check_sat().expect("check_sat should succeed");
    assert_eq!(result, SolveResult::Sat);

    // Reset should clear everything
    solver.try_reset().expect("reset should succeed");
    assert_eq!(solver.num_scopes(), 0, "scope_level should reset to 0");
    assert!(
        solver.unknown_reason().is_none(),
        "unknown reason should be cleared after reset"
    );
    assert!(
        solver.executor_error().is_none(),
        "executor error should be cleared after reset"
    );
    assert!(
        solver.assertions().is_empty(),
        "assertions should be cleared after reset"
    );
}

/// Verify that try_reset_assertions preserves declarations but clears
/// assertions and scope state (#8617 audit).
#[test]
fn test_try_reset_assertions_preserves_declarations() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");
    solver.try_assert_term(x_gt_0).expect("boolean assertion");

    solver.try_push().expect("push should succeed");
    assert_eq!(solver.num_scopes(), 1);

    // Reset assertions — should preserve x but clear assertions and scopes
    solver
        .try_reset_assertions()
        .expect("reset-assertions should succeed");
    assert_eq!(
        solver.num_scopes(),
        0,
        "scope_level should reset to 0 after reset-assertions"
    );

    // x should still be usable (declaration preserved)
    let one = solver.int_const(1);
    let x_eq_1 = solver
        .try_eq(x, one)
        .expect("x should still be a valid term");
    solver
        .try_assert_term(x_eq_1)
        .expect("boolean assertion should succeed after reset-assertions");
    let result = solver
        .try_check_sat()
        .expect("check_sat should succeed after reset-assertions");
    assert_eq!(
        result,
        SolveResult::Sat,
        "x = 1 should be SAT after reset-assertions"
    );
}
