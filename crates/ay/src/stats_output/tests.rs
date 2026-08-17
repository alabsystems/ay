// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_to_json_contains_required_fields() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::from_millis(42));
    stats.insert("conflicts", 1234);
    stats.insert("decisions", 5678);
    stats.insert_text("sat.capability.preprocess.state", "on");

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_eq!(parsed["result"], "sat");
    assert_eq!(parsed["wall_time_ms"], 42);
    assert_eq!(parsed["ay_build"]["stamp"], BUILD_PROVENANCE.stamp);
    assert_eq!(parsed["conflicts"], 1234);
    assert_eq!(parsed["decisions"], 5678);
    assert_eq!(parsed["sat.capability.preprocess.state"], "on");
    assert!(
        parsed.get("competition_jit").is_none(),
        "competition JIT metadata should only appear when attached"
    );
}

#[test]
fn test_to_json_suppresses_retired_sat_propagation_counters() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::ZERO);
    stats.insert("sat.native_code_helpers_enabled", 1);
    stats.insert("sat.retired_propagation_compiler_rounds", 2);
    stats.insert("sat.propagation_native_active", 1);
    stats.insert("sat.propagation_native_propagations", 3);

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    assert_eq!(parsed["sat.native_code_helpers_enabled"], 1);
    assert!(
        parsed
            .as_object()
            .expect("stats JSON should be an object")
            .keys()
            .all(|key| !is_retired_sat_propagation_counter(key)),
        "retired SAT propagation counters must not appear in stats JSON: {parsed}"
    );
}

#[test]
fn test_to_json_contains_competition_jit_evidence_with_counter() {
    let mut stats = RunStatistics::new(SolveMode::Pb, "sat", Duration::from_millis(7));
    stats.insert("pb_pbo_candidate_applications", 9);
    stats.competition_jit = Some(CompetitionJitEvidence {
        track: "pb".to_string(),
        artifact_id: "pb-pbo-candidates".to_string(),
        candidate_mode: "solver-program".to_string(),
        application_counter: Some(CompetitionJitApplicationCounter {
            key: "pb_pbo_candidate_applications".to_string(),
            value: 9,
        }),
    });

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    let evidence = &parsed["competition_jit"];
    assert_eq!(evidence["schema_version"], 1);
    assert_eq!(evidence["track"], "pb");
    assert_eq!(evidence["artifact_id"], "pb-pbo-candidates");
    assert_eq!(evidence["artifact"], "pb-pbo-candidates");
    assert_eq!(evidence["candidate_mode"], "solver-program");
    assert_eq!(evidence["requested_mode"], "solver-program");
    assert_eq!(evidence["native_dispatch"], false);
    assert_eq!(evidence["fail_closed"], false);
    assert_eq!(
        evidence["application_counter"]["key"],
        "pb_pbo_candidate_applications"
    );
    assert_eq!(evidence["application_counter"]["value"], 9);
    assert_eq!(parsed["pb_pbo_candidate_applications"], 9);
}

#[test]
fn test_to_json_contains_competition_jit_evidence_without_counter() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "unknown", Duration::ZERO);
    stats.competition_jit = Some(CompetitionJitEvidence {
        track: "sat".to_string(),
        artifact_id: "sat-native-code-helpers".to_string(),
        candidate_mode: "current".to_string(),
        application_counter: None,
    });

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    let evidence = &parsed["competition_jit"];
    assert_eq!(evidence["schema_version"], 1);
    assert_eq!(evidence["track"], "sat");
    assert_eq!(evidence["artifact_id"], "sat-native-code-helpers");
    assert_eq!(evidence["artifact"], "sat-native-code-helpers");
    assert_eq!(evidence["candidate_mode"], "current");
    assert_eq!(evidence["requested_mode"], "current");
    assert_eq!(evidence["native_dispatch"], false);
    assert_eq!(evidence["fail_closed"], true);
    assert!(
        evidence.get("application_counter").is_none(),
        "application counter should be omitted when not applicable"
    );
}

#[test]
fn test_to_json_competition_jit_current_mode_with_applications_dispatches_native() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::ZERO);
    stats.competition_jit = Some(CompetitionJitEvidence {
        track: "sat".to_string(),
        artifact_id: "sat-native-code-helpers".to_string(),
        candidate_mode: "current".to_string(),
        application_counter: Some(CompetitionJitApplicationCounter {
            key: "sat.native_code_helper_applications".to_string(),
            value: 3,
        }),
    });

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    let evidence = &parsed["competition_jit"];
    assert_eq!(evidence["requested_mode"], "current");
    assert_eq!(evidence["candidate_mode"], "current");
    assert_eq!(evidence["native_dispatch"], true);
    assert_eq!(evidence["fail_closed"], false);
}

#[test]
fn test_build_provenance_helpers_include_build_stamp() {
    assert_eq!(
        BUILD_PROVENANCE.json_value()["stamp"],
        serde_json::Value::String(BUILD_PROVENANCE.stamp.to_string())
    );
    assert!(
        BUILD_PROVENANCE
            .human_banner()
            .contains(BUILD_PROVENANCE.stamp),
        "human banner should expose the active build stamp"
    );
    assert!(
        BUILD_PROVENANCE
            .comment_line()
            .contains(BUILD_PROVENANCE.stamp),
        "comment line should expose the active build stamp"
    );
}

#[test]
fn test_to_json_single_line() {
    let stats = RunStatistics::new(SolveMode::Smt, "done", Duration::from_millis(100));
    let json_str = stats.to_json();
    assert!(
        !json_str.contains('\n'),
        "JSON stats should be a single line for easy grep/parse"
    );
}

#[test]
fn test_to_json_all_modes() {
    for (mode, expected) in [
        (SolveMode::Smt, "smt"),
        (SolveMode::DimacsSat, "dimacs-sat"),
        (SolveMode::Chc, "chc"),
        (SolveMode::Portfolio, "portfolio"),
        (SolveMode::Pb, "pb"),
    ] {
        let stats = RunStatistics::new(mode, "unknown", Duration::ZERO);
        let json_str = stats.to_json();
        let parsed: serde_json::Value = serde_json::from_str(&json_str).unwrap();
        assert_eq!(parsed["mode"], expected);
    }
}

#[test]
fn test_stats_config_any() {
    assert!(!StatsConfig {
        human: false,
        json: false
    }
    .any());
    assert!(StatsConfig {
        human: true,
        json: false
    }
    .any());
    assert!(StatsConfig {
        human: false,
        json: true
    }
    .any());
    assert!(StatsConfig {
        human: true,
        json: true
    }
    .any());
}
