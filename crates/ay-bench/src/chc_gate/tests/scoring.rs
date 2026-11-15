// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PAR-2 scoring, baseline comparison and outcome classification.

use super::*;

#[test]
fn chc_gate_par2_scores_unsolved_as_double_timeout() {
    let solved = CaseRecord {
        schema: CASES_SCHEMA,
        case_id: "a".to_string(),
        path: "a.smt2".to_string(),
        solver_input_path: "snapshot-a.smt2".to_string(),
        input_sha256: "sha256:test".to_string(),
        input_size_bytes: 1,
        category: "LIA".to_string(),
        family: "f".to_string(),
        expected_status: "sat".to_string(),
        expected_source: "manifest".to_string(),
        source: "manifest:m".to_string(),
        status: "sat".to_string(),
        classification: "solved".to_string(),
        solved: true,
        wrong: false,
        invalid: false,
        invalid_reasons: Vec::new(),
        elapsed_s: Some(0.25),
        par2_s: 0.25,
        timed_out: false,
        exit_code: Some(0),
        process_status: "exit status: 0".to_string(),
        stats_json_present: true,
        stats_json_path: String::new(),
        validation: ValidationTelemetry::default(),
        transform_memory: TransformMemoryTelemetry::default(),
        route: RouteTelemetry::default(),
        route_counters: BTreeMap::new(),
        required_route_counters: Vec::new(),
        missing_required_route_counters: Vec::new(),
        stdout: String::new(),
        stderr: String::new(),
        command_argv: Vec::new(),
        command_env: BTreeMap::new(),
    };
    let mut timeout = solved.clone();
    timeout.case_id = "b".to_string();
    timeout.solved = false;
    timeout.status = "timeout".to_string();
    timeout.classification = "timeout".to_string();
    timeout.par2_s = 4.0;
    let summary = summarize_overall(&[solved, timeout], false);
    assert_eq!(summary.solved, 1);
    assert_eq!(summary.par2_total, 4.25);
    assert_eq!(summary.memout, 0);
}

#[test]
fn chc_gate_baseline_regression_check_fails_on_solved_loss() {
    let baseline = BaselineStats {
        source: "baseline.json".to_string(),
        solved: Some(2),
        par2_total: Some(1.0),
        resource_plan: Some(crate::resource::ResourcePlan {
            requested_jobs: 1,
            jobs: 1,
            memlimit_mb_per_child: 1024,
            nbcore_per_child: 1,
            headroom_mb: 16000,
            planner: "test".to_string(),
        }),
        timeout_sec: Some(2.0),
        resource_enforcement: Some(crate::resource::ENFORCEMENT_AY_MEMORY_RSS_V1.to_string()),
    };
    let args = ChcGateArgs {
        manifest: Some(PathBuf::from("m.json")),
        ..test_args(PathBuf::from("out"), PathBuf::from("ay"), 2.0)
    };
    let current_plan = baseline.resource_plan.clone().unwrap();
    let checks = baseline_checks(&[], &baseline, &current_plan, &args);
    assert!(
        checks
            .iter()
            .any(|check| check.name == "baseline-solved-delta" && check.status == "fail"),
        "{checks:?}"
    );
}

#[test]
fn chc_gate_memout_has_distinct_classification_and_summary_bucket() {
    assert_eq!(classify_case("memout", false, false, false), "memout");
    let mut row = CaseRecord {
        schema: CASES_SCHEMA,
        case_id: "mem".to_string(),
        path: "mem.smt2".to_string(),
        solver_input_path: "snapshot-mem.smt2".to_string(),
        input_sha256: "sha256:test".to_string(),
        input_size_bytes: 1,
        category: "LIA".to_string(),
        family: "f".to_string(),
        expected_status: "sat".to_string(),
        expected_source: "manifest".to_string(),
        source: "manifest:m".to_string(),
        status: "memout".to_string(),
        classification: "memout".to_string(),
        solved: false,
        wrong: false,
        invalid: false,
        invalid_reasons: Vec::new(),
        elapsed_s: Some(1.0),
        par2_s: 4.0,
        timed_out: false,
        exit_code: None,
        process_status: "signal: 9".to_string(),
        stats_json_present: false,
        stats_json_path: String::new(),
        validation: ValidationTelemetry::default(),
        transform_memory: TransformMemoryTelemetry::default(),
        route: RouteTelemetry::default(),
        route_counters: BTreeMap::new(),
        required_route_counters: Vec::new(),
        missing_required_route_counters: Vec::new(),
        stdout: String::new(),
        stderr: String::new(),
        command_argv: Vec::new(),
        command_env: BTreeMap::new(),
    };
    let overall = summarize_overall(std::slice::from_ref(&row), false);
    assert_eq!(overall.memout, 1);
    assert_eq!(overall.error, 0);
    let categories = summarize_categories(std::slice::from_ref(&row));
    assert_eq!(categories[0].memout, 1);
    assert_eq!(categories[0].error, 0);
    row.classification = "error".to_string();
    assert_eq!(summarize_overall(&[row], false).error, 1);
}

#[test]
fn chc_gate_baseline_envelope_mismatch_skips_performance_comparison() {
    let baseline = BaselineStats {
        source: "baseline.json".to_string(),
        solved: Some(1),
        par2_total: Some(1.0),
        resource_plan: None,
        timeout_sec: None,
        resource_enforcement: None,
    };
    let args = test_args(PathBuf::from("out"), PathBuf::from("ay"), 1.0);
    let plan = crate::resource::ResourcePlan {
        requested_jobs: 1,
        jobs: 1,
        memlimit_mb_per_child: 1024,
        nbcore_per_child: 1,
        headroom_mb: 16000,
        planner: "test".to_string(),
    };
    let checks = baseline_checks(&[], &baseline, &plan, &args);
    assert_eq!(checks.len(), 1);
    assert_eq!(checks[0].name, "baseline-resource-envelope");
    assert_eq!(checks[0].status, "fail");
    assert!(checks[0].reason.contains("non-comparable"));
}
