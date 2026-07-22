// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Write all 5 event types to a temp file and return parsed JSONL lines.
fn write_all_event_types() -> Vec<serde_json::Value> {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag.jsonl");
    let writer = SatDiagnosticWriter::new(path.to_str().expect("utf8 path"))
        .expect("create diagnostic writer");

    writer.emit_clause_add(
        1,
        &[1, -2, 3],
        DiagnosticPass::Input,
        ClauseKind::Original,
        &[],
    );
    writer.emit_clause_delete(1, DiagnosticPass::Reduce, DeleteReason::Reduce);
    writer.emit_clause_replace(2, &[1, 3], DiagnosticPass::Vivify);
    writer.emit_var_transition(
        5,
        VarState::Active,
        VarState::Eliminated,
        DiagnosticPass::BVE,
    );
    writer.emit_result_summary(serde_json::json!({"result": "sat"}));

    assert_eq!(writer.finish(), 5);
    let contents = std::fs::read_to_string(&path).expect("read diagnostic file");
    contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect()
}

#[test]
fn test_diagnostic_header_schema() {
    let lines = write_all_event_types();
    assert_eq!(lines.len(), 6); // header + 5 events
    assert_eq!(lines[0]["type"], "header");
    assert_eq!(lines[0]["version"], "1");
    assert_eq!(lines[0]["tool"], "ay-sat-diagnostic");
}

#[test]
fn test_diagnostic_clause_add_event() {
    let lines = write_all_event_types();
    let e = &lines[1];
    assert_eq!(e["type"], "clause_add");
    assert_eq!(e["clause_id"], 1);
    assert_eq!(e["lits"], serde_json::json!([1, -2, 3]));
    assert_eq!(e["pass"], "input");
    assert_eq!(e["kind"], "original");
    assert_eq!(e["parents"], serde_json::json!([]));
}

#[test]
fn test_diagnostic_clause_delete_event() {
    let lines = write_all_event_types();
    let e = &lines[2];
    assert_eq!(e["type"], "clause_delete");
    assert_eq!(e["clause_id"], 1);
    assert_eq!(e["reason_policy"], "reduce");
}

#[test]
fn test_diagnostic_clause_replace_event() {
    let lines = write_all_event_types();
    let e = &lines[3];
    assert_eq!(e["type"], "clause_replace");
    assert_eq!(e["old_clause_id"], 2);
    assert_eq!(e["new_lits"], serde_json::json!([1, 3]));
    assert_eq!(e["parents"], serde_json::json!([2]));
}

#[test]
fn test_diagnostic_var_transition_and_summary() {
    let lines = write_all_event_types();
    let e4 = &lines[4];
    assert_eq!(e4["type"], "var_transition");
    assert_eq!(e4["var"], 5);
    assert_eq!(e4["from"], "active");
    assert_eq!(e4["to"], "eliminated");
    assert_eq!(e4["pass"], "bve");

    let e5 = &lines[5];
    assert_eq!(e5["type"], "result_summary");
    assert_eq!(e5["result"], "sat");
}

#[test]
fn test_diagnostic_restart_event() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag_restart.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");

    writer.emit_restart(42, 100);
    assert_eq!(writer.finish(), 1);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    // header + 1 restart event
    assert_eq!(lines.len(), 2);
    let e = &lines[1];
    assert_eq!(e["type"], "restart");
    assert_eq!(e["num_conflicts"], 42);
    assert_eq!(e["trail_len"], 100);
}

#[test]
fn test_diagnostic_chrono_backtrack_event() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag_chrono.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");

    writer.emit_chrono_backtrack(150, 10, 149);
    assert_eq!(writer.finish(), 1);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    assert_eq!(lines.len(), 2); // header + 1 event
    let e = &lines[1];
    assert_eq!(e["type"], "chrono_backtrack");
    assert_eq!(e["decision_level"], 150);
    assert_eq!(e["jump_level"], 10);
    assert_eq!(e["actual_level"], 149);
}

#[test]
fn test_diagnostic_mode_switch_event() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag_mode.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");

    writer.emit_mode_switch(true, 500, 2000);
    writer.emit_mode_switch(false, 2500, 2000);
    assert_eq!(writer.finish(), 2);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    assert_eq!(lines.len(), 3); // header + 2 events
    let e1 = &lines[1];
    assert_eq!(e1["type"], "mode_switch");
    assert_eq!(e1["mode"], "stable");
    assert_eq!(e1["num_conflicts"], 500);
    assert_eq!(e1["phase_length"], 2000);

    let e2 = &lines[2];
    assert_eq!(e2["type"], "mode_switch");
    assert_eq!(e2["mode"], "focused");
    assert_eq!(e2["num_conflicts"], 2500);
}

#[test]
fn test_diagnostic_incremental_scope_events() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag_scope.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");

    writer.emit_scope_push(1, 7, 0, 42);
    writer.emit_scope_pop(1, 0, 7, true, 42);
    assert_eq!(writer.finish(), 2);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    assert_eq!(lines.len(), 3); // header + 2 events
    let push = &lines[1];
    assert_eq!(push["type"], "scope_push");
    assert_eq!(push["scope_depth"], 1);
    assert_eq!(push["selector_var"], 7);
    assert_eq!(push["restored_clause_count"], 0);
    assert_eq!(push["num_conflicts"], 42);

    let pop = &lines[2];
    assert_eq!(pop["type"], "scope_pop");
    assert_eq!(pop["scope_depth_before"], 1);
    assert_eq!(pop["scope_depth_after"], 0);
    assert_eq!(pop["selector_var"], 7);
    assert_eq!(pop["retracted_empty_clause"], true);
    assert_eq!(pop["num_conflicts"], 42);
}

#[test]
fn test_diagnostic_assumption_events() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag_assumptions.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");

    writer.emit_assumption_batch(2, &[-3, -1], true, 12);
    writer.emit_assumption_result("unsat", Some(1), None, 12);
    assert_eq!(writer.finish(), 2);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    assert_eq!(lines.len(), 3); // header + 2 events
    let batch = &lines[1];
    assert_eq!(batch["type"], "assumption_batch");
    assert_eq!(batch["count"], 2);
    assert_eq!(batch["lits"], serde_json::json!([-3, -1]));
    assert_eq!(batch["composed_with_scope"], true);
    assert_eq!(batch["num_conflicts"], 12);

    let result = &lines[2];
    assert_eq!(result["type"], "assumption_result");
    assert_eq!(result["result"], "unsat");
    assert_eq!(result["core_size"], 1);
    assert_eq!(result["reason"], serde_json::Value::Null);
    assert_eq!(result["num_conflicts"], 12);
}

#[test]
fn test_diagnostic_inprocessing_round_event() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag_inproc.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");

    let telemetry = InprocessingRoundTelemetry {
        bcp_blocker_fastpath_hits: 123,
        bcp_binary_path_hits: 45,
        jumped_reasons: 12,
        bcp_replacement_scan_steps: 678,
        preprocess_level0_literals_removed: 9,
        preprocess_level0_satisfied_deleted: 3,
    };
    writer.emit_inprocessing_round(
        1000,
        500,
        480,
        100,
        &["vivify", "subsume", "bve"],
        &telemetry,
    );
    assert_eq!(writer.finish(), 1);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    let lines: Vec<serde_json::Value> = contents
        .lines()
        .map(|l| serde_json::from_str(l).expect("valid JSON"))
        .collect();

    assert_eq!(lines.len(), 2); // header + 1 event
    let e = &lines[1];
    assert_eq!(e["type"], "inprocessing_round");
    assert_eq!(e["num_conflicts"], 1000);
    assert_eq!(e["clauses_before"], 500);
    assert_eq!(e["clauses_after"], 480);
    assert_eq!(e["clause_delta"], -20);
    assert_eq!(e["vars_active"], 100);
    assert_eq!(e["passes"], serde_json::json!(["vivify", "subsume", "bve"]));
    assert_eq!(e["bcp_blocker_fastpath_hits"], 123);
    assert_eq!(e["bcp_binary_path_hits"], 45);
    assert_eq!(e["jumped_reasons"], 12);
    assert_eq!(e["bcp_replacement_scan_steps"], 678);
    assert_eq!(e["preprocess_level0_literals_removed"], 9);
    assert_eq!(e["preprocess_level0_satisfied_deleted"], 3);
}

#[test]
fn test_diagnostic_writer_empty_trace() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("empty.jsonl");
    let writer =
        SatDiagnosticWriter::new(path.to_str().expect("utf8 path")).expect("create writer");
    let count = writer.finish();
    assert_eq!(count, 0);

    let contents = std::fs::read_to_string(&path).expect("read file");
    assert_eq!(contents.lines().count(), 1); // header only
}
