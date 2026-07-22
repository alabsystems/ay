// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn write_all_events() -> Vec<serde_json::Value> {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("diag.jsonl");
    let writer = DpllDiagnosticWriter::new(path.to_str().expect("utf8 path"), "test::theory")
        .expect("create writer");

    writer.emit_dpll_round(7, "sat", 12, 3, "continue", 11, 2, 0, 4, 9);
    writer.emit_theory_check("propagate", "propagated", Some(2), None, 8);
    writer.emit_eager_propagate(3, 2, "sat", 1, 5);
    writer.emit_theory_split("need_split", 7);
    writer.emit_push(3);
    writer.emit_pop(3, 2);
    writer.emit_solve_summary("sat", 7, 120, 33, 44, 1, 2, 4, 9);

    assert_eq!(writer.finish(), 7);

    let contents = std::fs::read_to_string(&path).expect("read diag file");
    contents
        .lines()
        .map(|line| serde_json::from_str(line).expect("valid JSON line"))
        .collect()
}

#[test]
fn test_header_and_event_count() {
    let lines = write_all_events();
    assert_eq!(lines.len(), 8);
    assert_eq!(lines[0]["type"], "header");
    assert_eq!(lines[0]["tool"], "ay-dpll-diagnostic");
    assert_eq!(lines[0]["theory"], "test::theory");
}

#[test]
fn test_dpll_round_event_schema() {
    let lines = write_all_events();
    let event = &lines[1];
    assert_eq!(event["type"], "dpll_round");
    assert_eq!(event["round"], 7);
    assert_eq!(event["sat_result"], "sat");
    assert_eq!(event["check_result"], "continue");
    assert_eq!(event["propagations_added"], 2);
}

#[test]
fn test_solve_summary_event_schema() {
    let lines = write_all_events();
    let event = lines.last().expect("summary event");
    assert_eq!(event["type"], "solve_summary");
    assert_eq!(event["result"], "sat");
    assert_eq!(event["round_trips"], 7);
    assert_eq!(event["theory_conflicts"], 1);
    assert_eq!(event["theory_propagations"], 2);
}

#[test]
fn test_duration_to_micros_converts() {
    let micros = duration_to_micros(Duration::from_micros(42));
    assert_eq!(micros, 42);
}
