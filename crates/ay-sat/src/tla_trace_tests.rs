// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_tla_trace_writer_produces_valid_jsonl() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("trace.jsonl");
    let writer = TlaTraceWriter::new(
        path.to_str().unwrap(),
        "cdcl_test",
        &["assignment", "state", "decisionLevel"],
    );

    // Step 0: initial state (no action)
    writer.write_step(
        serde_json::json!({
            "assignment": {"type": "string", "value": "all_undef"},
            "state": {"type": "string", "value": "PROPAGATING"},
            "decisionLevel": {"type": "int", "value": 0},
        }),
        None,
    );

    // Step 1: Propagate action
    writer.write_step(
        serde_json::json!({
            "assignment": {"type": "string", "value": "v1=FALSE"},
            "state": {"type": "string", "value": "PROPAGATING"},
            "decisionLevel": {"type": "int", "value": 0},
        }),
        Some("Propagate"),
    );

    let steps = writer.finish();
    assert_eq!(steps, 2);

    // Verify each line is valid JSON with correct structure
    let contents = std::fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert_eq!(lines.len(), 3); // header + 2 steps

    // Header line
    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["type"], "header");
    assert_eq!(header["version"], "1");
    assert_eq!(header["module"], "cdcl_test");
    assert_eq!(
        header["variables"],
        serde_json::json!(["assignment", "state", "decisionLevel"])
    );

    // Step 0: no action
    let step0: serde_json::Value = serde_json::from_str(lines[1]).unwrap();
    assert_eq!(step0["type"], "step");
    assert_eq!(step0["index"], 0);
    assert!(step0.get("state").is_some());
    assert!(step0.get("action").is_none());

    // Step 1: has action
    let step1: serde_json::Value = serde_json::from_str(lines[2]).unwrap();
    assert_eq!(step1["type"], "step");
    assert_eq!(step1["index"], 1);
    assert_eq!(step1["action"]["name"], "Propagate");
}

#[test]
fn test_tla_trace_writer_empty_trace() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("empty.jsonl");
    let writer = TlaTraceWriter::new(path.to_str().unwrap(), "test", &["x"]);
    let steps = writer.finish();
    assert_eq!(steps, 0);

    let contents = std::fs::read_to_string(&path).unwrap();
    assert_eq!(contents.lines().count(), 1); // header only
}

#[test]
fn test_tla_trace_step_indices_are_sequential() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("seq.jsonl");
    let writer = TlaTraceWriter::new(path.to_str().unwrap(), "test", &["s"]);

    for i in 0..5 {
        let action = if i == 0 { None } else { Some("Step") };
        writer.write_step(
            serde_json::json!({"s": {"type": "int", "value": i}}),
            action,
        );
    }
    writer.finish();

    let contents = std::fs::read_to_string(&path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    // header + 5 steps
    assert_eq!(lines.len(), 6);

    for (i, line) in lines[1..].iter().enumerate() {
        let step: serde_json::Value = serde_json::from_str(line).unwrap();
        assert_eq!(step["index"], i);
    }
}
