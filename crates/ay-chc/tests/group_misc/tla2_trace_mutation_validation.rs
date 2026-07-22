// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negative/mutation tests for PDR TLA2 traces.
//!
//! Part of #2584: ensure `TLA2 trace validate` rejects semantically corrupted
//! traces, not just malformed JSON.

#[path = "../common/tla2_trace.rs"]
mod tla2_trace;

use ay_chc::PdrResult;
use ay_tla_bridge::tla2_validate_trace_with_timeout;
use std::path::{Path, PathBuf};
use std::time::Duration;
use tla2_trace::{pdr_spec_path, require_tla2_binary, solve_with_trace, specs_dir, unsafe_problem};

/// Timeout for each TLA2 validation subprocess (prevents holding the cargo lock).
const VALIDATION_TIMEOUT: Option<Duration> = Some(Duration::from_secs(30));

fn pdr_config_path() -> PathBuf {
    specs_dir().join("pdr_test_small.cfg")
}

fn read_trace_lines(path: &Path) -> Vec<String> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(ToString::to_string)
        .collect()
}

fn generate_valid_unsafe_trace(
    trace_file: &str,
) -> Option<(tempfile::TempDir, PathBuf, PathBuf, Vec<String>)> {
    if !require_tla2_binary() {
        return None;
    }
    let spec = pdr_spec_path();
    let config = pdr_config_path();

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join(trace_file);

    let result = solve_with_trace(unsafe_problem(), &trace_path);
    assert!(matches!(result, PdrResult::Unsafe(_)));

    let valid =
        tla2_validate_trace_with_timeout(&spec, &trace_path, Some(&config), VALIDATION_TIMEOUT);
    assert!(
        valid.is_ok(),
        "unmodified unsafe trace should validate before mutation: {valid:?}"
    );

    let lines = read_trace_lines(&trace_path);
    assert!(
        lines.len() >= 3,
        "expected at least 3 lines, got {}",
        lines.len()
    );

    Some((dir, spec, config, lines))
}

#[test]
fn test_pdr_trace_rejects_frames_below_minimum() {
    let Some((dir, spec, config, mut lines)) =
        generate_valid_unsafe_trace("pdr_unsafe_frames_base.jsonl")
    else {
        return;
    };

    let mut init_step: serde_json::Value = serde_json::from_str(&lines[1]).unwrap();
    init_step["state"]["frames"]["value"] = serde_json::json!(1);
    lines[1] = serde_json::to_string(&init_step).unwrap();

    let mutated_path = dir.path().join("pdr_unsafe_frames_below_minimum.jsonl");
    std::fs::write(&mutated_path, lines.join("\n")).unwrap();

    let invalid =
        tla2_validate_trace_with_timeout(&spec, &mutated_path, Some(&config), VALIDATION_TIMEOUT);
    assert!(
        invalid.is_err(),
        "frames < 2 mutation should be rejected by TLA2 validation"
    );
}

#[test]
fn test_pdr_trace_rejects_current_level_frame_mismatch() {
    let Some((dir, spec, config, mut lines)) =
        generate_valid_unsafe_trace("pdr_unsafe_current_level_base.jsonl")
    else {
        return;
    };

    let last_idx = lines.len() - 1;
    let mut terminal: serde_json::Value = serde_json::from_str(&lines[last_idx]).unwrap();
    let frames = terminal["state"]["frames"]["value"]
        .as_i64()
        .expect("frames.value should be an integer");
    terminal["state"]["currentLevel"]["value"] = serde_json::json!(frames);
    lines[last_idx] = serde_json::to_string(&terminal).unwrap();

    let mutated_path = dir.path().join("pdr_unsafe_current_level_mismatch.jsonl");
    std::fs::write(&mutated_path, lines.join("\n")).unwrap();

    let invalid =
        tla2_validate_trace_with_timeout(&spec, &mutated_path, Some(&config), VALIDATION_TIMEOUT);
    assert!(
        invalid.is_err(),
        "currentLevel != frames - 1 mutation should be rejected by TLA2 validation"
    );
}

#[test]
fn test_pdr_trace_rejects_non_running_source_for_declare_unsafe() {
    let Some((dir, spec, config, lines)) =
        generate_valid_unsafe_trace("pdr_unsafe_terminal_guard_base.jsonl")
    else {
        return;
    };

    let header = lines[0].clone();
    let mut step0: serde_json::Value = serde_json::from_str(&lines[1]).unwrap();
    step0["index"] = serde_json::json!(0);

    let mut injected_step = step0.clone();
    injected_step["index"] = serde_json::json!(1);
    injected_step["action"] = serde_json::json!({"name": "DeclareUnknown"});
    injected_step["state"]["result"]["value"] = serde_json::json!("Unknown");

    let mut terminal: serde_json::Value = serde_json::from_str(lines.last().unwrap()).unwrap();
    terminal["index"] = serde_json::json!(2);

    let mutated_lines = [
        header,
        serde_json::to_string(&step0).unwrap(),
        serde_json::to_string(&injected_step).unwrap(),
        serde_json::to_string(&terminal).unwrap(),
    ];

    let mutated_path = dir.path().join("pdr_unsafe_terminal_guard_broken.jsonl");
    std::fs::write(&mutated_path, mutated_lines.join("\n")).unwrap();

    let invalid =
        tla2_validate_trace_with_timeout(&spec, &mutated_path, Some(&config), VALIDATION_TIMEOUT);
    assert!(
        invalid.is_err(),
        "DeclareUnsafe from non-Running predecessor should be rejected"
    );
}

#[test]
fn test_pdr_trace_rejects_terminal_obligation_corruption() {
    let Some((dir, spec, config, mut lines)) =
        generate_valid_unsafe_trace("pdr_unsafe_obligation_base.jsonl")
    else {
        return;
    };

    let last_idx = lines.len() - 1;
    let mut terminal: serde_json::Value = serde_json::from_str(&lines[last_idx]).unwrap();
    let obligations = terminal["state"]["obligations"]["value"]
        .as_i64()
        .expect("obligations.value should be an integer");
    terminal["state"]["obligations"]["value"] = serde_json::json!(obligations + 1);
    lines[last_idx] = serde_json::to_string(&terminal).unwrap();

    let mutated_path = dir
        .path()
        .join("pdr_unsafe_corrupt_terminal_obligations.jsonl");
    std::fs::write(&mutated_path, lines.join("\n")).unwrap();

    let invalid =
        tla2_validate_trace_with_timeout(&spec, &mutated_path, Some(&config), VALIDATION_TIMEOUT);
    assert!(
        invalid.is_err(),
        "terminal obligations corruption should be rejected by tla2 validation"
    );
}

/// Negative test: obligations exceeding MaxObligations must be rejected.
/// This verifies that the spec bounds the obligation queue cardinality.
/// Part of #2578.
#[test]
fn test_pdr_trace_rejects_obligations_exceeding_max() {
    let Some((dir, spec, config, mut lines)) =
        generate_valid_unsafe_trace("pdr_unsafe_obligation_overflow_base.jsonl")
    else {
        return;
    };

    // Mutate the init step to have obligations = MaxObligations + 1 (11)
    let mut init_step: serde_json::Value = serde_json::from_str(&lines[1]).unwrap();
    init_step["state"]["obligations"]["value"] = serde_json::json!(11);
    lines[1] = serde_json::to_string(&init_step).unwrap();

    let mutated_path = dir.path().join("pdr_unsafe_obligation_overflow.jsonl");
    std::fs::write(&mutated_path, lines.join("\n")).unwrap();

    let invalid =
        tla2_validate_trace_with_timeout(&spec, &mutated_path, Some(&config), VALIDATION_TIMEOUT);
    assert!(
        invalid.is_err(),
        "obligations exceeding MaxObligations should be rejected by TypeInvariant"
    );
}
