// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for `--trace-file` JSONL output.
//!
//! Validates that the documented CLI flag produces valid TLA2-format JSONL
//! for both SAT (DIMACS) and CHC (PDR) solving paths.

use ntest::timeout;
use std::process::Command;

/// Parse a JSONL trace file into a vec of serde_json::Value.
fn read_trace(path: &std::path::Path) -> Vec<serde_json::Value> {
    let contents = std::fs::read_to_string(path).expect("trace file should exist");
    contents
        .lines()
        .map(|line| serde_json::from_str(line).expect("each line should be valid JSON"))
        .collect()
}

#[test]
#[timeout(30_000)]
fn test_sat_trace_file_produces_valid_jsonl() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();

    let cnf_path = temp_dir.join(format!("ay_trace_test_sat_{pid}.cnf"));
    let trace_path = temp_dir.join(format!("ay_trace_test_sat_{pid}.jsonl"));

    // Simple SAT instance: (x1 OR x2) AND (NOT x1 OR NOT x2)
    std::fs::write(&cnf_path, "p cnf 2 2\n1 2 0\n-1 -2 0\n").unwrap();

    let output = Command::new(ay_path)
        .arg(&cnf_path)
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg("--trace-file")
        .arg(&trace_path)
        .output()
        .expect("failed to spawn ay");

    let _ = std::fs::remove_file(&cnf_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(10),
        "expected SAT exit code 10, got {:?}: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("SATISFIABLE"),
        "expected SAT, got: {stdout}"
    );

    // Validate trace file
    assert!(trace_path.exists(), "trace file was not created");
    let trace = read_trace(&trace_path);
    let _ = std::fs::remove_file(&trace_path);

    assert!(
        trace.len() >= 3,
        "expected header + initial step + terminal step, got {} lines",
        trace.len()
    );

    // Header validation
    let header = &trace[0];
    assert_eq!(header["type"], "header", "first line should be header");
    assert_eq!(header["module"], "cdcl_test");
    assert_eq!(header["version"], "1");
    let vars = header["variables"]
        .as_array()
        .expect("variables should be array");
    assert_eq!(vars.len(), 5, "CDCL trace should have 5 variables");

    // Initial step (index 0, no action)
    let step0 = &trace[1];
    assert_eq!(step0["type"], "step");
    assert_eq!(step0["index"], 0);
    assert!(
        step0.get("action").is_none(),
        "initial step should have no action"
    );
    assert!(step0.get("state").is_some(), "step should have state");

    // Terminal step should have DeclareSat action
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareSat");
    assert_eq!(last["state"]["state"]["value"], "SAT");

    // Step indices should be sequential
    for (i, step) in trace.iter().skip(1).enumerate() {
        assert_eq!(step["index"], i, "step index mismatch at position {i}");
    }
}

#[test]
#[timeout(30_000)]
fn test_unsat_trace_file_produces_valid_jsonl() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();

    let cnf_path = temp_dir.join(format!("ay_trace_test_unsat_{pid}.cnf"));
    let trace_path = temp_dir.join(format!("ay_trace_test_unsat_{pid}.jsonl"));

    // Simple UNSAT instance: (x1) AND (NOT x1)
    std::fs::write(&cnf_path, "p cnf 1 2\n1 0\n-1 0\n").unwrap();

    let output = Command::new(ay_path)
        .arg(&cnf_path)
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg("--trace-file")
        .arg(&trace_path)
        .output()
        .expect("failed to spawn ay");

    let _ = std::fs::remove_file(&cnf_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT exit code 20, got {:?}: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("UNSATISFIABLE"),
        "expected UNSAT, got: {stdout}"
    );

    // Validate trace file
    assert!(trace_path.exists(), "trace file was not created");
    let trace = read_trace(&trace_path);
    let _ = std::fs::remove_file(&trace_path);

    assert!(trace.len() >= 3, "expected at least 3 lines");

    // Header
    assert_eq!(trace[0]["type"], "header");
    assert_eq!(trace[0]["module"], "cdcl_test");

    // Terminal step should have DeclareUnsat action
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareUnsat");
    assert_eq!(last["state"]["state"]["value"], "UNSAT");
}

#[test]
#[timeout(30_000)]
fn test_no_trace_file_without_cli_flag_even_if_env_is_set() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();

    let cnf_path = temp_dir.join(format!("ay_trace_test_none_{pid}.cnf"));
    let trace_path = temp_dir.join(format!("ay_trace_test_none_{pid}.jsonl"));

    // Ensure trace file does not exist before running
    let _ = std::fs::remove_file(&trace_path);

    std::fs::write(&cnf_path, "p cnf 2 2\n1 2 0\n-1 -2 0\n").unwrap();

    let output = Command::new(ay_path)
        .arg(&cnf_path)
        .env("AY_TRACE_FILE", &trace_path)
        .output()
        .expect("failed to spawn ay");

    let _ = std::fs::remove_file(&cnf_path);

    // SAT competition exit code: 10 = SAT
    assert_eq!(output.status.code(), Some(10));

    // No trace file should be created
    assert!(
        !trace_path.exists(),
        "trace file should NOT be created without --trace-file, even if AY_TRACE_FILE is set"
    );
}

#[test]
#[timeout(30_000)]
fn test_smt_trace_file_produces_valid_jsonl() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();

    let smt_path = temp_dir.join(format!("ay_trace_test_smt_{pid}.smt2"));
    let trace_path = temp_dir.join(format!("ay_trace_test_smt_{pid}.jsonl"));

    // Simple QF_LIA problem
    let smt_input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    std::fs::write(&smt_path, smt_input).unwrap();

    let output = Command::new(ay_path)
        .arg(&smt_path)
        .arg("--trace-file")
        .arg(&trace_path)
        .output()
        .expect("failed to spawn ay");

    let _ = std::fs::remove_file(&smt_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.starts_with("sat"), "expected sat, got: {stdout}");

    // Validate trace file
    assert!(trace_path.exists(), "SMT trace file was not created");
    let trace = read_trace(&trace_path);
    let _ = std::fs::remove_file(&trace_path);

    assert!(
        trace.len() >= 3,
        "expected header + initial step + terminal step, got {} lines",
        trace.len()
    );

    // Header validation (should use CDCL module since DPLL(T) wraps SAT)
    let header = &trace[0];
    assert_eq!(header["type"], "header");
    assert_eq!(header["module"], "cdcl_test");
    assert_eq!(header["version"], "1");

    // Terminal step should have DeclareSat
    let last = trace.last().unwrap();
    assert_eq!(last["action"]["name"], "DeclareSat");
    assert_eq!(last["state"]["state"]["value"], "SAT");
}

#[test]
#[timeout(60_000)]
fn test_chc_trace_file_produces_valid_jsonl() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();

    let smt_path = temp_dir.join(format!("ay_trace_test_chc_{pid}.smt2"));
    let trace_path = temp_dir.join(format!("ay_trace_test_chc_{pid}.jsonl"));

    // Simple CHC problem: Inv(x) with x >= 0, init x = 0, query x < 0
    // Expected: SAT (safe)
    let chc_input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    std::fs::write(&smt_path, chc_input).unwrap();

    let output = Command::new(ay_path)
        .arg(&smt_path)
        .arg("--trace-file")
        .arg(&trace_path)
        .output()
        .expect("failed to spawn ay");

    let _ = std::fs::remove_file(&smt_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.starts_with("sat"), "expected sat, got: {stdout}");

    // Validate trace file
    assert!(trace_path.exists(), "CHC trace file was not created");
    let trace = read_trace(&trace_path);
    let _ = std::fs::remove_file(&trace_path);

    assert!(
        trace.len() >= 2,
        "expected at least header + terminal step, got {} lines",
        trace.len()
    );

    // Header validation
    let header = &trace[0];
    assert_eq!(header["type"], "header");
    assert_eq!(header["module"], "pdr_test");
    let vars = header["variables"]
        .as_array()
        .expect("variables should be array");
    assert_eq!(
        vars.len(),
        8,
        "PDR trace should have 8 variables (including obligation identity)"
    );

    // Terminal step should be DeclareSafe (Inv is x >= 0)
    let last = trace.last().unwrap();
    let action_name = last["action"]["name"].as_str().unwrap_or("");
    assert!(
        action_name == "DeclareSafe"
            || action_name == "DeclareUnsafe"
            || action_name == "DeclareUnknown",
        "terminal action should be a Declare* action, got: {action_name}"
    );
    assert_eq!(
        last["state"]["result"]["value"], "Safe",
        "expected Safe result for this problem"
    );

    // Verify all steps have valid TLA2 value encoding
    for (i, step) in trace.iter().skip(1).enumerate() {
        assert_eq!(step["type"], "step", "line {} should be a step", i + 1);
        let state = step.get("state").expect("step should have state");
        // Check that all 8 PDR trace variables are present
        for var in [
            "frames",
            "obligations",
            "currentLevel",
            "result",
            "lemmaCount",
            "activePredicate",
            "activeLevel",
            "obligationDepth",
        ] {
            assert!(
                state.get(var).is_some(),
                "step {i} missing variable '{var}'"
            );
        }
    }
}

#[test]
#[timeout(60_000)]
fn test_chc_flag_trace_file_produces_valid_jsonl() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_dir = std::env::temp_dir();
    let pid = std::process::id();

    let smt_path = temp_dir.join(format!("ay_trace_test_chc_flag_{pid}.smt2"));
    let trace_path = temp_dir.join(format!("ay_trace_test_chc_flag_{pid}.jsonl"));

    let chc_input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    std::fs::write(&smt_path, chc_input).unwrap();

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg(&smt_path)
        .arg("--trace-file")
        .arg(&trace_path)
        .output()
        .expect("failed to spawn ay");

    let _ = std::fs::remove_file(&smt_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.starts_with("sat"), "expected sat, got: {stdout}");

    assert!(trace_path.exists(), "CHC --chc trace file was not created");
    let trace = read_trace(&trace_path);
    let _ = std::fs::remove_file(&trace_path);

    assert!(
        trace.len() >= 2,
        "expected at least header + terminal step, got {} lines",
        trace.len()
    );
    assert_eq!(trace[0]["type"], "header");
    assert_eq!(trace[0]["module"], "pdr_test");

    let last = trace.last().unwrap();
    assert_eq!(
        last["state"]["result"]["value"], "Safe",
        "expected Safe result for this problem"
    );
}
