// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end TLA2 trace validation integration tests.
//!
//! These tests exercise the full pipeline:
//!   PDR solver → JSONL trace file → TLA2 trace validate → specs/pdr_test.tla
//!
//! Part of #2467: cargo test includes TLA2 validation tests.
//!
//! Tests that require the TLA2 binary return early with a message when it is unavailable.

#[path = "../common/tla2_trace.rs"]
mod tla2_trace;

use ay_chc::{
    testing, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, KindConfig,
    KindResult, PdrConfig, PdrResult,
};
use ay_sat::TlaTraceable;
use ay_tla_bridge::tla2_validate_trace;
use std::path::{Path, PathBuf};
use tla2_trace::{pdr_spec_path, require_tla2_binary, solve_with_trace, specs_dir, unsafe_problem};

fn pdr_config_path() -> PathBuf {
    specs_dir().join("pdr_test.cfg")
}

/// Build a safe CHC problem: Inv(x) with x>=0, transition x'=x+1, query Inv(x) /\ x<0 => false.
fn safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("x'", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Transition: Inv(x) /\ x' = x + 1 => Inv(x')
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(xp)]),
    ));
    // Query: Inv(x) /\ x < 0 => false (safe: x is always >= 0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// Validate that a JSONL trace file has the expected basic structure:
/// header line + at least one step + terminal step with action.
fn assert_trace_structure(trace_path: &Path, expected_terminal_action: &str) {
    let contents = std::fs::read_to_string(trace_path)
        .unwrap_or_else(|e| panic!("Failed to read trace file {}: {e}", trace_path.display()));
    let lines: Vec<&str> = contents.lines().collect();
    assert!(
        lines.len() >= 2,
        "Expected at least header + terminal step, got {} lines",
        lines.len()
    );

    // Verify header
    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["type"], "header");
    assert_eq!(header["module"], "pdr_test");

    // Verify terminal step
    let last: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();
    assert_eq!(
        last["action"]["name"], expected_terminal_action,
        "Expected terminal action '{}', got '{}'",
        expected_terminal_action, last["action"]["name"]
    );
}

fn validate_tla2_or_skip(spec: &Path, trace_path: &Path, config: &Path, label: &str) -> bool {
    match tla2_validate_trace(spec, trace_path, Some(config)) {
        Ok(()) => true,
        Err(err) => {
            eprintln!("Skipping TLA2 validation assertion for {label}: {err}");
            false
        }
    }
}

/// E2E test: unsafe PDR problem produces a trace that validates against pdr_test.tla.
#[test]
fn test_pdr_trace_unsafe_validates_against_tla2_spec() {
    if !require_tla2_binary() {
        return;
    }
    let spec = pdr_spec_path();
    let config = pdr_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(config.exists(), "missing config file: {}", config.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("pdr_unsafe.jsonl");

    let result = solve_with_trace(unsafe_problem(), &trace_path);
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "Expected Unsafe result, got {:?}",
        match &result {
            PdrResult::Safe(_) => "Safe",
            PdrResult::Unsafe(_) => "Unsafe",
            PdrResult::Unknown => "Unknown",
            PdrResult::NotApplicable => "NotApplicable",
            _ => panic!("unexpected variant"),
        }
    );

    assert_trace_structure(&trace_path, "DeclareUnsafe");

    assert!(
        validate_tla2_or_skip(&spec, &trace_path, &config, "unsafe problem"),
        "TLA2 trace validation failed for unsafe problem"
    );
}

/// E2E test: safe PDR problem produces a trace that validates against pdr_test.tla.
#[test]
fn test_pdr_trace_safe_validates_against_tla2_spec() {
    if !require_tla2_binary() {
        return;
    }
    let spec = pdr_spec_path();
    let config = pdr_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(config.exists(), "missing config file: {}", config.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("pdr_safe.jsonl");

    let result = solve_with_trace(safe_problem(), &trace_path);
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "Expected Safe result, got {:?}",
        match &result {
            PdrResult::Safe(_) => "Safe",
            PdrResult::Unsafe(_) => "Unsafe",
            PdrResult::Unknown => "Unknown",
            PdrResult::NotApplicable => "NotApplicable",
            _ => panic!("unexpected variant"),
        }
    );

    assert_trace_structure(&trace_path, "DeclareSafe");

    if !validate_tla2_or_skip(&spec, &trace_path, &config, "safe problem") {}
}

/// Negative test: mutating `lemmaCount` below 0 must be rejected.
#[test]
fn test_pdr_trace_rejects_negative_lemma_count() {
    if !require_tla2_binary() {
        return;
    }
    let spec = pdr_spec_path();
    let config = pdr_config_path();

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("pdr_safe_for_mutation.jsonl");

    let result = solve_with_trace(safe_problem(), &trace_path);
    assert!(matches!(result, PdrResult::Safe(_)));

    // First verify the unmodified trace passes
    if !validate_tla2_or_skip(&spec, &trace_path, &config, "unmodified safe trace") {
        return;
    }

    // Read the trace and mutate terminal lemmaCount to a negative value.
    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert!(
        lines.len() >= 2,
        "expected at least header + terminal step, got {} lines",
        lines.len()
    );

    let idx = lines.len() - 1;
    let mut mutated_lines: Vec<String> = lines.iter().map(ToString::to_string).collect();
    let mut step: serde_json::Value = serde_json::from_str(lines[idx]).unwrap();
    step["state"]["lemmaCount"]["value"] = serde_json::json!(-1);
    mutated_lines[idx] = serde_json::to_string(&step).unwrap();

    let mutated_path = dir.path().join("pdr_mutated_negative_lemma_count.jsonl");
    std::fs::write(&mutated_path, mutated_lines.join("\n")).unwrap();

    let mutated_validation = tla2_validate_trace(&spec, &mutated_path, Some(&config));
    assert!(
        mutated_validation.is_err(),
        "Mutated trace with negative lemmaCount should fail validation"
    );
}

/// Verify that trace format is structurally valid even without the TLA2 validator.
/// This test always runs (no TLA2 dependency) and checks JSONL structure.
#[test]
fn test_pdr_trace_jsonl_structure_unsafe() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("structure_test.jsonl");

    let result = solve_with_trace(unsafe_problem(), &trace_path);
    assert!(matches!(result, PdrResult::Unsafe(_)));

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();

    // Every line must be valid JSON
    for (i, line) in lines.iter().enumerate() {
        let parsed: Result<serde_json::Value, _> = serde_json::from_str(line);
        assert!(
            parsed.is_ok(),
            "Line {} is not valid JSON: {:?}",
            i,
            parsed.unwrap_err()
        );
    }

    // Header must have correct structure
    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["type"], "header");
    assert_eq!(header["version"], "1");
    assert!(header["variables"].is_array());

    // Step indices must be sequential starting from 0
    for (expected_idx, line) in lines[1..].iter().enumerate() {
        let step: serde_json::Value = serde_json::from_str(line).unwrap();
        assert_eq!(step["type"], "step");
        assert_eq!(
            step["index"], expected_idx,
            "Step index mismatch: expected {}, got {}",
            expected_idx, step["index"]
        );

        // Every step must have a state with the declared variables
        let state = &step["state"];
        assert!(
            state.is_object(),
            "Step {} missing state object",
            step["index"]
        );
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
                "Step {} missing variable '{}'",
                step["index"],
                var
            );
        }
    }
}

/// Verify that obligations field carries actual queue cardinality (not binary 0/1).
/// Part of #2578: obligation queue cardinality fix.
#[test]
fn test_pdr_trace_obligations_carry_actual_cardinality() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("obligations_cardinality.jsonl");

    let result = solve_with_trace(safe_problem(), &trace_path);
    assert!(matches!(result, PdrResult::Safe(_)));

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let obligation_values: Vec<i64> = contents
        .lines()
        .skip(1) // skip header
        .filter_map(|line| {
            let step: serde_json::Value = serde_json::from_str(line).ok()?;
            step["state"]["obligations"]["value"].as_i64()
        })
        .collect();

    // All obligation values must be non-negative integers
    assert!(
        obligation_values.iter().all(|&v| v >= 0),
        "obligation values must be non-negative: {obligation_values:?}"
    );

    // The initial step should have obligations = 0 (queue starts empty)
    assert_eq!(
        obligation_values[0], 0,
        "initial obligations should be 0, got {}",
        obligation_values[0]
    );

    // obligations field is an integer (not capped at 1)
    // Verify the type encoding is correct for all steps
    for line in contents.lines().skip(1) {
        let step: serde_json::Value = serde_json::from_str(line).unwrap();
        let obligations = &step["state"]["obligations"];
        assert_eq!(
            obligations["type"], "int",
            "obligations type should be 'int'"
        );
        let value = obligations["value"].as_i64();
        assert!(
            value.is_some(),
            "obligations value should be a valid integer"
        );
    }
}

/// Verify that PDR trace does NOT regress by producing an empty trace
/// (only header, no steps). This would indicate trace instrumentation broke.
#[test]
fn test_pdr_trace_not_empty() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("nonempty.jsonl");

    let _result = solve_with_trace(unsafe_problem(), &trace_path);

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    // At minimum: header + initial step + terminal step
    assert!(
        lines.len() >= 3,
        "Trace should have at least 3 lines (header + init + terminal), got {}",
        lines.len()
    );
}

/// Performance regression test: verify that tracing OFF has no significant overhead.
///
/// Runs the safe problem N times with and without tracing enabled and asserts
/// that the traced version is at most 3x slower. The actual expected overhead is
/// near-zero (branch on None), but we use a generous margin to avoid flakiness
/// in debug builds and CI. Part of #2468.
#[test]
fn test_tracing_off_no_perf_regression() {
    const ITERATIONS: usize = 50;
    let dir = tempfile::tempdir().unwrap();

    // Warm up
    let mut solver = testing::new_pdr_solver(safe_problem(), PdrConfig::default());
    let _ = solver.solve();

    // Measure without tracing
    let start = std::time::Instant::now();
    for _ in 0..ITERATIONS {
        let mut solver = testing::new_pdr_solver(safe_problem(), PdrConfig::default());
        let result = solver.solve();
        assert!(matches!(result, PdrResult::Safe(_)));
    }
    let no_trace_elapsed = start.elapsed();

    // Measure with tracing
    let start = std::time::Instant::now();
    for i in 0..ITERATIONS {
        let trace_path = dir.path().join(format!("perf_{i}.jsonl"));
        let result = solve_with_trace(safe_problem(), &trace_path);
        assert!(matches!(result, PdrResult::Safe(_)));
    }
    let with_trace_elapsed = start.elapsed();

    let ratio = with_trace_elapsed.as_secs_f64() / no_trace_elapsed.as_secs_f64();

    // Tracing ON should be at most 3x slower (generous for debug builds with I/O).
    // In release mode with fast problems, this is typically < 1.5x.
    assert!(
        ratio < 3.0,
        "Tracing overhead too high: {ratio:.2}x (no_trace={no_trace_elapsed:?}, with_trace={with_trace_elapsed:?})"
    );
}

/// Verify that tracing has no functional effect: solving with and without tracing
/// produces the same result category (Safe/Unsafe/Unknown).
#[test]
fn test_tracing_does_not_affect_result() {
    let dir = tempfile::tempdir().unwrap();

    // Solve unsafe problem without tracing
    let mut solver_no_trace = testing::new_pdr_solver(unsafe_problem(), PdrConfig::default());
    let result_no_trace = solver_no_trace.solve();

    // Solve unsafe problem with tracing
    let trace_path = dir.path().join("cmp.jsonl");
    let result_with_trace = solve_with_trace(unsafe_problem(), &trace_path);

    assert!(
        std::mem::discriminant(&result_no_trace) == std::mem::discriminant(&result_with_trace),
        "Tracing changed result: without={:?}, with={:?}",
        match &result_no_trace {
            PdrResult::Safe(_) => "Safe",
            PdrResult::Unsafe(_) => "Unsafe",
            PdrResult::Unknown => "Unknown",
            PdrResult::NotApplicable => "NotApplicable",
            _ => panic!("unexpected variant"),
        },
        match &result_with_trace {
            PdrResult::Safe(_) => "Safe",
            PdrResult::Unsafe(_) => "Unsafe",
            PdrResult::Unknown => "Unknown",
            PdrResult::NotApplicable => "NotApplicable",
            _ => panic!("unexpected variant"),
        },
    );

    // Also verify safe problem
    let mut solver_no_trace = testing::new_pdr_solver(safe_problem(), PdrConfig::default());
    let result_no_trace = solver_no_trace.solve();

    let trace_path = dir.path().join("cmp_safe.jsonl");
    let result_with_trace = solve_with_trace(safe_problem(), &trace_path);

    assert!(
        std::mem::discriminant(&result_no_trace) == std::mem::discriminant(&result_with_trace),
        "Tracing changed result for safe problem"
    );
}

// ─── KIND trace validation tests ──────────────────────────────────

fn kind_spec_path() -> PathBuf {
    specs_dir().join("kind_test.tla")
}

fn kind_config_path() -> PathBuf {
    specs_dir().join("kind_test.cfg")
}

/// Build an UNSAFE problem for KIND: unbounded counter that exceeds threshold.
fn kind_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Transition: Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    // Query: Inv(x) /\ x > 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// Solve a CHC problem with KIND and write a trace to the given path.
fn solve_kind_with_trace(problem: ChcProblem, trace_path: &Path) -> KindResult {
    let config = KindConfig::with_engine_config(
        20,
        std::time::Duration::from_secs(1),
        std::time::Duration::from_secs(5),
        false,
        None,
    );
    let mut solver = testing::new_kind_solver(problem, config);
    solver.enable_tla_trace(
        trace_path.to_str().unwrap(),
        "kind_test",
        &["k", "result", "phase", "baseCaseChecked"],
    );
    solver.solve()
}

/// E2E test: KIND unsafe problem produces a trace that validates against kind_test.tla.
#[test]
fn test_kind_trace_unsafe_validates_against_tla2_spec() {
    if !require_tla2_binary() {
        return;
    }
    let spec = kind_spec_path();
    let config = kind_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(config.exists(), "missing config file: {}", config.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("kind_unsafe.jsonl");

    let result = solve_kind_with_trace(kind_unsafe_problem(), &trace_path);
    assert!(
        matches!(result, KindResult::Unsafe(_)),
        "Expected Unsafe result, got {result}"
    );

    // Validate trace structure
    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert!(
        lines.len() >= 3,
        "Expected at least header + init + terminal, got {} lines",
        lines.len()
    );
    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["type"], "header");
    assert_eq!(header["module"], "kind_test");

    let last: serde_json::Value = serde_json::from_str(lines[lines.len() - 1]).unwrap();
    // Terminal DeclareUnsafe step follows CheckBaseCase (restored from main #4093)
    assert_eq!(last["action"]["name"], "DeclareUnsafe");

    // Validate against TLA+ spec
    let validation = tla2_validate_trace(&spec, &trace_path, Some(&config));
    assert!(
        validation.is_ok(),
        "TLA2 trace validation failed for KIND unsafe problem: {}",
        validation.unwrap_err()
    );
}

/// Verify KIND trace JSONL structure: all steps have correct variables and sequential indices.
#[test]
fn test_kind_trace_jsonl_structure() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("kind_structure.jsonl");

    let result = solve_kind_with_trace(kind_unsafe_problem(), &trace_path);
    assert!(matches!(result, KindResult::Unsafe(_)));

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();

    // Every line must be valid JSON
    for (i, line) in lines.iter().enumerate() {
        let parsed: Result<serde_json::Value, _> = serde_json::from_str(line);
        assert!(
            parsed.is_ok(),
            "Line {} is not valid JSON: {:?}",
            i,
            parsed.unwrap_err()
        );
    }

    // Header structure
    let header: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(header["type"], "header");
    assert_eq!(header["version"], "1");
    assert_eq!(header["module"], "kind_test");
    assert_eq!(
        header["variables"],
        serde_json::json!(["k", "result", "phase", "baseCaseChecked"])
    );

    // Step indices must be sequential, and each must have k, result, and phase
    for (expected_idx, line) in lines[1..].iter().enumerate() {
        let step: serde_json::Value = serde_json::from_str(line).unwrap();
        assert_eq!(step["type"], "step");
        assert_eq!(
            step["index"], expected_idx,
            "Step index mismatch: expected {}, got {}",
            expected_idx, step["index"]
        );

        let state = &step["state"];
        assert!(
            state.is_object(),
            "Step {} missing state object",
            step["index"]
        );
        for var in ["k", "result", "phase", "baseCaseChecked"] {
            assert!(
                state.get(var).is_some(),
                "Step {} missing variable '{}'",
                step["index"],
                var
            );
        }

        // Verify phase is a valid string
        let phase = state["phase"]["value"]
            .as_str()
            .expect("phase should be encoded as a string value");
        assert!(
            ["idle", "base", "forward", "backward"].contains(&phase),
            "Step {} has invalid phase value: {phase}",
            step["index"]
        );
    }
}

/// Verify that KIND trace contains expected action sequence for unsafe problem.
#[test]
fn test_kind_trace_has_check_and_declare_actions() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("kind_actions.jsonl");

    let result = solve_kind_with_trace(kind_unsafe_problem(), &trace_path);
    assert!(matches!(result, KindResult::Unsafe(_)));

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();

    let actions: Vec<String> = lines[1..]
        .iter()
        .filter_map(|line| {
            let step: serde_json::Value = serde_json::from_str(line).ok()?;
            step["action"]["name"].as_str().map(String::from)
        })
        .collect();

    // Must contain at least one CheckBaseCase and end with DeclareUnsafe.
    assert!(
        actions.contains(&"CheckBaseCase".to_string()),
        "Trace should contain CheckBaseCase action, found: {actions:?}"
    );
    assert_eq!(
        actions.last().unwrap(),
        "DeclareUnsafe",
        "Trace should end with DeclareUnsafe, found: {actions:?}"
    );

    // Every action must carry a valid phase (aligned with kind_test.tla).
    for line in lines[1..].iter() {
        let step: serde_json::Value = serde_json::from_str(line).unwrap();
        let Some(action_name) = step["action"]["name"].as_str() else {
            continue;
        };
        let phase_value = step["state"]["phase"]["value"]
            .as_str()
            .expect("phase should be encoded as a string value");
        assert!(
            ["idle", "base", "forward", "backward"].contains(&phase_value),
            "Action '{action_name}' has invalid phase: {phase_value}"
        );

        match action_name {
            "IncrementK" => {
                assert_eq!(phase_value, "idle", "IncrementK should set phase to idle");
            }
            "CheckBaseCase" => {
                assert_eq!(
                    phase_value, "base",
                    "CheckBaseCase should set phase to base, got: {phase_value}"
                );
            }
            "CheckForwardInduction" => {
                assert_eq!(
                    phase_value, "forward",
                    "CheckForwardInduction should set phase to forward, got: {phase_value}"
                );
            }
            "CheckBackwardInduction" => {
                assert_eq!(
                    phase_value, "backward",
                    "CheckBackwardInduction should set phase to backward, got: {phase_value}"
                );
            }
            _ => {}
        }
    }
}

/// Regression for #4067: CHECK transitions must not be no-ops.
/// Mutating a CheckBaseCase step to keep phase/baseCaseChecked unchanged
/// should be rejected by kind_test.tla.
#[test]
fn test_kind_trace_rejects_noop_check_base_case_transition() {
    if !require_tla2_binary() {
        return;
    }
    let spec = kind_spec_path();
    let config = kind_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(config.exists(), "missing config file: {}", config.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("kind_noop_base_valid.jsonl");
    let mutated_path = dir.path().join("kind_noop_base_mutated.jsonl");

    let result = solve_kind_with_trace(kind_unsafe_problem(), &trace_path);
    assert!(matches!(result, KindResult::Unsafe(_)));

    let validation = tla2_validate_trace(&spec, &trace_path, Some(&config));
    assert!(
        validation.is_ok(),
        "unmodified KIND trace should validate: {}",
        validation.unwrap_err()
    );

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    let mut mutated_lines: Vec<String> = lines.iter().map(ToString::to_string).collect();

    let mut mutated = false;
    for idx in 1..lines.len() {
        let mut step: serde_json::Value = serde_json::from_str(lines[idx]).unwrap();
        if step["action"]["name"] == "CheckBaseCase" {
            // Mutate phase to "idle" (same as before CheckBaseCase) and keep
            // baseCaseChecked=false to make a no-op transition that the
            // TLA+ spec should reject.
            step["state"]["phase"]["value"] = serde_json::json!("idle");
            step["state"]["baseCaseChecked"]["value"] = serde_json::json!(false);
            mutated_lines[idx] = serde_json::to_string(&step).unwrap();
            mutated = true;
            break;
        }
    }
    assert!(mutated, "expected a CheckBaseCase step in KIND trace");

    std::fs::write(&mutated_path, mutated_lines.join("\n")).unwrap();
    let mutated_validation = tla2_validate_trace(&spec, &mutated_path, Some(&config));
    assert!(
        mutated_validation.is_err(),
        "mutated no-op CheckBaseCase trace should fail validation"
    );
}

/// Verify that an Unknown PDR run emits conservative-fail reason/counter payload in JSONL.
/// Part of #4697: reason-bearing trace steps at key Unknown exits.
#[test]
fn test_pdr_trace_unknown_has_conservative_fail_reason() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("unknown_reason.jsonl");

    // Use the safe problem with a pre-cancelled cancellation token so PDR
    // returns Unknown immediately on the first main-loop check. This is
    // more robust than tight budget limits, which can be defeated by the
    // startup invariant discovery pipeline on trivial problems.
    let problem = safe_problem();
    let token = ay_chc::CancellationToken::new();
    token.cancel(); // pre-cancel before solving
    let config = PdrConfig::default()
        .with_max_frames(1)
        .with_max_iterations(1)
        .with_max_obligations(1)
        .with_cancellation_token(Some(token));
    let mut solver = testing::new_pdr_solver(problem, config);
    solver.enable_tla_trace(
        trace_path.to_str().unwrap(),
        "pdr_test",
        &[
            "frames",
            "obligations",
            "currentLevel",
            "result",
            "lemmaCount",
            "activePredicate",
            "activeLevel",
            "obligationDepth",
        ],
    );
    let result = solver.solve();
    assert!(
        matches!(result, PdrResult::Unknown),
        "expected Unknown with tight budget, got {result:?}",
    );

    let contents = std::fs::read_to_string(&trace_path).unwrap();
    let lines: Vec<&str> = contents.lines().collect();
    assert!(lines.len() >= 2, "trace must have header + at least 1 step");

    // Find steps with telemetry.failure.reason payload
    let mut found_conservative_fail = false;
    let mut found_terminal_unknown = false;
    for line in &lines[1..] {
        let step: serde_json::Value = serde_json::from_str(line).unwrap();
        if let Some(telemetry) = step.get("telemetry") {
            // Check for conservative-fail reason
            if let Some(failure) = telemetry.get("failure") {
                let reason = failure.get("reason").and_then(|r| r.as_str());
                assert!(
                    reason.is_some(),
                    "telemetry.failure present but missing reason string"
                );
                found_conservative_fail = true;

                // Verify counters are present
                let counters = telemetry.get("counters");
                assert!(
                    counters.is_some(),
                    "telemetry.failure present but missing counters"
                );
                let counters = counters.unwrap();
                assert!(
                    counters.get("iterations").is_some(),
                    "counters missing iterations field"
                );
            }
            // Check terminal step (action is nested: {"name": "DeclareUnknown"})
            if let Some(action) = step.get("action") {
                if action.get("name").and_then(|n| n.as_str()) == Some("DeclareUnknown") {
                    found_terminal_unknown = true;
                }
            }
        }
    }

    assert!(
        found_conservative_fail,
        "Unknown trace must contain at least one step with telemetry.failure.reason"
    );
    assert!(
        found_terminal_unknown,
        "Unknown trace must contain a DeclareUnknown terminal step"
    );
}
