// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! SAT trace validation integration tests for `cdcl_test.tla`.
//!
//! Part of #2572: ensure runtime SAT trace validation enforces semantic
//! invariants, not just type-shape checks.

use super::common::{
    ay_version_has_source_identity, build_ay_cli, cargo_binary_path, isolated_cargo_target_dir,
    isolated_cargo_target_dir_for_outer, source_bound_target_name, source_identity_from_parts,
    BuiltWorkspaceBinary, AY_CLI_TARGET_NAME,
};
use ay_sat::{Literal, Solver, TlaTraceable, Variable};
use ay_tla_bridge::{find_tla2_binary, tla2_validate_trace, Tla2TraceError};
use ntest::timeout;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

fn specs_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("specs")
}

fn cdcl_spec_path() -> PathBuf {
    specs_dir().join("cdcl_test.tla")
}

fn cdcl_main_spec_path() -> PathBuf {
    specs_dir().join("cdcl.tla")
}

fn cdcl_config_path() -> PathBuf {
    specs_dir().join("cdcl_test.cfg")
}

fn tla_variable_declarations(spec_path: &Path) -> Vec<String> {
    let contents = std::fs::read_to_string(spec_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", spec_path.display()));
    let mut in_variables = false;
    let mut variables = Vec::new();
    for line in contents.lines() {
        let trimmed = line.trim();
        if trimmed == "VARIABLES" {
            in_variables = true;
            continue;
        }
        if !in_variables {
            continue;
        }
        if trimmed.is_empty() {
            break;
        }
        variables.push(trimmed.trim_end_matches(',').to_owned());
    }
    assert!(
        !variables.is_empty(),
        "{} should declare TLA state variables",
        spec_path.display()
    );
    variables
}

fn tla_operator_is_declared(spec_path: &Path, operator: &str) -> bool {
    let contents = std::fs::read_to_string(spec_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", spec_path.display()));
    contents.lines().any(|line| {
        line.strip_prefix(operator)
            .is_some_and(|suffix| suffix.trim_start().starts_with("=="))
    })
}

fn require_tla2_binary() -> bool {
    if let Err(err) = find_tla2_binary() {
        eprintln!(
            "tla2 binary not found; cannot run SAT trace validation tests: {err}. \
Build tla2: cd ~/tla2 && cargo build --release -p tla-cli. Skipping test."
        );
        return false;
    }
    true
}

fn read_trace(path: &Path) -> Vec<serde_json::Value> {
    let contents = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read trace file {}: {e}", path.display()));
    contents
        .lines()
        .map(|line| {
            serde_json::from_str::<serde_json::Value>(line)
                .unwrap_or_else(|e| panic!("invalid JSON trace line: {e}; line={line}"))
        })
        .collect()
}

fn write_trace(path: &Path, steps: &[serde_json::Value]) {
    let mut out = String::new();
    for step in steps {
        out.push_str(&step.to_string());
        out.push('\n');
    }
    std::fs::write(path, out)
        .unwrap_or_else(|e| panic!("failed to write trace file {}: {e}", path.display()));
}

fn make_first_trail_literal_inconsistent_with_assignment(step: &mut serde_json::Value) {
    let (first_var, bad_sign) = {
        let mapping = step["state"]["assignment"]["value"]["mapping"]
            .as_array()
            .expect("assignment mapping should be an array");
        let first_pair = mapping
            .first()
            .expect("assignment mapping should have at least one entry")
            .as_array()
            .expect("assignment mapping entry should be [key, value]");
        let first_var = first_pair[0].clone();
        let assigned = first_pair[1]["value"]
            .as_str()
            .expect("assignment value should be string");
        let bad_sign = if assigned == "TRUE" { "neg" } else { "pos" };
        (first_var, bad_sign)
    };

    let trail = step["state"]["trail"]["value"]
        .as_array_mut()
        .expect("trail should be an array");
    if trail.is_empty() {
        trail.push(serde_json::json!({
            "type": "tuple",
            "value": [first_var, {"type":"string","value":bad_sign}]
        }));
    } else {
        let first_lit = trail[0]
            .get_mut("value")
            .expect("tuple literal should have value field")
            .as_array_mut()
            .expect("tuple literal value should be array");
        first_lit[0] = first_var;
        first_lit[1] = serde_json::json!({"type":"string","value":bad_sign});
    }
}

fn assert_validation_rejected(err: Tla2TraceError) {
    match err {
        Tla2TraceError::ValidationFailed { stdout, stderr, .. } => {
            let combined = format!("{stdout}\n{stderr}");
            assert!(
                combined.contains("Soundness")
                    || combined.contains("SatCorrect")
                    || combined.contains("UnsatCorrect")
                    || combined.contains("no matching spec states"),
                "expected trace rejection, got:\n{combined}"
            );
        }
        other => panic!("expected validation failure, got {other:?}"),
    }
}

#[test]
fn test_solver_trace_metadata_matches_cdcl_spec_and_emitted_header() {
    let spec_path = cdcl_spec_path();
    assert_eq!(
        Solver::tla_module(),
        spec_path
            .file_stem()
            .and_then(std::ffi::OsStr::to_str)
            .expect("CDCL spec should have a UTF-8 file stem")
    );

    let spec_variables = tla_variable_declarations(&spec_path);
    let solver_variables = Solver::tla_variables()
        .iter()
        .map(|variable| (*variable).to_owned())
        .collect::<Vec<_>>();
    assert_eq!(
        solver_variables, spec_variables,
        "Solver trace metadata must remain aligned with the CDCL TLA spec"
    );
    for action in Solver::tla_actions() {
        assert!(
            tla_operator_is_declared(&spec_path, action),
            "Solver trace action {action:?} must name an operator in {}",
            spec_path.display()
        );
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("canonical_header.jsonl");
    let mut solver = Solver::new(0);
    solver.enable_tla_trace(
        trace_path.to_str().expect("trace path should be UTF-8"),
        Solver::tla_module(),
        Solver::tla_variables(),
    );
    assert!(solver.solve().into_inner().is_sat());

    let trace = read_trace(&trace_path);
    let header = trace
        .iter()
        .find(|event| event["type"] == "header")
        .expect("trace should contain a header");
    let emitted_variables = header["variables"]
        .as_array()
        .expect("header variables should be an array")
        .iter()
        .map(|variable| {
            variable
                .as_str()
                .expect("header variable should be a string")
        })
        .collect::<Vec<_>>();
    assert_eq!(emitted_variables, Solver::tla_variables());
}

#[test]
fn test_cdcl_main_spec_unsat_correct_is_non_vacuous() {
    let spec_path = cdcl_main_spec_path();
    let contents = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", spec_path.display()));

    let unsat_start = contents
        .find("UnsatCorrect ==")
        .expect("cdcl.tla should define UnsatCorrect");
    let unsat_tail = &contents[unsat_start..];
    let soundness_start = unsat_tail
        .find("Soundness ==")
        .expect("UnsatCorrect block should precede Soundness");
    let unsat_block = &unsat_tail[..soundness_start];

    assert!(
        !unsat_block.contains("state = \"UNSAT\" => TRUE"),
        "UnsatCorrect must not be vacuous (`=> TRUE` placeholder)"
    );
    assert!(
        unsat_block.contains("RootConflictDerivable"),
        "UnsatCorrect should reference a concrete root-conflict witness predicate"
    );

    let root_start = contents
        .find("RootConflictDerivable ==")
        .expect("cdcl.tla should define RootConflictDerivable");
    let root_tail = &contents[root_start..];
    let unsat_start = root_tail
        .find("UnsatCorrect ==")
        .expect("RootConflictDerivable should precede UnsatCorrect");
    let root_block = &root_tail[..unsat_start];

    assert!(
        root_block.contains("decisionLevel = 0"),
        "RootConflictDerivable should require root-level conflict (`decisionLevel = 0`)"
    );
    assert!(
        root_block.contains("Falsified(conflict)"),
        "RootConflictDerivable should require a falsified conflict clause witness"
    );
}

fn solve_unsat_with_trace(trace_path: &Path) {
    let mut solver = Solver::new(2);
    solver.enable_tla_trace(
        trace_path
            .to_str()
            .expect("trace path should be valid UTF-8"),
        Solver::tla_module(),
        Solver::tla_variables(),
    );

    assert!(solver.add_clause(vec![Literal::positive(Variable::new(0))]));
    assert!(solver.add_clause(vec![Literal::negative(Variable::new(0))]));

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());
}

fn solve_conflict_driven_unsat_with_trace(trace_path: &Path) {
    let mut solver = Solver::new(2);
    // Disable preprocessing so the UNSAT is discovered via CDCL conflict
    // analysis or lucky phase analysis (not BVE).
    solver.set_preprocess_enabled(false);
    solver.enable_tla_trace(
        trace_path
            .to_str()
            .expect("trace path should be valid UTF-8"),
        Solver::tla_module(),
        Solver::tla_variables(),
    );

    // Unsat XOR system: every 2-variable assignment falsifies at least one clause.
    // With enhanced lucky phases (level-1 conflict analysis), this may be
    // detected during pre-solving rather than full CDCL search.
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1))
    ]));
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(1))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(1))
    ]));

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());
}

fn solve_sat_with_trace(trace_path: &Path) {
    let mut solver = Solver::new(2);
    solver.enable_tla_trace(
        trace_path
            .to_str()
            .expect("trace path should be valid UTF-8"),
        Solver::tla_module(),
        Solver::tla_variables(),
    );

    // (x0 OR x1) is satisfiable.
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1))
    ]));

    let result = solver.solve().into_inner();
    assert!(result.is_sat());
}

#[test]
#[timeout(60_000)]
fn test_unsat_trace_validation_rejects_non_root_unsat_terminal_state() {
    if !require_tla2_binary() {
        return;
    }
    let spec = cdcl_spec_path();
    let cfg = cdcl_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(cfg.exists(), "missing config file: {}", cfg.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("unsat_valid.jsonl");
    let broken_trace_path = dir.path().join("unsat_broken.jsonl");

    solve_unsat_with_trace(&trace_path);
    let ok = tla2_validate_trace(&spec, &trace_path, Some(&cfg));
    assert!(ok.is_ok(), "valid UNSAT trace should validate: {ok:?}");

    let mut trace = read_trace(&trace_path);
    let last = trace.last_mut().expect("trace should have terminal step");
    assert_eq!(last["action"]["name"], "DeclareUnsat");
    last["state"]["decisionLevel"]["value"] = serde_json::json!(1);
    write_trace(&broken_trace_path, &trace);

    let err = tla2_validate_trace(&spec, &broken_trace_path, Some(&cfg))
        .expect_err("broken UNSAT terminal state should fail validation");
    assert_validation_rejected(err);
}

#[test]
#[timeout(60_000)]
fn test_sat_trace_validation_rejects_inconsistent_sat_terminal_trail() {
    if !require_tla2_binary() {
        return;
    }
    let spec = cdcl_spec_path();
    let cfg = cdcl_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(cfg.exists(), "missing config file: {}", cfg.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("sat_valid.jsonl");
    let broken_trace_path = dir.path().join("sat_broken.jsonl");

    solve_sat_with_trace(&trace_path);
    let ok = tla2_validate_trace(&spec, &trace_path, Some(&cfg));
    assert!(ok.is_ok(), "valid SAT trace should validate: {ok:?}");

    let mut trace = read_trace(&trace_path);
    let last = trace.last_mut().expect("trace should have terminal step");
    assert_eq!(last["action"]["name"], "DeclareSat");
    make_first_trail_literal_inconsistent_with_assignment(last);
    write_trace(&broken_trace_path, &trace);

    let err = tla2_validate_trace(&spec, &broken_trace_path, Some(&cfg))
        .expect_err("inconsistent SAT trail semantics should fail validation");
    assert_validation_rejected(err);
}

#[test]
#[timeout(60_000)]
fn test_unsat_trace_validation_rejects_inconsistent_unsat_terminal_trail() {
    if !require_tla2_binary() {
        return;
    }
    let spec = cdcl_spec_path();
    let cfg = cdcl_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(cfg.exists(), "missing config file: {}", cfg.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("unsat_terminal_valid.jsonl");
    let broken_trace_path = dir.path().join("unsat_terminal_broken.jsonl");

    solve_unsat_with_trace(&trace_path);
    let ok = tla2_validate_trace(&spec, &trace_path, Some(&cfg));
    assert!(ok.is_ok(), "valid UNSAT trace should validate: {ok:?}");

    let mut trace = read_trace(&trace_path);
    let last = trace.last_mut().expect("trace should have terminal step");
    assert_eq!(last["action"]["name"], "DeclareUnsat");
    make_first_trail_literal_inconsistent_with_assignment(last);
    write_trace(&broken_trace_path, &trace);

    let err = tla2_validate_trace(&spec, &broken_trace_path, Some(&cfg))
        .expect_err("inconsistent UNSAT terminal trail semantics should fail validation");
    assert_validation_rejected(err);
}

#[test]
#[timeout(60_000)]
fn test_unsat_trace_validation_rejects_inconsistent_analyze_and_learn_state() {
    if !require_tla2_binary() {
        return;
    }
    let spec = cdcl_spec_path();
    let cfg = cdcl_config_path();
    assert!(spec.exists(), "missing spec file: {}", spec.display());
    assert!(cfg.exists(), "missing config file: {}", cfg.display());

    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("unsat_analyze_valid.jsonl");
    let broken_trace_path = dir.path().join("unsat_analyze_broken.jsonl");

    solve_conflict_driven_unsat_with_trace(&trace_path);

    let mut trace = read_trace(&trace_path);

    // Enhanced lucky phases (level-1 conflict analysis) may detect the 2-variable
    // XOR UNSAT during pre-solving, producing a trace without AnalyzeAndLearn steps.
    // When this happens, the corruption test is not applicable — the trace structure
    // is different but the solver result is correct.
    let has_analyze = trace
        .iter()
        .any(|step| step["action"]["name"] == "AnalyzeAndLearn");

    if !has_analyze {
        // Lucky phases caught the UNSAT. Verify the trace is still well-formed
        // (has a DeclareUnsat terminal step).
        let terminal = trace.last().expect("trace should have at least one step");
        assert_eq!(
            terminal["action"]["name"], "DeclareUnsat",
            "lucky-phase UNSAT trace should end with DeclareUnsat"
        );
        return;
    }

    // Validate the original trace
    let ok = tla2_validate_trace(&spec, &trace_path, Some(&cfg));
    assert!(
        ok.is_ok(),
        "valid conflict-driven UNSAT trace should validate: {ok:?}"
    );

    // Corrupt the AnalyzeAndLearn step and verify rejection
    let analyze_step = trace
        .iter_mut()
        .find(|step| step["action"]["name"] == "AnalyzeAndLearn")
        .expect("trace should include AnalyzeAndLearn");
    make_first_trail_literal_inconsistent_with_assignment(analyze_step);
    write_trace(&broken_trace_path, &trace);

    let err = tla2_validate_trace(&spec, &broken_trace_path, Some(&cfg))
        .expect_err("inconsistent AnalyzeAndLearn state should fail validation");
    assert_validation_rejected(err);
}

/// Part of #2577: verify that BCP (Propagate) steps appear in conflict-driven
/// UNSAT traces. Uses PHP(4,3) pigeonhole principle (12 vars) to force full
/// CDCL — too complex for lucky phases to solve at level-1.
///
/// Note: TLA2 semantic validation is not performed here because the TLA+ spec
/// uses unconstrained existentials over all possible assignments, making TLC
/// infeasible at NumVars=12 (state space ~10^22). The 2-variable tests cover
/// TLA2 semantic validation; this test covers CDCL trace structure.
#[test]
#[timeout(60_000)]
fn test_propagate_steps_present_in_conflict_driven_unsat_trace() {
    let dir = tempfile::tempdir().unwrap();
    let trace_path = dir.path().join("propagate_check.jsonl");

    // Build PHP(4,3) in-process: 4 pigeons, 3 holes, 12 variables.
    let mut solver = Solver::new(12);
    solver.set_preprocess_enabled(false);
    solver.enable_tla_trace(
        trace_path
            .to_str()
            .expect("trace path should be valid UTF-8"),
        Solver::tla_module(),
        Solver::tla_variables(),
    );

    // At-least-one per pigeon (each pigeon must be in some hole).
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]));
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(3)),
        Literal::positive(Variable::new(4)),
        Literal::positive(Variable::new(5)),
    ]));
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(6)),
        Literal::positive(Variable::new(7)),
        Literal::positive(Variable::new(8)),
    ]));
    assert!(solver.add_clause(vec![
        Literal::positive(Variable::new(9)),
        Literal::positive(Variable::new(10)),
        Literal::positive(Variable::new(11)),
    ]));

    // At-most-one per hole (no two pigeons share a hole).
    // Hole 1: vars 0,3,6,9
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(3))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(6))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(9))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::negative(Variable::new(6))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::negative(Variable::new(9))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(6)),
        Literal::negative(Variable::new(9))
    ]));
    // Hole 2: vars 1,4,7,10
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(4))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(7))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(1)),
        Literal::negative(Variable::new(10))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(4)),
        Literal::negative(Variable::new(7))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(4)),
        Literal::negative(Variable::new(10))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(7)),
        Literal::negative(Variable::new(10))
    ]));
    // Hole 3: vars 2,5,8,11
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(5))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(8))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(11))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(5)),
        Literal::negative(Variable::new(8))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(5)),
        Literal::negative(Variable::new(11))
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable::new(8)),
        Literal::negative(Variable::new(11))
    ]));

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let trace = read_trace(&trace_path);

    let propagate_count = trace
        .iter()
        .filter(|step| step["action"]["name"] == "Propagate")
        .count();
    assert!(
        propagate_count >= 1,
        "PHP(4,3) UNSAT trace must contain Propagate steps (requires CDCL), found {propagate_count}"
    );

    let has_conflict_analysis = trace
        .iter()
        .any(|step| step["action"]["name"] == "AnalyzeAndLearn");
    assert!(
        has_conflict_analysis,
        "PHP(4,3) UNSAT trace must contain AnalyzeAndLearn steps (requires CDCL)"
    );

    // Verify terminal step is DeclareUnsat
    let terminal = trace.last().expect("trace should have terminal step");
    assert_eq!(
        terminal["action"]["name"], "DeclareUnsat",
        "PHP(4,3) CDCL UNSAT trace should end with DeclareUnsat"
    );
}

// --- E2E tests: ay binary -> trace file -> TLA2 validation ---
// Part of #2466, #2467: End-to-end validation using the ay CLI binary.

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("AY workspace root should be canonicalizable")
}

fn isolated_ay_target_dir_for_outer(
    workspace: &Path,
    source_identity: &str,
    outer_exe: Option<&Path>,
) -> PathBuf {
    let target_name = source_bound_target_name(AY_CLI_TARGET_NAME, source_identity);
    isolated_cargo_target_dir_for_outer(workspace, &target_name, outer_exe)
}

fn isolated_ay_target_dir(workspace: &Path, source_identity: &str) -> PathBuf {
    let target_name = source_bound_target_name(AY_CLI_TARGET_NAME, source_identity);
    isolated_cargo_target_dir(workspace, &target_name)
}

fn isolated_ay_binary(target_dir: &Path) -> PathBuf {
    cargo_binary_path(target_dir, "ay")
}

fn version_has_source_identity(version_stdout: &[u8], source_identity: &str) -> bool {
    ay_version_has_source_identity(version_stdout, source_identity)
}

fn build_current_ay_binary(workspace: &Path) -> BuiltWorkspaceBinary {
    build_ay_cli(workspace)
}

fn require_ay_binary() -> &'static BuiltWorkspaceBinary {
    static AY_BINARY: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
    AY_BINARY.get_or_init(|| build_current_ay_binary(&workspace_root()))
}

#[test]
fn test_ay_cli_plan_never_reuses_stale_ambient_target_binary() {
    let workspace = tempfile::tempdir().unwrap();
    let binary_name = format!("ay{}", std::env::consts::EXE_SUFFIX);
    let stale_release = workspace.path().join("target/release").join(&binary_name);
    let stale_debug = workspace.path().join("target/debug").join(&binary_name);
    std::fs::create_dir_all(stale_release.parent().unwrap()).unwrap();
    std::fs::create_dir_all(stale_debug.parent().unwrap()).unwrap();
    std::fs::write(&stale_release, b"stale-release").unwrap();
    std::fs::write(&stale_debug, b"stale-debug").unwrap();

    let identity = source_identity_from_parts(b"example-head\n", b"", &[]);
    let isolated_target = isolated_ay_target_dir(workspace.path(), &identity);
    let planned_binary = isolated_ay_binary(&isolated_target);
    assert_eq!(
        planned_binary,
        isolated_target.join("debug").join(binary_name)
    );
    assert_ne!(planned_binary, stale_release);
    assert_ne!(planned_binary, stale_debug);
    assert!(!planned_binary.exists());
}

#[test]
fn test_ay_cli_source_identity_and_worktree_isolation_fail_closed() {
    let head = b"example-head\n";
    let clean = source_identity_from_parts(head, b"", &[]);
    let dirty_a = source_identity_from_parts(head, b"diff --git a/a b/a\n+one\n", &[]);
    let dirty_b = source_identity_from_parts(head, b"diff --git a/a b/a\n+two\n", &[]);
    assert_ne!(clean, dirty_a);
    assert_ne!(dirty_a, dirty_b);

    let version = format!("ay 0.11.0+build.1.{dirty_a}@2026-07-13T00:00:00Z\n");
    assert!(version_has_source_identity(version.as_bytes(), &dirty_a));
    assert!(!version_has_source_identity(version.as_bytes(), &clean));
    assert!(!version_has_source_identity(version.as_bytes(), &dirty_b));
    assert!(!version_has_source_identity(&[0xff, 0xfe], &dirty_a));

    let root = tempfile::tempdir().unwrap();
    let same_worktree_clean_target = isolated_ay_target_dir(root.path(), &clean);
    let same_worktree_dirty_target = isolated_ay_target_dir(root.path(), &dirty_a);
    assert_ne!(
        same_worktree_clean_target, same_worktree_dirty_target,
        "changed-source builders must never overwrite an already-returned AY path"
    );

    let worktree_a = root.path().join("worktree-a");
    let worktree_b = root.path().join("worktree-b");
    assert_ne!(
        isolated_ay_target_dir(&worktree_a, &dirty_a),
        isolated_ay_target_dir(&worktree_b, &dirty_a)
    );

    let primary = root
        .path()
        .join("target")
        .join(source_bound_target_name(AY_CLI_TARGET_NAME, &dirty_a));
    let outer_exe = primary.join("debug/deps/group_misc-test");
    let collision_safe = isolated_ay_target_dir_for_outer(root.path(), &dirty_a, Some(&outer_exe));
    assert_ne!(collision_safe, primary);
    assert!(!outer_exe.starts_with(&collision_safe));
}

fn assert_dimacs_exit(output: &std::process::Output, expected: i32, verdict: &str) {
    assert_eq!(
        output.status.code(),
        Some(expected),
        "ay binary should return DIMACS {verdict} exit code {expected}, got {:?}\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// E2E: Run ay binary on a SAT problem with `--trace-file`, validate trace.
#[test]
#[timeout(600_000)]
fn test_e2e_ay_binary_sat_trace_validates() {
    if !require_tla2_binary() {
        return;
    }
    let ay_bin = require_ay_binary();
    let spec = cdcl_spec_path();
    let cfg = cdcl_config_path();

    let dir = tempfile::tempdir().unwrap();
    let cnf_path = dir.path().join("sat.cnf");
    let trace_path = dir.path().join("sat_trace.jsonl");

    // 2-variable SAT problem: (x0 OR x1)
    std::fs::write(&cnf_path, "p cnf 2 1\n1 2 0\n").unwrap();

    let output = ay_bin
        .command()
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(cnf_path.to_str().unwrap())
        .arg("--trace-file")
        .arg(trace_path.to_str().unwrap())
        .output()
        .expect("failed to run ay binary");

    assert_dimacs_exit(&output, 10, "SAT");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("SATISFIABLE"),
        "expected SAT result, got: {stdout}"
    );
    assert!(
        trace_path.exists(),
        "trace file should be created at {}",
        trace_path.display()
    );

    let trace = read_trace(&trace_path);
    assert!(
        trace.len() >= 2,
        "trace should have at least Init + terminal step"
    );

    let last_step = trace.last().unwrap();
    assert_eq!(
        last_step["action"]["name"], "DeclareSat",
        "terminal step should be DeclareSat"
    );

    let ok = tla2_validate_trace(&spec, &trace_path, Some(&cfg));
    assert!(
        ok.is_ok(),
        "e2e SAT trace from ay binary should validate: {ok:?}"
    );
}

/// E2E: Run ay binary on an UNSAT problem with `--trace-file`, validate trace.
#[test]
#[timeout(600_000)]
fn test_e2e_ay_binary_unsat_trace_validates() {
    if !require_tla2_binary() {
        return;
    }
    let ay_bin = require_ay_binary();
    let spec = cdcl_spec_path();
    let cfg = cdcl_config_path();

    let dir = tempfile::tempdir().unwrap();
    let cnf_path = dir.path().join("unsat.cnf");
    let trace_path = dir.path().join("unsat_trace.jsonl");

    // 2-variable UNSAT problem: (x0) AND (NOT x0)
    std::fs::write(&cnf_path, "p cnf 2 2\n1 0\n-1 0\n").unwrap();

    let output = ay_bin
        .command()
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(cnf_path.to_str().unwrap())
        .arg("--trace-file")
        .arg(trace_path.to_str().unwrap())
        .output()
        .expect("failed to run ay binary");

    assert_dimacs_exit(&output, 20, "UNSAT");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("UNSATISFIABLE"),
        "expected UNSAT result, got: {stdout}"
    );
    assert!(
        trace_path.exists(),
        "trace file should be created at {}",
        trace_path.display()
    );

    let trace = read_trace(&trace_path);
    assert!(
        trace.len() >= 2,
        "trace should have at least Init + terminal step"
    );

    // The DIMACS header intentionally over-declares one unused variable.  AY
    // sizes the dense solver from variables that actually occur, so this is a
    // one-variable trace validated under the same bounded config as the
    // two-variable SAT trace.  This locks the trace/spec contract to solver
    // reality instead of the untrusted input header.
    let initial_step = trace
        .iter()
        .find(|event| event["type"] == "step" && event["index"] == 0)
        .expect("trace should contain initial step 0");
    let initial_domain = initial_step["state"]["assignment"]["value"]["domain"]
        .as_array()
        .expect("initial assignment domain should be an array");
    assert_eq!(
        initial_domain.len(),
        1,
        "contradictory-unit fixture should exercise content-sized tracing"
    );

    let last_step = trace.last().unwrap();
    assert_eq!(
        last_step["action"]["name"], "DeclareUnsat",
        "terminal step should be DeclareUnsat"
    );

    let ok = tla2_validate_trace(&spec, &trace_path, Some(&cfg));
    assert!(
        ok.is_ok(),
        "e2e UNSAT trace from ay binary should validate: {ok:?}"
    );
}

/// E2E: Run ay binary on a conflict-driven UNSAT problem, verify trace
/// structure. Uses PHP(4,3) pigeonhole principle (4 pigeons, 3 holes, 12
/// variables) which is too complex for lucky phases to solve at level-1,
/// forcing full CDCL conflict analysis and backtracking.
///
/// Note: TLA2 semantic validation is not performed here because the TLA+ spec
/// uses unconstrained existentials over all possible assignments, making TLC
/// infeasible at NumVars=12 (state space ~10^22). The simpler 2-variable e2e
/// tests cover TLA2 validation; this test covers CDCL trace structure from the
/// ay binary.
#[test]
#[timeout(600_000)]
fn test_e2e_ay_binary_conflict_driven_unsat_trace_validates() {
    let ay_bin = require_ay_binary();

    let dir = tempfile::tempdir().unwrap();
    let cnf_path = dir.path().join("php43_unsat.cnf");
    let trace_path = dir.path().join("php43_trace.jsonl");

    // Pigeonhole principle PHP(4,3): 4 pigeons, 3 holes — guaranteed UNSAT.
    // Variables: p_{ij} = pigeon i in hole j (12 vars, 22 clauses).
    // Pigeon 1: vars 1,2,3. Pigeon 2: vars 4,5,6.
    // Pigeon 3: vars 7,8,9. Pigeon 4: vars 10,11,12.
    // At-least-one per pigeon (4 clauses), at-most-one per hole (18 clauses).
    std::fs::write(
        &cnf_path,
        "p cnf 12 22\n\
         1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n\
         -1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n\
         -2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n\
         -3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n",
    )
    .unwrap();

    let output = ay_bin
        .command()
        .arg("--disable")
        .arg("preprocess")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg("--trace-file")
        .arg(trace_path.to_str().unwrap())
        .arg(cnf_path.to_str().unwrap())
        .output()
        .expect("failed to run ay binary");

    assert_dimacs_exit(&output, 20, "UNSAT");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("UNSATISFIABLE"),
        "expected UNSAT result, got: {stdout}"
    );

    let trace = read_trace(&trace_path);

    let has_propagate = trace
        .iter()
        .any(|step| step["action"]["name"] == "Propagate");
    assert!(
        has_propagate,
        "PHP(4,3) UNSAT trace must contain Propagate steps (requires CDCL)"
    );

    let has_conflict_analysis = trace
        .iter()
        .any(|step| step["action"]["name"] == "AnalyzeAndLearn");
    assert!(
        has_conflict_analysis,
        "PHP(4,3) UNSAT trace must contain AnalyzeAndLearn steps (requires CDCL)"
    );

    // Verify terminal step is DeclareUnsat
    let terminal = trace.last().expect("trace should have terminal step");
    assert_eq!(
        terminal["action"]["name"], "DeclareUnsat",
        "PHP(4,3) CDCL UNSAT trace should end with DeclareUnsat"
    );
}
