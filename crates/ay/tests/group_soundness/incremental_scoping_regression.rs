// Incremental scoping regression tests for #1432
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// These tests verify soundness of the "reused Boolean subterm across scopes"
// pattern. When an assertion is popped, its cached Tseitin/BV variables must
// still have their definitional clauses active if those variables can appear
// in future assertions.
//
// Expected behavior: first check-sat returns sat, second returns unsat.
// Unsound behavior: both return sat (cached var unconstrained after pop).
//
// Reference: the development design notes

use ntest::timeout;
use std::path::PathBuf;
use std::process::{Command, ExitStatus};

#[derive(Debug)]
struct AYIncrementalRun {
    smt_file: String,
    benchmark_path: PathBuf,
    results: Vec<String>,
    status: ExitStatus,
    stdout: String,
    stderr: String,
}

impl AYIncrementalRun {
    fn context(&self) -> String {
        format!(
            "file={}\npath={}\nresults={:?}\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
            self.smt_file,
            self.benchmark_path.display(),
            self.results,
            self.status,
            self.stdout,
            self.stderr
        )
    }
}

fn run_ay_incremental(smt_file: &str) -> AYIncrementalRun {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("CARGO_MANIFEST_DIR should be <workspace>/crates/ay");
    let benchmark_path = workspace_root
        .join("benchmarks")
        .join("smt")
        .join("regression")
        .join("incremental_scoping")
        .join(smt_file);

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    // Collect sat/unsat/unknown responses.
    let results = stdout
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            trimmed == "sat" || trimmed == "unsat" || trimmed == "unknown"
        })
        .map(|s| s.trim().to_string())
        .collect();

    AYIncrementalRun {
        smt_file: smt_file.to_string(),
        benchmark_path,
        results,
        status: output.status,
        stdout,
        stderr,
    }
}

fn assert_sat_then_unsat(run: &AYIncrementalRun) {
    assert!(
        run.status.success(),
        "Expected ay to exit successfully.\n{}",
        run.context()
    );
    assert_eq!(
        run.results.len(),
        2,
        "Expected 2 check-sat results.\n{}",
        run.context()
    );
    assert_eq!(
        run.results[0],
        "sat",
        "First check-sat should be sat.\n{}",
        run.context()
    );
    assert_eq!(
        run.results[1],
        "unsat",
        "Second check-sat should be unsat (not spurious sat from unconstrained cached var).\n{}",
        run.context()
    );
}

/// QF_UF: Reused Boolean subterm across scopes
///
/// Part of #1432 - Tseitin caching soundness
/// The subterm (and a b) is introduced in scope 1, then reused in scope 2
/// with (not a), which should be UNSAT.
#[test]
#[timeout(60000)]
fn test_qf_uf_reused_subterm() {
    let run = run_ay_incremental("qf_uf_reused_subterm.smt2");
    assert_sat_then_unsat(&run);
}

/// QF_LRA: Reused Boolean subterm across scopes
///
/// Part of #1432 - Tseitin caching soundness with LRA theory
/// The subterm (and (>= x 0.0) (< x 1.0)) is introduced in scope 1,
/// then reused in scope 2 with (< x 0.0), which should be UNSAT.
#[test]
#[timeout(60000)]
fn test_qf_lra_reused_subterm() {
    let run = run_ay_incremental("qf_lra_reused_subterm.smt2");
    assert_sat_then_unsat(&run);
}

/// QF_LIA: Reused Boolean subterm across scopes
///
/// Part of #1432 - Tseitin caching soundness with LIA theory
/// The subterm (and (>= x 0) (< x 1)) is introduced in scope 1,
/// then reused in scope 2 with (< x 0), which should be UNSAT.
#[test]
#[timeout(60000)]
fn test_qf_lia_reused_subterm() {
    let run = run_ay_incremental("qf_lia_reused_subterm.smt2");
    assert_sat_then_unsat(&run);
}

/// QF_BV: Reused Boolean subterm across scopes
///
/// Part of #1432 - BV caching soundness
/// The subterm (and (= x #x00) (distinct x #x01)) is introduced in scope 1,
/// then reused in scope 2 with (distinct x #x00), which should be UNSAT.
#[test]
#[timeout(60000)]
fn test_qf_bv_reused_subterm() {
    let run = run_ay_incremental("qf_bv_reused_subterm.smt2");
    assert_sat_then_unsat(&run);
}

/// QF_BV: Reused *internal* BV subterm across scopes (#1454)
///
/// Tests BV arithmetic operations (bvadd) that generate their own
/// bitblasting circuits, as opposed to simple Boolean predicates.
/// The internal subterm (bvadd x #x01) is introduced in scope 1,
/// then reused in scope 2 with a contradiction.
#[test]
#[timeout(60000)]
fn test_qf_bv_internal_subterm() {
    let run = run_ay_incremental("qf_bv_internal_subterm.smt2");
    assert_sat_then_unsat(&run);
}

/// QF_BV: Multiple internal BV subterms across scopes (#1454)
///
/// Tests multiple BV operations (bvadd, bvand, concat) that generate
/// their own bitblasting circuits. Exercises deeper caching scenarios.
#[test]
#[timeout(60000)]
fn test_qf_bv_internal_subterm_multi() {
    let run = run_ay_incremental("qf_bv_internal_subterm_multi.smt2");
    // Expected: sat, sat, sat, unsat
    assert!(
        run.status.success(),
        "Expected ay to exit successfully.\n{}",
        run.context()
    );
    assert_eq!(
        run.results.len(),
        4,
        "Expected 4 check-sat results.\n{}",
        run.context()
    );
    assert_eq!(
        run.results[0],
        "sat",
        "Test 1 (bvadd) should be sat.\n{}",
        run.context()
    );
    assert_eq!(
        run.results[1],
        "sat",
        "Test 2 (bvand) should be sat.\n{}",
        run.context()
    );
    assert_eq!(
        run.results[2],
        "sat",
        "Test 3 (concat) should be sat.\n{}",
        run.context()
    );
    assert_eq!(
        run.results[3],
        "unsat",
        "Test 4 (reused bvadd contradiction) should be unsat.\n{}",
        run.context()
    );
}
