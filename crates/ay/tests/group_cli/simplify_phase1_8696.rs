// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `ay simplify` Phase 1 (#8696).
//!
//! Covers the flat `ay simplify FILE` CLI surface, constant folding behaviour,
//! and the `--check-sat` flag.

use ntest::timeout;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_smt2(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_simplify_phase1_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

/// Brief acceptance: input `(assert (= (+ 1 2) x)) (check-sat)` must produce an
/// assertion containing `(= 3 x)` or `(= x 3)`. The `(check-sat)` from the
/// input is dropped because `--check-sat` was not passed.
#[test]
#[timeout(30_000)]
fn simplify_folds_addition_and_strips_check_sat() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "(declare-const x Int)\n(assert (= (+ 1 2) x))\n(check-sat)\n";
    let (path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("simplify")
        .arg(&path)
        .output()
        .expect("spawn ay simplify");

    assert!(
        output.status.success(),
        "ay simplify exited non-zero: status={:?}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("(= 3 x)") || stdout.contains("(= x 3)"),
        "simplified output missing folded equality: {stdout}"
    );
    assert!(
        !stdout.contains("(check-sat)"),
        "unexpected (check-sat) without --check-sat flag: {stdout}"
    );
    assert!(
        stdout.contains("(declare-const x Int)"),
        "declarations must be preserved: {stdout}"
    );
}

/// `--check-sat` re-emits a single `(check-sat)` after the simplified
/// assertions even when the input did not include one.
#[test]
#[timeout(30_000)]
fn simplify_check_sat_flag_emits_trailing_check_sat() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "(declare-const x Int)\n(assert (= (+ 1 2) x))\n";
    let (path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("simplify")
        .arg("--check-sat")
        .arg(&path)
        .output()
        .expect("spawn ay simplify");

    assert!(
        output.status.success(),
        "ay simplify --check-sat exited non-zero: status={:?}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let occurrences = stdout.matches("(check-sat)").count();
    assert_eq!(
        occurrences, 1,
        "expected exactly one (check-sat) with --check-sat: {stdout}"
    );
    assert!(
        stdout
            .lines()
            .last()
            .map(|line| line.trim() == "(check-sat)")
            .unwrap_or(false),
        "(check-sat) should be the final emitted command: {stdout}"
    );
}

/// `--help` must work without any input file so scripts can discover the CLI.
#[test]
#[timeout(30_000)]
fn simplify_help_smoketest() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("simplify")
        .arg("--help")
        .output()
        .expect("spawn ay simplify --help");

    assert!(output.status.success(), "ay simplify --help failed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("--tactic"),
        "help output missing --tactic: {stdout}"
    );
    assert!(
        stdout.contains("--check-sat"),
        "help output missing --check-sat: {stdout}"
    );
    // Phase 2: --assumptions FILE must appear in help.
    assert!(
        stdout.contains("--assumptions"),
        "help output missing --assumptions: {stdout}"
    );
}

/// Phase 2: `propagate-values` substitutes symbol=numeral facts from
/// `--assumptions` into the main assertions. The assumption itself is NOT
/// emitted as an assertion in the output (it's read-only context).
#[test]
#[timeout(30_000)]
fn simplify_assumptions_propagate_values() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let main = "(declare-const x Int)\n(assert (> x 3))\n(assert (< x 10))\n";
    let assumptions = "(declare-const x Int)\n(assert (= x 5))\n";
    let (main_path, _cleanup_main) = write_temp_smt2(main);
    let (assum_path, _cleanup_assum) = write_temp_smt2(assumptions);

    let output = Command::new(ay_path)
        .arg("simplify")
        .arg("--tactic")
        .arg("propagate-values")
        .arg("--assumptions")
        .arg(&assum_path)
        .arg(&main_path)
        .output()
        .expect("spawn ay simplify --tactic propagate-values --assumptions");

    assert!(
        output.status.success(),
        "ay simplify --assumptions exited non-zero: status={:?}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    // `x > 3` with `x = 5` substitution should fold to `(> 5 3)` (the
    // simplify step doesn't fold cross-arg integer comparisons further).
    assert!(
        stdout.contains("(> 5 3)"),
        "expected substituted assertion (> 5 3) in output: {stdout}"
    );
    assert!(
        stdout.contains("(< 5 10)"),
        "expected substituted assertion (< 5 10) in output: {stdout}"
    );
    // Assumption itself must NOT appear as an emitted assertion.
    assert!(
        !stdout.contains("(assert (= x 5))"),
        "assumption must not be emitted as an assertion: {stdout}"
    );
}

/// Phase 2: `ctx-simplify` drops assertions that are strictly implied by an
/// assumption-bound. Without `--assumptions`, the assertion is kept; with
/// the stronger assumption, it must be dropped.
#[test]
#[timeout(30_000)]
fn simplify_assumptions_ctx_simplify_drops_implied() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let main = "(declare-const x Int)\n(assert (> x 3))\n";
    let assumptions = "(declare-const x Int)\n(assert (> x 10))\n";
    let (main_path, _cleanup_main) = write_temp_smt2(main);
    let (assum_path, _cleanup_assum) = write_temp_smt2(assumptions);

    let output = Command::new(ay_path)
        .arg("simplify")
        .arg("--tactic")
        .arg("ctx-simplify")
        .arg("--assumptions")
        .arg(&assum_path)
        .arg(&main_path)
        .output()
        .expect("spawn ay simplify --tactic ctx-simplify --assumptions");

    assert!(
        output.status.success(),
        "ay simplify --tactic ctx-simplify --assumptions exited non-zero: status={:?}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    // The only assertion must be dropped.
    assert!(
        !stdout.contains("(assert"),
        "implied assertion must be dropped by ctx-simplify with assumption: {stdout}"
    );
    // Removal counter is reported in the output header.
    assert!(
        stdout.contains("removed 1 implied assertion"),
        "expected 'removed 1 implied assertion' trace line: {stdout}"
    );
}

/// Phase 2: a missing `--assumptions` file must produce an error with a
/// readable diagnostic, not a panic.
#[test]
#[timeout(30_000)]
fn simplify_assumptions_missing_file_errors_cleanly() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let main = "(declare-const x Int)\n(assert (> x 3))\n";
    let (main_path, _cleanup_main) = write_temp_smt2(main);
    let missing = std::env::temp_dir().join(format!(
        "ay_simplify_phase2_missing_{}.smt2",
        std::process::id()
    ));
    // Do NOT create the file.

    let output = Command::new(ay_path)
        .arg("simplify")
        .arg("--assumptions")
        .arg(&missing)
        .arg(&main_path)
        .output()
        .expect("spawn ay simplify --assumptions <missing>");

    assert!(
        !output.status.success(),
        "ay simplify with missing --assumptions file should have failed: stdout={}",
        String::from_utf8_lossy(&output.stdout)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("assumptions"),
        "stderr should mention assumptions in the error: {stderr}"
    );
}
