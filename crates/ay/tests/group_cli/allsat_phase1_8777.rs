// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the `ay allsat` subcommand (#8777).
//!
//! These tests exercise the DIMACS CNF entry point, SMT-LIB-compatible model
//! emission, `--max-models` capping, and `--projected-vars` projection.

use ntest::timeout;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_cnf(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_allsat_8777_{}_{}.cnf",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp cnf");
    (path.clone(), CleanupGuard(path))
}

/// Count the number of `(model` opening tokens in the CLI output.
fn count_models(stdout: &str) -> usize {
    stdout.lines().filter(|l| l.starts_with("(model")).count()
}

/// `(x1 OR x2) AND (NOT x1 OR NOT x2)` has exactly two satisfying models:
/// `{x1=T, x2=F}` and `{x1=F, x2=T}`. `ay allsat` must emit exactly two
/// `(model ...)` blocks and close with an `exhaustive` comment.
#[test]
#[timeout(30_000)]
fn allsat_enumerates_known_model_count() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
    let (path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(ay_path)
        .arg("allsat")
        .arg(&path)
        .output()
        .expect("spawn ay allsat");

    assert!(
        output.status.success(),
        "ay allsat exited non-zero: status={:?}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        count_models(&stdout),
        2,
        "expected exactly 2 models, got: {stdout}"
    );
    assert!(
        stdout.contains("2 model(s) enumerated (exhaustive)"),
        "missing exhaustive summary line: {stdout}"
    );
    // Both variables must be defined in every model block.
    assert!(
        stdout.contains("(define-fun x1 () Bool"),
        "x1 missing from model output: {stdout}"
    );
    assert!(
        stdout.contains("(define-fun x2 () Bool"),
        "x2 missing from model output: {stdout}"
    );
}

/// DIMACS header variables are part of the formula even when no clause
/// mentions them. They must appear in models and contribute both truth values
/// to full enumeration.
#[test]
#[timeout(30_000)]
fn allsat_enumerates_header_declared_free_variables() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    for (cnf, expected_models) in [("p cnf 2 0\n", 4), ("p cnf 2 1\n1 0\n", 2)] {
        let (path, _cleanup) = write_temp_cnf(cnf);
        let output = Command::new(ay_path)
            .arg("allsat")
            .arg(&path)
            .output()
            .expect("spawn ay allsat");
        assert!(
            output.status.success(),
            "free-variable enumeration failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(count_models(&stdout), expected_models, "{stdout}");
        assert!(
            stdout.contains(&format!(
                "{expected_models} model(s) enumerated (exhaustive)"
            )),
            "{stdout}"
        );
        assert_eq!(
            stdout.matches("(define-fun x2 () Bool").count(),
            expected_models,
            "free x2 must be printed in every model: {stdout}"
        );
        assert!(stdout.contains("(define-fun x2 () Bool false)"), "{stdout}");
        assert!(stdout.contains("(define-fun x2 () Bool true)"), "{stdout}");
    }
}

/// `--max-models 1` truncates enumeration and reports `capped`.
#[test]
#[timeout(30_000)]
fn allsat_max_models_caps_enumeration() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
    let (path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(ay_path)
        .arg("allsat")
        .arg(&path)
        .arg("--max-models")
        .arg("1")
        .output()
        .expect("spawn ay allsat --max-models 1");

    assert!(output.status.success(), "ay allsat --max-models 1 failed");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        count_models(&stdout),
        1,
        "expected cap at 1 model: {stdout}"
    );
    assert!(
        stdout.contains("1 model(s) enumerated (capped)"),
        "missing capped summary line: {stdout}"
    );
}

/// `x1 AND (x2 OR x3)` has three full models but only one projected assignment
/// to `{x1}`: `x1=true`.
#[test]
#[timeout(30_000)]
fn allsat_projected_vars_collapses_duplicates() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 3 2\n1 0\n2 3 0\n";
    let (path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(ay_path)
        .arg("allsat")
        .arg(&path)
        .arg("--projected-vars")
        .arg("1")
        .output()
        .expect("spawn ay allsat --projected-vars 1");

    assert!(
        output.status.success(),
        "ay allsat --projected-vars 1 failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        count_models(&stdout),
        1,
        "projected enumeration should have 1 model: {stdout}"
    );
    assert!(
        stdout.contains("(define-fun x1 () Bool true)"),
        "projected model must pin x1=true: {stdout}"
    );
    // Non-projected vars must NOT appear in the output — the solver only
    // distinguishes models by projected vars, so reporting others would
    // misrepresent the enumeration.
    assert!(
        !stdout.contains("(define-fun x2 ()"),
        "unexpected x2 in projected output: {stdout}"
    );
    assert!(
        !stdout.contains("(define-fun x3 ()"),
        "unexpected x3 in projected output: {stdout}"
    );
}

/// An out-of-range projected variable must produce a user-visible error with
/// a non-zero exit code — not a silent success or panic.
#[test]
#[timeout(30_000)]
fn allsat_rejects_invalid_projected_var() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 2 0\n-1 -2 0\n";
    let (path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(ay_path)
        .arg("allsat")
        .arg(&path)
        .arg("--projected-vars")
        .arg("99")
        .output()
        .expect("spawn ay allsat");

    assert!(
        !output.status.success(),
        "ay allsat should fail on out-of-range projected var"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("exceeds formula variable count"),
        "stderr must explain the invalid projected var: {stderr}"
    );
}
