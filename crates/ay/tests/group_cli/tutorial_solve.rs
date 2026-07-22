// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay tutorial solve` integration tests (#8692).
//!
//! Covers the educational `ay tutorial solve <file>` path:
//!
//! * SAT input → "SATISFIABLE" banner, model block, and a
//!   per-assertion back-substitution section that prints each rule with
//!   model values plugged in and confirms it evaluates to True.
//! * UNSAT input → "UNSATISFIABLE" banner and a plain-English hint
//!   listing the contradicting rules.
//! * `ay tutorial` (no args) → prints the welcome banner without error.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn temp_path(extension: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_tutorial_solve_{}_{}.{}",
        std::process::id(),
        file_id,
        extension
    ));
    (path.clone(), CleanupGuard(path))
}

fn write_temp(contents: &str, extension: &str) -> (PathBuf, CleanupGuard) {
    let (path, cleanup) = temp_path(extension);
    std::fs::write(&path, contents).expect("write temp input");
    (path, cleanup)
}

fn run_ay(args: &[&str]) -> std::process::Output {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    Command::new(ay_path)
        .args(args)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay")
}

fn help_lists_command(help: &str, command: &str) -> bool {
    help.lines()
        .any(|line| line.trim_start().starts_with(&format!("{command} ")))
}

#[test]
#[timeout(30_000)]
fn test_public_help_shows_tutorial_without_internal_commands() {
    let output = run_ay(&["--help"]);
    assert!(output.status.success(), "ay --help failed");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(help_lists_command(&stdout, "tutorial"), "{stdout}");
    assert!(help_lists_command(&stdout, "diagnose"), "{stdout}");

    for command in [
        "bench",
        "corpus",
        "tool",
        "z3-audit",
        "scripts",
        "competition-jit",
        "gate",
        "consumer-smoke",
        "launch-gate",
        "release",
        "launch-packet",
        "submission",
        "verifier-audit",
        "bisect",
    ] {
        assert!(!help_lists_command(&stdout, command), "{stdout}");
    }
}

#[test]
#[timeout(60_000)]
fn test_tutorial_solve_sat_shows_back_substitution() {
    // SAT input with two assertions. Tutorial output must:
    //   1. Identify the result as SATISFIABLE.
    //   2. Print a model block.
    //   3. For each rule, print the original body and the body with model
    //      values substituted, then confirm it evaluates to True.
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (> x y))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
(get-model)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&["tutorial", "solve", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay tutorial solve failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stdout.contains("Result: SATISFIABLE"),
        "expected SATISFIABLE banner, got: {stdout}"
    );
    assert!(
        stdout.contains("Model (variable assignments)"),
        "expected model block, got: {stdout}"
    );
    assert!(
        stdout.contains("Checking the model against each rule"),
        "expected back-substitution header, got: {stdout}"
    );
    // The first rule includes `(+ x y)` — after substitution it must contain
    // a `(+` with numeric values, not the literal symbols.
    assert!(
        stdout.contains("Rule 1: (= (+ x y) 10)"),
        "expected original Rule 1 text, got: {stdout}"
    );
    assert!(
        stdout.contains("with model: (= (+ "),
        "expected substituted rule 1, got: {stdout}"
    );
    // Every rule must be confirmed to evaluate to True.
    let true_count = stdout.matches("evaluates to True").count();
    assert!(
        true_count >= 4,
        "expected at least 4 'evaluates to True' confirmations (one per rule), got {true_count}: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn test_tutorial_solve_unsat_explains_contradiction() {
    // UNSAT input: x > 10 AND x < 0. Tutorial mode must:
    //   1. Say UNSATISFIABLE in plain English.
    //   2. List the rules so the user can see the contradiction.
    let smt = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 0))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&["tutorial", "solve", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay tutorial solve failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stdout.contains("Result: UNSATISFIABLE"),
        "expected UNSATISFIABLE banner, got: {stdout}"
    );
    assert!(
        stdout.contains("No answer exists"),
        "expected plain-English UNSAT line, got: {stdout}"
    );
    assert!(
        stdout.contains("The rules were:"),
        "expected rules listing for small UNSAT, got: {stdout}"
    );
    assert!(
        stdout.contains("(> x 10)") && stdout.contains("(< x 0)"),
        "expected both contradicting rules to be listed, got: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn test_tutorial_welcome_runs_without_file() {
    // `ay tutorial` with no args prints the welcome banner + a quick example.
    let output = run_ay(&["tutorial"]);
    assert!(
        output.status.success(),
        "ay tutorial failed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("AY tutorial"),
        "expected welcome banner, got: {stdout}"
    );
    assert!(
        stdout.contains("ay tutorial --interactive"),
        "expected tutorial hint, got: {stdout}"
    );
}
