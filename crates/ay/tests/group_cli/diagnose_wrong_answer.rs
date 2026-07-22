// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the `ay diagnose` subcommand.
//!
//! Verifies that verdict-dispute diagnostics land end-to-end: the subcommand runs
//! ay with `--validate`, composes `--explain` output, detects disagreement
//! against the expected verdict, and returns a non-zero exit code.

use ntest::timeout;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use crate::spawn::OutputTimeout;

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
        "ay_diagnose_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

/// `ay diagnose` on a file where ay returns SAT but the user claims UNSAT
/// must: (a) exit non-zero (specifically 2 for disagreement), (b) print
/// "DECLARED MISMATCH" in the text report, (c) surface the `--explain` constraint
/// verification block so the user can see ay's model.
#[test]
#[timeout(60_000)]
fn diagnose_reports_sat_expected_unsat_conflict() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // A trivially-sat benchmark; we lie about the expected verdict to
    // simulate a wrong-answer scenario without needing a real solver bug.
    let smt2 = "(set-logic QF_LIA)\n\
                (declare-const x Int)\n\
                (assert (>= x 0))\n\
                (assert (<= x 10))\n\
                (check-sat)\n";
    let (path, _cleanup) = write_temp_smt2(smt2);

    let output = Command::new(ay_path)
        .arg("diagnose")
        .arg("--expected")
        .arg("unsat")
        .arg("--reference")
        .arg("none")
        .arg(&path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to run ay diagnose");

    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for sat-vs-expected-unsat disagreement; got {:?}. stdout=\n{}\nstderr=\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ay binary:"),
        "expected ay binary path in diagnose output; got:\n{stdout}"
    );
    assert!(
        stdout.contains("ay build:"),
        "expected ay build summary in diagnose output; got:\n{stdout}"
    );
    assert!(
        stdout.contains("DECLARED MISMATCH"),
        "expected declared-mismatch marker in diagnose output; got:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence conflict"),
        "expected evidence-conflict qualification in summary; got:\n{stdout}"
    );
    assert!(
        stdout.contains("=== Explanation (SAT) ==="),
        "expected --explain constraint-verification block; got:\n{stdout}"
    );
    assert!(
        stdout.contains("Constraint verification:"),
        "expected constraint verification detail; got:\n{stdout}"
    );
}

/// `ay diagnose` on a SAT benchmark with no external label (no `--expected`,
/// `--reference none`) returns exit 0 and prints unscored messaging; the
/// --explain block is still included so the user sees
/// model+constraints.
#[test]
#[timeout(60_000)]
fn diagnose_sat_without_expected_evidence_exits_zero() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt2 = "(set-logic QF_LIA)\n\
                (declare-const x Int)\n\
                (assert (= x 7))\n\
                (check-sat)\n";
    let (path, _cleanup) = write_temp_smt2(smt2);

    let output = Command::new(ay_path)
        .arg("diagnose")
        .arg("--reference")
        .arg("none")
        .arg(&path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to run ay diagnose");

    assert_eq!(
        output.status.code(),
        Some(0),
        "expected exit 0 for unscored case; got {:?}. stderr=\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ay binary:"),
        "expected ay binary path in report; got:\n{stdout}"
    );
    assert!(
        stdout.contains("ay build:"),
        "expected ay build summary in report; got:\n{stdout}"
    );
    assert!(
        stdout.contains("ay verdict:      sat"),
        "expected 'ay verdict:      sat' in report; got:\n{stdout}"
    );
    assert!(
        stdout.contains("=== Explanation (SAT) ==="),
        "expected --explain block even when no disagreement; got:\n{stdout}"
    );
}

/// JSON output must be machine-readable and include the key diagnostic fields.
#[test]
#[timeout(60_000)]
fn diagnose_json_output_contains_expected_keys() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt2 = "(set-logic QF_LIA)\n\
                (declare-const x Int)\n\
                (assert (= x 1))\n\
                (check-sat)\n";
    let (path, _cleanup) = write_temp_smt2(smt2);

    let output = Command::new(ay_path)
        .arg("diagnose")
        .arg("--json")
        .arg("--expected")
        .arg("unsat")
        .arg("--reference")
        .arg("none")
        .arg(&path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to run ay diagnose --json");

    assert_eq!(output.status.code(), Some(2));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
        panic!("failed to parse diagnose --json output: {e}\nstdout:\n{stdout}")
    });
    let expected_binary = std::fs::canonicalize(ay_path)
        .unwrap_or_else(|_| std::path::PathBuf::from(ay_path))
        .display()
        .to_string();

    assert_eq!(parsed["ay"]["verdict"], "sat");
    assert_eq!(
        parsed["ay"]["binary"].as_str(),
        Some(expected_binary.as_str())
    );
    assert!(parsed["ay"]["build"]["summary"].is_string());
    assert!(parsed["ay"]["build"]["stamp"].is_string());
    assert_eq!(parsed["expected"], "unsat");
    assert_eq!(parsed["declared_expected"], "unsat");
    assert_eq!(parsed["expected_dispute"], true);
    assert_eq!(parsed["reference_dispute"], false);
    assert_eq!(parsed["disagreement"], true);
    assert_eq!(parsed["exit_code"], 2);
    assert!(parsed["summary"]
        .as_str()
        .unwrap()
        .contains("evidence conflict"));
    assert!(parsed["explain_output"]
        .as_str()
        .unwrap()
        .contains("Constraint verification"));
}

/// `:status sat` annotation in the file feeds `--expected` automatically.
#[test]
#[timeout(60_000)]
fn diagnose_reads_status_annotation() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let smt2 = "(set-info :status sat)\n\
                (set-logic QF_LIA)\n\
                (declare-const x Int)\n\
                (assert (= x 42))\n\
                (check-sat)\n";
    let (path, _cleanup) = write_temp_smt2(smt2);

    let output = Command::new(ay_path)
        .arg("diagnose")
        .arg("--reference")
        .arg("none")
        .arg(&path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to run ay diagnose");

    assert_eq!(output.status.code(), Some(0));

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("expected:        sat"),
        "expected :status annotation to populate --expected; got:\n{stdout}"
    );
}
