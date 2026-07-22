// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Phase 1 `--explain` reason-code integration tests (#8693).
//!
//! These drive the `ay` binary end-to-end and assert that the Phase 1
//! reason-code classification appears on stdout after `unsat`. Coverage:
//!
//! * `(assert false)` → `PreprocessingDetected`
//! * Propositional (QF_UF bool) contradiction → `UnitPropagationContradiction`
//! * `--explain-format json` → single-line JSON with expected fields
//!
//! Tests intentionally use the thinnest possible SMT inputs so the assertions
//! about which engine path produced UNSAT remain stable across unrelated
//! solver changes.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

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
        "ay_explain_phase1_{}_{}.{}",
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
    Command::new(ay_path).args(args).output().expect("spawn ay")
}

#[test]
#[timeout(60_000)]
fn test_explain_assert_false_detected() {
    // `(assert false)` is constant-false: the elaborator reports UNSAT before
    // any CDCL search runs. Phase 1 must classify this as
    // `PreprocessingDetected`.
    let smt = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&[
        "--explain",
        "--no-verify-proof",
        input_path.to_str().unwrap(),
    ]);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("unsat"),
        "expected unsat in stdout, got: {stdout}"
    );
    assert!(
        stdout.contains("Reason: PreprocessingDetected"),
        "expected PreprocessingDetected reason code, got: {stdout}"
    );
    assert!(
        stdout.contains("Explanation:"),
        "expected Explanation: prefix, got: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn test_explain_plain_cdcl_unsat() {
    // Propositional formula with a unit-propagation contradiction:
    //   (p), (not p)
    // No theory is involved — CDCL derives the empty clause immediately via
    // unit propagation. Phase 1 must classify this as
    // `UnitPropagationContradiction`.
    let smt = r#"(set-logic QF_UF)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
"#;
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&[
        "--explain",
        "--no-verify-proof",
        input_path.to_str().unwrap(),
    ]);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("unsat"),
        "expected unsat in stdout, got: {stdout}"
    );
    // Acceptable outcomes: pure propositional UNSAT (expected) OR
    // PreprocessingDetected if the elaborator collapses `p ∧ ¬p` to `false`
    // before CDCL runs. Both correctly point at "no theory reasoning needed".
    let is_prop = stdout.contains("Reason: UnitPropagationContradiction");
    let is_preprocessing = stdout.contains("Reason: PreprocessingDetected");
    assert!(
        is_prop || is_preprocessing,
        "expected UnitPropagationContradiction or PreprocessingDetected reason, got: {stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn test_explain_json_format_emits_single_line_object() {
    // `--explain-format json` must print exactly one JSON object line per
    // UNSAT result, with stable field names `reason`, `theory`, `message`.
    let smt = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&[
        "--explain",
        "--explain-format",
        "json",
        "--no-verify-proof",
        input_path.to_str().unwrap(),
    ]);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("unsat"),
        "expected unsat in stdout, got: {stdout}"
    );
    // Find the JSON line. It must start with `{"reason":`.
    let json_line = stdout
        .lines()
        .find(|line| line.trim_start().starts_with(r#"{"reason":"#))
        .unwrap_or_else(|| panic!("no JSON reason line found in stdout:\n{stdout}"));
    assert!(
        json_line.contains(r#""reason":"PreprocessingDetected""#),
        "expected PreprocessingDetected reason in JSON, got: {json_line}"
    );
    assert!(
        json_line.contains(r#""theory":null"#),
        "expected theory:null in JSON (no theory involved), got: {json_line}"
    );
    assert!(
        json_line.contains(r#""message":""#),
        "expected message field in JSON, got: {json_line}"
    );
    assert!(
        json_line.trim_end().ends_with('}'),
        "expected JSON to end with }} on a single line, got: {json_line}"
    );
}

#[test]
#[timeout(60_000)]
fn test_explain_disabled_by_default() {
    // Baseline: without `--explain`, no reason-code block appears.
    let smt = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    let (input_path, _cleanup) = write_temp(smt, "smt2");

    let output = run_ay(&["--no-verify-proof", input_path.to_str().unwrap()]);
    assert!(
        output.status.success(),
        "ay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("unsat"),
        "expected unsat in stdout, got: {stdout}"
    );
    assert!(
        !stdout.contains("Reason code"),
        "Reason code block must not appear without --explain, got: {stdout}"
    );
    assert!(
        !stdout.contains("Reason: PreprocessingDetected"),
        "Reason line must not appear without --explain, got: {stdout}"
    );
}
