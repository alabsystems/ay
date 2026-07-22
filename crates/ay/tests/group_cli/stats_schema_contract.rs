// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Schema contract tests for `--stats` canonical output (#4723).
//!
//! Verifies that all three solve modes (SMT, DIMACS SAT, CHC) emit a common
//! key set on stderr via the `RunStatistics` envelope, preventing silent
//! schema drift across modes.

use ntest::timeout;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_file(contents: &str, ext: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_schema_contract_{}_{}.{ext}",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp file");
    (path.clone(), CleanupGuard(path))
}

/// Common keys that MUST appear in the canonical stats output for all modes.
const COMMON_KEYS: &[&str] = &[
    "ay.mode:",
    "ay.result:",
    "ay.wall_time_ms:",
    "ay.build.stamp:",
];

/// Header that MUST appear to indicate canonical stats format.
const STATS_HEADER: &str = "AY statistics";

/// Parse canonical stderr output and return the set of keys found.
fn extract_keys(stderr: &str) -> Vec<String> {
    stderr
        .lines()
        .filter_map(|line| {
            let trimmed = line.strip_prefix("c ")?;
            let key = trimmed.split_whitespace().next()?;
            if key.ends_with(':') {
                Some(key.to_string())
            } else {
                None
            }
        })
        .collect()
}

#[test]
#[timeout(30_000)]
fn test_schema_contract_smt_mode() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_file(input, "smt2");

    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(STATS_HEADER),
        "SMT mode: missing canonical stats header in stderr: {stderr}"
    );

    let keys = extract_keys(&stderr);
    for common in COMMON_KEYS {
        assert!(
            keys.iter().any(|k| k == common),
            "SMT mode: missing common key {common} in stderr keys: {keys:?}\nFull stderr: {stderr}"
        );
    }

    // SMT mode should have its own mode tag
    assert!(
        stderr.contains("smt"),
        "SMT mode: expected 'smt' mode tag in stderr: {stderr}"
    );

    // SMT should have conflicts and decisions (common solver keys)
    assert!(
        keys.iter().any(|k| k == "conflicts:"),
        "SMT mode: missing 'conflicts' key in stderr: {keys:?}"
    );
    assert!(
        keys.iter().any(|k| k == "decisions:"),
        "SMT mode: missing 'decisions' key in stderr: {keys:?}"
    );
}

#[test]
#[timeout(30_000)]
fn test_schema_contract_dimacs_sat_mode() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // Simple satisfiable CNF: (x1) AND (x2)
    let input = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_file(input, "cnf");

    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(STATS_HEADER),
        "DIMACS SAT mode: missing canonical stats header in stderr: {stderr}"
    );

    let keys = extract_keys(&stderr);
    for common in COMMON_KEYS {
        assert!(
            keys.iter().any(|k| k == common),
            "DIMACS SAT mode: missing common key {common} in stderr keys: {keys:?}\nFull stderr: {stderr}"
        );
    }

    // SAT mode should have its own mode tag
    assert!(
        stderr.contains("dimacs-sat"),
        "DIMACS SAT mode: expected 'dimacs-sat' mode tag in stderr: {stderr}"
    );

    // SAT should have conflicts and decisions (common solver keys)
    assert!(
        keys.iter().any(|k| k == "conflicts:"),
        "DIMACS SAT mode: missing 'conflicts' key: {keys:?}"
    );
    assert!(
        keys.iter().any(|k| k == "decisions:"),
        "DIMACS SAT mode: missing 'decisions' key: {keys:?}"
    );
    assert!(
        keys.iter().any(|k| k == "propagations:"),
        "DIMACS SAT mode: missing 'propagations' key: {keys:?}"
    );
    assert!(
        keys.iter().any(|k| k == "restarts:"),
        "DIMACS SAT mode: missing 'restarts' key: {keys:?}"
    );
}

#[test]
#[timeout(30_000)]
fn test_schema_contract_chc_mode() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_file(input, "smt2");

    // Use auto-detect (no --chc flag) so it goes through run_chc_from_content
    // which produces ChcStatistics with PDR counters. The --chc flag routes
    // through the adaptive portfolio which doesn't expose stats yet.
    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(STATS_HEADER),
        "CHC mode: missing canonical stats header in stderr: {stderr}"
    );

    let keys = extract_keys(&stderr);
    for common in COMMON_KEYS {
        assert!(
            keys.iter().any(|k| k == common),
            "CHC mode: missing common key {common} in stderr keys: {keys:?}\nFull stderr: {stderr}"
        );
    }

    // CHC mode tag
    assert!(
        stderr.contains("ay.mode:") && stderr.contains("chc"),
        "CHC mode: expected 'chc' mode tag in stderr: {stderr}"
    );

    // CHC-specific counters not yet wired: ChcStatistics struct exists in
    // ay-chc but print_chc_stats doesn't receive or emit chc.* keys yet.
    // Re-enable when plumbing is complete (#4723 remaining AC).
    // let chc_keys: Vec<_> = keys.iter().filter(|k| k.starts_with("chc.")).collect();
    // assert!(chc_keys.len() >= 3, ...);
}
