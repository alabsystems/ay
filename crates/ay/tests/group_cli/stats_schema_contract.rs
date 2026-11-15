// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Schema contract tests for `--stats` canonical output (#4723).
//!
//! Verifies that all three solve modes (SMT, DIMACS SAT, CHC) emit a common
//! key set on stderr via the `RunStatistics` envelope, preventing silent
//! schema drift across modes.
//!
//! Meridian PR1 (58f2aaa13) changed the human surface deliberately: the build
//! stamp is stated by the `c ay.session.*` markers alone, never again as a
//! `c ay.build.stamp:` row in a statistics block; and SMT runs print only the
//! s-expression `(:statistics …)` block, so their envelope is reachable only
//! through `--stats-json`. The cross-mode contract therefore has two halves:
//! the human comment block (DIMACS, CHC) and the JSON envelope (every mode).

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

/// Common keys that MUST appear in the canonical human stats block (DIMACS,
/// CHC). The build stamp is deliberately not one of them: see
/// [`assert_build_stamp_not_restated`].
const COMMON_KEYS: &[&str] = &["ay.mode:", "ay.result:", "ay.wall_time_ms:"];

/// Common fields that MUST appear in the `--stats-json` envelope of every mode.
const COMMON_JSON_FIELDS: &[&str] = &["mode", "result", "wall_time_ms", "ay_build"];

/// Header that MUST appear to indicate canonical stats format.
const STATS_HEADER: &str = "AY statistics";

/// Only the `c ay.session.*` markers may name the build; no statistics block
/// restates it (58f2aaa13). How many markers carry it depends on the session
/// log level (`AY_SESSION_LOG`, forced to `full` by any competition signal),
/// which `build_version_stamp_8870` pins, so this holds at every level. The
/// stamp's value comes from the start marker when there is one, which catches
/// a restatement under any key spelling.
fn assert_build_stamp_not_restated(mode: &str, stderr: &str) {
    let stamp = stderr.lines().find_map(|line| {
        line.strip_prefix("c ay.session.start ")?
            .split_whitespace()
            .find_map(|field| field.strip_prefix("build.stamp="))
    });
    for line in stderr
        .lines()
        .filter(|line| !line.starts_with("c ay.session."))
    {
        assert!(
            !line.contains("build.stamp") && stamp.is_none_or(|stamp| !line.contains(stamp)),
            "{mode}: only the session markers may state the build stamp; {line:?} restates it in: {stderr}"
        );
    }
}

/// Run `ay --stats-json FILE`, check its exit code, and return the one JSON
/// envelope on stderr.
fn stats_json_envelope(path: &std::path::Path, expected_exit: i32) -> serde_json::Value {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--stats-json")
        .arg(path)
        .output()
        .expect("Failed to spawn ay --stats-json");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(expected_exit),
        "expected exit {expected_exit} from ay --stats-json {}: {stderr}",
        path.display()
    );
    let json_lines: Vec<&str> = stderr
        .lines()
        .filter(|line| line.trim_start().starts_with('{'))
        .collect();
    assert_eq!(
        json_lines.len(),
        1,
        "expected exactly one JSON stats envelope on stderr: {stderr}"
    );
    serde_json::from_str(json_lines[0]).expect("stats envelope must be valid JSON")
}

fn assert_common_json_fields(mode: &str, parsed: &serde_json::Value) {
    for field in COMMON_JSON_FIELDS {
        assert!(
            parsed.get(field).is_some(),
            "{mode}: missing common JSON field {field}: {parsed}"
        );
    }
    assert!(
        parsed["ay_build"]["stamp"]
            .as_str()
            .is_some_and(|stamp| !stamp.is_empty()),
        "{mode}: the JSON envelope must carry the build stamp: {parsed}"
    );
}

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
    // The human surface of an SMT run is the s-expression block alone: the
    // comment block restated it under a second set of names (58f2aaa13).
    assert!(
        !stderr.contains(STATS_HEADER) && !stderr.contains("ay.mode:"),
        "SMT mode: the comment stats block must not be emitted: {stderr}"
    );
    for key in ["(:statistics", ":result", ":conflicts", ":decisions"] {
        assert!(
            stderr.contains(key),
            "SMT mode: missing {key} in the s-expression statistics block: {stderr}"
        );
    }
    assert_build_stamp_not_restated("SMT mode", &stderr);

    // The SMT envelope, with its own mode tag and the common solver keys.
    let parsed = stats_json_envelope(&temp_path, 0);
    assert_common_json_fields("SMT mode", &parsed);
    assert_eq!(
        parsed["mode"], "smt",
        "SMT mode: expected 'smt' mode tag: {parsed}"
    );
    for key in ["conflicts", "decisions"] {
        assert!(
            parsed[key].is_u64(),
            "SMT mode: missing numeric '{key}' in the JSON envelope: {parsed}"
        );
    }
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
    assert_build_stamp_not_restated("DIMACS SAT mode", &stderr);

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
    assert_build_stamp_not_restated("CHC mode", &stderr);

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

/// The JSON envelope is the one surface every mode still shares field for
/// field, build provenance included, so it is where cross-mode drift shows.
#[test]
#[timeout(60_000)]
fn test_schema_contract_json_envelope_common_fields_all_modes() {
    // One directory for all three inputs, so the sidecars a default run leaves
    // beside its input (DIMACS proof status, CHC certificate) go with it.
    let dir = tempfile::tempdir().expect("create fixture directory");
    let fixture = |name: &str, contents: &str| {
        let path = dir.path().join(name);
        std::fs::write(&path, contents).expect("write fixture");
        path
    };
    let smt = fixture(
        "sat.smt2",
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 42))\n(check-sat)\n",
    );
    let cnf = fixture("sat.cnf", "p cnf 2 2\n1 0\n2 0\n");
    let horn = fixture(
        "safe.smt2",
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    );

    // (mode, input, exit code, the tags that mode may report). DIMACS keeps
    // the SAT Competition's 10; a default CHC query may run the portfolio.
    for (mode, path, exit_code, tags) in [
        ("SMT", &smt, 0, &["smt"][..]),
        ("DIMACS SAT", &cnf, 10, &["dimacs-sat"][..]),
        ("CHC", &horn, 0, &["chc", "portfolio"][..]),
    ] {
        let parsed = stats_json_envelope(path, exit_code);
        assert_common_json_fields(mode, &parsed);
        assert!(
            parsed["mode"]
                .as_str()
                .is_some_and(|tag| tags.contains(&tag)),
            "{mode}: expected a mode tag in {tags:?}: {parsed}"
        );
        assert_eq!(
            parsed["result"], "sat",
            "{mode}: every fixture here is satisfiable: {parsed}"
        );
    }
}
