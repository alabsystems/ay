// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the CLI-owned SAT / theory disable flags (#8506).
//!
//! Runtime technique toggles in the `ay` binary are configured through CLI
//! flags, not `AY_NO_*` environment variables.

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
        "ay_cli_env_migration_{}_{}.{}",
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

/// A trivially satisfiable DIMACS CNF — exercises the SAT solve path so that
/// `--no-*` flags are actually consulted by preprocess().
const TRIVIAL_SAT_CNF: &str = "p cnf 2 1\n1 2 0\n";

/// A trivially satisfiable SMT-LIB instance for theory flag tests.
const TRIVIAL_SMT: &str =
    "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 0))\n(check-sat)\n";

/// A trivially satisfiable SMT-LIB BV instance for unsupported JIT stat guards.
const TRIVIAL_BV_SMT: &str =
    "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x #x00))\n(check-sat)\n";

fn parse_stats_json(stderr: &str) -> serde_json::Value {
    let json_line = stderr
        .lines()
        .find(|line| line.trim_start().starts_with('{'))
        .unwrap_or_else(|| panic!("expected stats JSON line on stderr, got: {stderr}"));
    serde_json::from_str(json_line).expect("stats stderr line should be valid JSON")
}

#[test]
#[timeout(60_000)]
fn test_no_bve_cli_flag_solves_without_warning() {
    // --no-bve must work as a first-class CLI flag, not emit a deprecation
    // warning, and still produce a correct result.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--no-bve")
        .arg(&input)
        .output()
        .expect("spawn ay");

    // DIMACS SAT returns exit code 10 (SAT) or 20 (UNSAT); both are success.
    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "ay failed with --no-bve, exit={code:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("SAT") || stdout.contains("sat"),
        "expected sat output, got: {stdout}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("AY_NO_BVE is deprecated"),
        "CLI flag should NOT emit env var deprecation warning, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_multiple_no_flags_cli() {
    // Exercise multiple --no-* flags at once to verify they all parse and
    // apply without warnings or conflicts.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--no-bve")
        .arg("--no-vivify")
        .arg("--no-probe")
        .arg("--no-subsume")
        .arg("--no-bce")
        .arg("--no-congruence")
        .arg("--no-inprocess")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "ay failed with multiple --no-* flags, exit={code:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("deprecated"),
        "pure CLI usage must not emit deprecation warnings, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_theory_no_flag_cli_solves_without_warning() {
    // --no-bound-axioms is a pre-existing CLI flag that previously bridged
    // through AY_NO_BOUND_AXIOMS env var. After #8506 it wires directly into
    // the global TheoryDisableFlags, with no env var side effect.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg("--no-bound-axioms")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "ay failed with --no-bound-axioms, exit={code:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("deprecated"),
        "CLI flag should not emit env var deprecation warning, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_smt_bv_stats_json_fail_closes_unsupported_jit_counters() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_BV_SMT, "smt2");

    let output = Command::new(ay_path)
        .arg(&input)
        .arg("--stats-json")
        .output()
        .expect("spawn ay with --stats-json on QF_BV fixture");

    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "ay failed on QF_BV stats-json fixture, exit={code:?}: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("sat"),
        "QF_BV fixture should solve as sat, got: {stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json(&stderr);
    assert_eq!(parsed["mode"], "smt");
    for key in [
        "smt_bv_batch_template_applications",
        "smt_native_code_helper_applications",
    ] {
        assert_eq!(
            parsed[key].as_u64(),
            Some(0),
            "unsupported SMT JIT counter {key} must fail closed at zero: {parsed}"
        );
    }
    assert!(
        parsed.get("competition_jit").is_none(),
        "unsupported BV/native-helper SMT JIT artifacts must not emit competition metadata: {parsed}"
    );
}

#[test]
#[timeout(60_000)]
fn test_dimacs_stats_json_uses_native_code_helper_label() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _c) = write_temp(TRIVIAL_SAT_CNF, "cnf");

    let output = Command::new(ay_path)
        .arg("--stats-json")
        .arg(&input)
        .output()
        .expect("spawn ay with --stats-json");

    let code = output.status.code();
    assert!(
        matches!(code, Some(0) | Some(10) | Some(20)),
        "ay failed with --stats-json, exit={code:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("\"sat.native_code_helpers_enabled\":"),
        "stats JSON should expose the current SAT native-code helper label, got: {stderr}"
    );
    assert!(
        !stderr.contains("\"sat.jit_propagations\":"),
        "stats JSON should not expose ambiguous retired SAT JIT BCP labels, got: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_help_lists_migrated_flags() {
    // Full help must document the advanced disable flags so users can
    // discover the supported runtime knobs without crowding default help.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--help=full")
        .output()
        .expect("spawn ay");

    let help = String::from_utf8_lossy(&output.stdout);
    for flag in [
        "--no-bve",
        "--no-vivify",
        "--no-probe",
        "--no-subsume",
        "--no-bce",
        "--no-inprocess",
        "--no-preprocess",
        "--no-congruence",
        "--no-cold-restart",
    ] {
        assert!(
            help.contains(flag),
            "help output missing {flag}, got:\n{help}"
        );
    }
}
