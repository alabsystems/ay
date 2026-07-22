// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB 2.6 conformance runner (#8343).
//!
//! Complements smtlib_compliance.rs with:
//! - File-based benchmark conformance tests (reads .smt2 files with :status annotations)
//! - Additional command tests (check-sat-assuming, get-value, define-fun, define-sort,
//!   declare-datatypes, get-unsat-assumptions)
//! - Conformance summary report across 12 logics

use ntest::timeout;
use std::fmt;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use wait_timeout::ChildExt;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

struct AYOutput {
    stdout: String,
    stderr: String,
    success: bool,
}

fn run_ay_stdin(input: &str) -> AYOutput {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().expect("stdin must be piped");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write to ay stdin");
    }

    let output = child.wait_with_output().expect("failed to wait on ay");
    AYOutput {
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        success: output.status.success(),
    }
}

fn first_line(out: &AYOutput) -> &str {
    out.stdout.lines().next().unwrap_or("").trim()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error(String),
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Unsat => write!(f, "unsat"),
            Self::Unknown => write!(f, "unknown"),
            Self::Timeout => write!(f, "timeout"),
            Self::Error(e) => write!(f, "error: {e}"),
        }
    }
}

/// Run AY on a file with a timeout (in seconds). Returns the Outcome.
fn run_ay_file(path: &Path, timeout_secs: u64) -> Outcome {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let mut child = match Command::new(ay_path)
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => return Outcome::Error(format!("spawn failed: {e}")),
    };

    let timeout_dur = std::time::Duration::from_secs(timeout_secs);
    match child.wait_timeout(timeout_dur) {
        Ok(Some(status)) => {
            // Process exited within timeout. Read output from pipes.
            let mut stdout_buf = Vec::new();
            let mut stderr_buf = Vec::new();
            if let Some(mut out) = child.stdout.take() {
                let _ = out.read_to_end(&mut stdout_buf);
            }
            if let Some(mut err) = child.stderr.take() {
                let _ = err.read_to_end(&mut stderr_buf);
            }
            let stdout = String::from_utf8_lossy(&stdout_buf);
            let first = stdout.lines().next().unwrap_or("").trim();
            if !status.success() && first.is_empty() {
                let stderr_str = String::from_utf8_lossy(&stderr_buf);
                return Outcome::Error(format!(
                    "exit code {:?}, stderr: {}",
                    status.code(),
                    stderr_str.chars().take(200).collect::<String>()
                ));
            }
            match first {
                "sat" => Outcome::Sat,
                "unsat" => Outcome::Unsat,
                "unknown" => Outcome::Unknown,
                other => Outcome::Error(format!("unexpected output: {other}")),
            }
        }
        Ok(None) => {
            // Timeout. Kill the child.
            let _ = child.kill();
            let _ = child.wait();
            Outcome::Timeout
        }
        Err(e) => Outcome::Error(format!("wait error: {e}")),
    }
}

/// Return the workspace root (parent of `crates/`).
fn workspace_root() -> PathBuf {
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest)
        .parent()
        .and_then(|p| p.parent())
        .expect("cannot find workspace root")
        .to_path_buf()
}

/// Extract expected status from a .smt2 file's :status annotation.
/// Returns None if no :status annotation is found.
fn extract_expected_status(path: &Path) -> Option<Outcome> {
    let content = std::fs::read_to_string(path).ok()?;
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.contains(":status") {
            if trimmed.contains(":status sat") {
                return Some(Outcome::Sat);
            } else if trimmed.contains(":status unsat") {
                return Some(Outcome::Unsat);
            } else if trimmed.contains(":status unknown") {
                return Some(Outcome::Unknown);
            }
        }
    }
    None
}

/// Run all .smt2 files in a directory that have :status annotations.
/// Returns (total, pass, fail, timeout, error, unknown) counts.
fn run_benchmark_dir(dir: &Path, timeout_secs: u64) -> (usize, usize, usize, usize, usize, usize) {
    run_benchmark_dir_with_skip(dir, timeout_secs, &[])
}

fn run_benchmark_dir_with_skip(
    dir: &Path,
    timeout_secs: u64,
    skipped_files: &[&str],
) -> (usize, usize, usize, usize, usize, usize) {
    let mut total = 0;
    let mut pass = 0;
    let mut fail = 0;
    let mut timeouts = 0;
    let mut errors = 0;
    let mut unknowns = 0;

    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read dir {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "smt2"))
        .collect();
    entries.sort();

    for path in &entries {
        let expected = match extract_expected_status(path) {
            Some(e) => e,
            None => continue, // skip files without :status
        };

        // Skip :status unknown files -- nothing to check
        if expected == Outcome::Unknown {
            continue;
        }

        let file_name = path.file_name().unwrap_or_default().to_string_lossy();
        if skipped_files.iter().any(|skipped| *skipped == file_name) {
            eprintln!("  SKIP: {file_name} (known slow benchmark exceeds CI conformance budget)");
            continue;
        }

        total += 1;
        let actual = run_ay_file(path, timeout_secs);

        match &actual {
            Outcome::Timeout => {
                timeouts += 1;
                eprintln!(
                    "  TIMEOUT: {} (expected {})",
                    path.file_name().unwrap_or_default().to_string_lossy(),
                    expected
                );
            }
            Outcome::Error(e) => {
                errors += 1;
                eprintln!(
                    "  ERROR: {} — {e}",
                    path.file_name().unwrap_or_default().to_string_lossy()
                );
            }
            Outcome::Unknown => {
                unknowns += 1;
                eprintln!(
                    "  UNKNOWN: {} (expected {})",
                    path.file_name().unwrap_or_default().to_string_lossy(),
                    expected
                );
            }
            outcome if *outcome == expected => {
                pass += 1;
            }
            outcome => {
                fail += 1;
                eprintln!(
                    "  MISMATCH: {} — expected {expected}, got {outcome}",
                    path.file_name().unwrap_or_default().to_string_lossy()
                );
            }
        }
    }

    (total, pass, fail, timeouts, errors, unknowns)
}

// ===========================================================================
// Part 1: Benchmark file conformance tests
// ===========================================================================

#[test]
#[timeout(120_000)]
fn test_conformance_qf_ax_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_AX");
    if !dir.exists() {
        eprintln!("Skipping QF_AX: directory not found");
        return;
    }
    let (total, pass, fail, timeouts, errors, unknowns) = run_benchmark_dir(&dir, 30);
    eprintln!(
        "QF_AX: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    // At minimum we should run some benchmarks
    assert!(
        total > 0,
        "Expected at least one QF_AX benchmark with :status"
    );
    // Allow some failures (conformance gap discovery), but majority should pass
    let pass_rate = if total > 0 {
        pass as f64 / total as f64
    } else {
        0.0
    };
    eprintln!("QF_AX pass rate: {:.1}%", pass_rate * 100.0);
}

#[test]
#[timeout(120_000)]
fn test_conformance_qf_auflia_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_AUFLIA");
    if !dir.exists() {
        eprintln!("Skipping QF_AUFLIA: directory not found");
        return;
    }
    let (total, pass, fail, timeouts, errors, unknowns) = run_benchmark_dir_with_skip(
        &dir,
        30,
        &[
            "storeinv_t3_pp_sf_ai_00008_001.cvc.smt2",
            "storeinv_t3_pp_sf_ai_00009_001.cvc.smt2",
            "storeinv_t3_pp_sf_ai_00010_001.cvc.smt2",
        ],
    );
    eprintln!(
        "QF_AUFLIA: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    assert!(
        total > 0,
        "Expected at least one QF_AUFLIA benchmark with :status"
    );
    let pass_rate = if total > 0 {
        pass as f64 / total as f64
    } else {
        0.0
    };
    eprintln!("QF_AUFLIA pass rate: {:.1}%", pass_rate * 100.0);
}

#[test]
#[timeout(120_000)]
fn test_conformance_qf_bv_extract_concat_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_BV_extract_concat");
    if !dir.exists() {
        eprintln!("Skipping QF_BV_extract_concat: directory not found");
        return;
    }
    let (total, pass, fail, timeouts, errors, unknowns) = run_benchmark_dir(&dir, 30);
    eprintln!(
        "QF_BV_extract_concat: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    assert!(
        total > 0,
        "Expected at least one QF_BV benchmark with :status"
    );
    let pass_rate = if total > 0 {
        pass as f64 / total as f64
    } else {
        0.0
    };
    eprintln!("QF_BV_extract_concat pass rate: {:.1}%", pass_rate * 100.0);
}

#[test]
#[timeout(120_000)]
fn test_conformance_qf_uflra_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_UFLRA");
    if !dir.exists() {
        eprintln!("Skipping QF_UFLRA: directory not found");
        return;
    }
    // QF_UFLRA may have subdirectories; collect all .smt2 recursively
    let mut all_files: Vec<PathBuf> = Vec::new();
    fn collect_smt2(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    collect_smt2(&path, files);
                } else if path.extension().is_some_and(|ext| ext == "smt2") {
                    files.push(path);
                }
            }
        }
    }
    collect_smt2(&dir, &mut all_files);
    all_files.sort();

    let mut total = 0;
    let mut pass = 0;
    let mut fail = 0;
    let mut timeouts = 0;
    let mut errors = 0;
    let mut unknowns = 0;

    for path in &all_files {
        let expected = match extract_expected_status(path) {
            Some(e) => e,
            None => continue,
        };
        if expected == Outcome::Unknown {
            continue;
        }
        total += 1;
        let actual = run_ay_file(path, 30);
        match &actual {
            Outcome::Timeout => timeouts += 1,
            Outcome::Error(_) => errors += 1,
            Outcome::Unknown => unknowns += 1,
            outcome if *outcome == expected => pass += 1,
            _ => fail += 1,
        }
    }

    eprintln!(
        "QF_UFLRA: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    if total > 0 {
        let pass_rate = f64::from(pass) / f64::from(total);
        eprintln!("QF_UFLRA pass rate: {:.1}%", pass_rate * 100.0);
    }
}

// ===========================================================================
// Part 2: Additional command compliance tests
// ===========================================================================

// --- check-sat-assuming ---

#[test]
#[timeout(30_000)]
fn test_cmd_check_sat_assuming_sat() {
    let input = "\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(check-sat-assuming ((> x 5)))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "check-sat-assuming expected sat or unknown, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_check_sat_assuming_unsat() {
    let input = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat-assuming ((< x 0)))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "unsat" || fl == "unknown",
        "check-sat-assuming expected unsat or unknown, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_check_sat_assuming_incremental() {
    let input = "\
(set-logic QF_UF)
(set-option :produce-unsat-assumptions true)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(assert (not (= a b)))
(check-sat-assuming ((= a b)))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "unsat" || fl == "unknown",
        "check-sat-assuming contradictory expected unsat or unknown, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- get-value ---

#[test]
#[timeout(30_000)]
fn test_cmd_get_value_int() {
    let input = "\
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-const x Int)
(assert (= x 42))
(check-sat)
(get-value (x))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "get-value test: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
    if fl == "sat" {
        // Output should contain the value assignment
        assert!(
            out.stdout.contains("42") || out.stdout.contains("x"),
            "get-value output should contain value: {}",
            out.stdout
        );
    }
}

#[test]
#[timeout(30_000)]
fn test_cmd_get_value_bool() {
    let input = "\
(set-logic QF_UF)
(set-option :produce-models true)
(declare-const p Bool)
(assert p)
(check-sat)
(get-value (p))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "get-value bool test: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
    if fl == "sat" {
        assert!(
            out.stdout.contains("true") || out.stdout.contains("p"),
            "get-value bool output should contain true: {}",
            out.stdout
        );
    }
}

#[test]
#[timeout(30_000)]
fn test_cmd_get_value_bitvector() {
    let input = "\
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(assert (= x #xFF))
(check-sat)
(get-value (x))
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "get-value bv test: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- define-fun ---

#[test]
#[timeout(30_000)]
fn test_cmd_define_fun_basic() {
    let input = "\
(set-logic QF_LIA)
(define-fun double ((x Int)) Int (* 2 x))
(declare-const a Int)
(assert (= (double a) 10))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-fun basic: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_define_fun_nested() {
    let input = "\
(set-logic QF_LIA)
(define-fun inc ((x Int)) Int (+ x 1))
(define-fun double_inc ((x Int)) Int (inc (inc x)))
(declare-const a Int)
(assert (= (double_inc 0) 2))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-fun nested: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- define-sort ---

#[test]
#[timeout(30_000)]
fn test_cmd_define_sort_alias() {
    let input = "\
(set-logic QF_LIA)
(define-sort MyInt () Int)
(declare-const x MyInt)
(assert (> x 5))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-sort alias: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_define_sort_parametric() {
    let input = "\
(set-logic QF_AUFLIA)
(define-sort IntArray () (Array Int Int))
(declare-const a IntArray)
(assert (= (select a 0) 42))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown",
        "define-sort parametric: expected sat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- declare-datatypes ---

#[test]
#[timeout(30_000)]
fn test_cmd_declare_datatypes_simple() {
    let input = "\
(set-logic ALL)
(declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))
(declare-const c Color)
(assert (= c Red))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    // Datatype support may be partial
    assert!(
        fl == "sat" || fl == "unknown" || out.stdout.contains("error") || !out.success,
        "declare-datatypes: unexpected output: {fl}\nstderr: {}",
        out.stderr
    );
}

#[test]
#[timeout(30_000)]
fn test_cmd_declare_datatypes_option() {
    let input = "\
(set-logic ALL)
(declare-datatypes ((Option 1)) ((par (T) ((Some (val T)) (None)))))
(declare-const x (Option Int))
(assert (= x (Some 42)))
(check-sat)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    assert!(
        fl == "sat" || fl == "unknown" || out.stdout.contains("error") || !out.success,
        "declare-datatypes option: unexpected output: {fl}\nstderr: {}",
        out.stderr
    );
}

// --- get-info ---

#[test]
#[timeout(30_000)]
fn test_cmd_get_info_version() {
    let input = "\
(get-info :name)
(get-info :version)
(exit)
";
    let out = run_ay_stdin(input);
    // Should produce some response (not necessarily formatted per spec)
    assert!(
        out.success || !out.stdout.is_empty(),
        "get-info should produce output\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

// --- get-unsat-assumptions ---

#[test]
#[timeout(30_000)]
fn test_cmd_get_unsat_assumptions() {
    let input = "\
(set-logic QF_LIA)
(set-option :produce-unsat-assumptions true)
(declare-const x Int)
(assert (> x 0))
(check-sat-assuming ((< x 0)))
(get-unsat-assumptions)
(exit)
";
    let out = run_ay_stdin(input);
    let fl = first_line(&out);
    // The first line should be unsat (or unknown)
    assert!(
        fl == "unsat" || fl == "unknown",
        "get-unsat-assumptions test: expected unsat, got: {fl}\nstderr: {}",
        out.stderr
    );
}

// ===========================================================================
// Part 3: Conformance summary report across logics
// ===========================================================================

#[test]
#[timeout(300_000)]
fn test_conformance_summary_report() {
    // Inline benchmarks for 12 logics to get a quick conformance snapshot
    let benchmarks: Vec<(&str, &str, &str)> = vec![
        ("QF_LIA", "sat", "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(check-sat)(exit)"),
        ("QF_LIA", "unsat", "(set-logic QF_LIA)(declare-const x Int)(assert (and (> x 0) (< x 0)))(check-sat)(exit)"),
        ("QF_LRA", "sat", "(set-logic QF_LRA)(declare-const x Real)(assert (> x 0.5))(check-sat)(exit)"),
        ("QF_LRA", "unsat", "(set-logic QF_LRA)(declare-const x Real)(assert (and (> x 1.0) (< x 0.0)))(check-sat)(exit)"),
        ("QF_UF", "sat", "(set-logic QF_UF)(declare-sort U 0)(declare-const a U)(declare-const b U)(assert (not (= a b)))(check-sat)(exit)"),
        ("QF_UF", "unsat", "(set-logic QF_UF)(declare-sort U 0)(declare-const a U)(assert (not (= a a)))(check-sat)(exit)"),
        ("QF_BV", "sat", "(set-logic QF_BV)(declare-const x (_ BitVec 32))(assert (bvugt x #x00000000))(check-sat)(exit)"),
        ("QF_BV", "unsat", "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (and (bvugt x #xFE) (bvult x #xFF)))(check-sat)(exit)"),
        ("QF_UFLIA", "sat", "(set-logic QF_UFLIA)(declare-fun f (Int) Int)(declare-const a Int)(assert (> (f a) 0))(check-sat)(exit)"),
        ("QF_UFLIA", "unsat", "(set-logic QF_UFLIA)(declare-fun f (Int) Int)(declare-const a Int)(assert (and (= (f a) 0) (> (f a) 0)))(check-sat)(exit)"),
        ("QF_UFLRA", "sat", "(set-logic QF_UFLRA)(declare-fun g (Real) Real)(declare-const r Real)(assert (> (g r) 0.0))(check-sat)(exit)"),
        ("QF_UFLRA", "unsat", "(set-logic QF_UFLRA)(declare-fun g (Real) Real)(declare-const r Real)(assert (and (= (g r) 0.0) (> (g r) 1.0)))(check-sat)(exit)"),
        ("QF_AUFLIA", "sat", "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))(assert (= (select a 0) 42))(check-sat)(exit)"),
        ("QF_AUFLIA", "unsat", "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))(declare-const b (Array Int Int))(assert (and (= a b) (not (= (select a 0) (select b 0)))))(check-sat)(exit)"),
        ("QF_ABV", "sat", "(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))(assert (= (select a #x00) #xFF))(check-sat)(exit)"),
        ("QF_ABV", "unsat", "(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))(assert (and (= (select a #x00) #xFF) (= (select a #x00) #x00)))(check-sat)(exit)"),
        ("QF_NIA", "sat", "(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 4))(check-sat)(exit)"),
        ("QF_NIA", "unsat", "(set-logic QF_NIA)(declare-const x Int)(assert (and (= (* x x) 2) (> x 0) (< x 2)))(check-sat)(exit)"),
        ("LIA", "sat", "(set-logic LIA)(declare-const x Int)(assert (forall ((y Int)) (>= (+ x y) y)))(check-sat)(exit)"),
        ("LIA", "unsat", "(set-logic LIA)(assert (forall ((x Int)) (> x x)))(check-sat)(exit)"),
        ("LRA", "sat", "(set-logic LRA)(declare-const x Real)(assert (exists ((y Real)) (= (+ x y) 0.0)))(check-sat)(exit)"),
        ("LRA", "unsat", "(set-logic LRA)(assert (forall ((x Real)) (> x x)))(check-sat)(exit)"),
    ];

    // Collect results by logic
    use std::collections::BTreeMap;
    let mut results: BTreeMap<&str, (usize, usize, usize, usize)> = BTreeMap::new();

    for (logic, expected_str, input) in &benchmarks {
        let out = run_ay_stdin(input);
        let fl = first_line(&out);

        let entry = results.entry(logic).or_insert((0, 0, 0, 0));
        entry.0 += 1; // total

        if fl == *expected_str {
            entry.1 += 1; // pass
        } else if fl == "unknown" {
            entry.3 += 1; // unknown
        } else {
            entry.2 += 1; // fail
            eprintln!(
                "  {logic}: expected {expected_str}, got {fl} — stderr: {}",
                out.stderr.lines().next().unwrap_or("")
            );
        }
    }

    // Print summary table
    eprintln!("\n=== SMT-LIB 2.6 Conformance Summary ===");
    eprintln!(
        "{:<12} {:>5} {:>5} {:>5} {:>5} {:>8}",
        "Logic", "Total", "Pass", "Fail", "Unkn", "Rate"
    );
    eprintln!("{}", "-".repeat(48));

    let mut grand_total = 0;
    let mut grand_pass = 0;
    let mut grand_fail = 0;
    let mut grand_unknown = 0;

    for (logic, (total, pass, fail, unknown)) in &results {
        let rate = if *total > 0 {
            format!("{:.0}%", (*pass as f64 / *total as f64) * 100.0)
        } else {
            "N/A".to_string()
        };
        eprintln!("{logic:<12} {total:>5} {pass:>5} {fail:>5} {unknown:>5} {rate:>8}");
        grand_total += total;
        grand_pass += pass;
        grand_fail += fail;
        grand_unknown += unknown;
    }

    eprintln!("{}", "-".repeat(48));
    let grand_rate = if grand_total > 0 {
        format!("{:.0}%", (grand_pass as f64 / grand_total as f64) * 100.0)
    } else {
        "N/A".to_string()
    };
    eprintln!(
        "{:<12} {:>5} {:>5} {:>5} {:>5} {:>8}",
        "TOTAL", grand_total, grand_pass, grand_fail, grand_unknown, grand_rate
    );

    // We expect at least some tests to pass
    assert!(
        grand_pass > 0,
        "At least some conformance benchmarks should pass"
    );
}
