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

use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::smt::{first_line, run_ay_file as run_ay_file_bounded, run_ay_stdin, Outcome};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Run AY on a file with a timeout (in seconds). Returns the Outcome.
fn run_ay_file(path: &Path, timeout_secs: u64) -> Outcome {
    run_ay_file_bounded(path, Duration::from_secs(timeout_secs))
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

include!("smtlib_conformance_runner/benchmark_files.rs");

include!("smtlib_conformance_runner/commands.rs");

// ===========================================================================
// Part 3: Conformance summary report across logics
// ===========================================================================

#[test]
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
