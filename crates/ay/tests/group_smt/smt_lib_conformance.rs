// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB 2.6 conformance test suite (#8343).
//!
//! Runs AY on a curated set of small benchmarks in `benchmarks/conformance/`
//! and verifies correctness against expected sat/unsat annotations.
//!
//! Coverage: QF_LIA, QF_LRA, QF_UF, QF_BV, QF_ABV, QF_AUFLIA, QF_AX,
//!           QF_UFLIA, QF_UFLRA (9 logics, ~40 benchmarks).
//!
//! Soundness policy:
//! - If AY returns the wrong definite answer (sat when expected unsat, or vice versa),
//!   the test FAILS. This is a soundness bug.
//! - If AY returns "unknown", the test passes (solver is incomplete but sound).
//! - If AY errors or times out, the test records the failure but does not assert
//!   soundness violation (the solver did not claim a wrong answer).
//!
//! Each logic directory is tested independently so failures are isolated per logic.

use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::smt::{run_ay_file as run_ay_file_bounded, Outcome};

// ---------------------------------------------------------------------------
// Types and helpers
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expected {
    Sat,
    Unsat,
}

#[allow(dead_code)]
struct BenchmarkResult {
    file: String,
    expected: Expected,
    actual: Outcome,
}

impl BenchmarkResult {
    /// Returns true if this result represents a soundness violation:
    /// AY returned a definite answer that contradicts the expected result.
    fn is_soundness_violation(&self) -> bool {
        matches!(
            (&self.expected, &self.actual),
            (Expected::Sat, Outcome::Unsat) | (Expected::Unsat, Outcome::Sat)
        )
    }

    fn is_pass(&self) -> bool {
        matches!(
            (&self.expected, &self.actual),
            (Expected::Sat, Outcome::Sat) | (Expected::Unsat, Outcome::Unsat)
        )
    }
}

fn run_ay_file(path: &Path, timeout_secs: u64) -> Outcome {
    run_ay_file_bounded(path, Duration::from_secs(timeout_secs))
}

fn workspace_root() -> PathBuf {
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest)
        .parent()
        .and_then(|p| p.parent())
        .expect("cannot find workspace root")
        .to_path_buf()
}

fn extract_expected_status(path: &Path) -> Option<Expected> {
    let content = std::fs::read_to_string(path).ok()?;
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.contains(":status") {
            if trimmed.contains(":status sat") {
                return Some(Expected::Sat);
            } else if trimmed.contains(":status unsat") {
                return Some(Expected::Unsat);
            }
        }
    }
    None
}

/// Run all conformance benchmarks in a logic directory.
/// Returns the results and panics on any soundness violation.
fn run_conformance_logic(logic: &str, timeout_secs: u64) -> Vec<BenchmarkResult> {
    let root = workspace_root();
    let dir = root.join("benchmarks/conformance").join(logic);
    if !dir.exists() {
        eprintln!("SKIP: {logic} -- no conformance directory");
        return Vec::new();
    }

    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "smt2"))
        .collect();
    entries.sort();

    assert!(
        !entries.is_empty(),
        "{logic}: no .smt2 files in {}",
        dir.display()
    );

    let mut results = Vec::new();
    let mut soundness_violations = Vec::new();

    for path in &entries {
        let expected = match extract_expected_status(path) {
            Some(e) => e,
            None => continue,
        };

        let actual = run_ay_file(path, timeout_secs);
        let file_name = path.file_name().unwrap().to_string_lossy().to_string();

        let result = BenchmarkResult {
            file: file_name.clone(),
            expected,
            actual,
        };

        if result.is_soundness_violation() {
            soundness_violations.push(format!(
                "  SOUNDNESS BUG: {file_name} -- expected {}, got {}",
                match &result.expected {
                    Expected::Sat => "sat",
                    Expected::Unsat => "unsat",
                },
                result.actual
            ));
        }

        results.push(result);
    }

    // Print summary for this logic
    let total = results.len();
    let pass = results.iter().filter(|r| r.is_pass()).count();
    let unknown = results
        .iter()
        .filter(|r| matches!(r.actual, Outcome::Unknown))
        .count();
    let errors = results
        .iter()
        .filter(|r| matches!(r.actual, Outcome::Error(_) | Outcome::Timeout))
        .count();
    let violations = soundness_violations.len();

    eprintln!(
        "{logic}: {total} benchmarks -- {pass} pass, {violations} soundness bugs, \
         {unknown} unknown, {errors} error/timeout"
    );

    if !soundness_violations.is_empty() {
        for v in &soundness_violations {
            eprintln!("{v}");
        }
        panic!(
            "{logic}: {violations} SOUNDNESS VIOLATION(S) detected. \
             AY returned a definite wrong answer."
        );
    }

    results
}

// ===========================================================================
// Per-logic conformance tests
// ===========================================================================

#[test]
fn test_conformance_qf_lia() {
    let results = run_conformance_logic("QF_LIA", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_LIA: expected at least 4 benchmarks");
}

#[test]
fn test_conformance_qf_lra() {
    let results = run_conformance_logic("QF_LRA", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_LRA: expected at least 4 benchmarks");
}

#[test]
fn test_conformance_qf_uf() {
    let results = run_conformance_logic("QF_UF", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_UF: expected at least 4 benchmarks");
}

#[test]
fn test_conformance_qf_bv() {
    let results = run_conformance_logic("QF_BV", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_BV: expected at least 4 benchmarks");
}

#[test]
fn test_conformance_qf_abv() {
    let results = run_conformance_logic("QF_ABV", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_ABV: expected at least 4 benchmarks");
}

#[test]
fn test_conformance_qf_auflia() {
    let results = run_conformance_logic("QF_AUFLIA", 10);
    if results.is_empty() {
        return;
    }
    assert!(
        results.len() >= 4,
        "QF_AUFLIA: expected at least 4 benchmarks"
    );
}

#[test]
fn test_conformance_qf_ax() {
    let results = run_conformance_logic("QF_AX", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 3, "QF_AX: expected at least 3 benchmarks");
}

#[test]
fn test_conformance_qf_uflia() {
    let results = run_conformance_logic("QF_UFLIA", 10);
    if results.is_empty() {
        return;
    }
    assert!(
        results.len() >= 3,
        "QF_UFLIA: expected at least 3 benchmarks"
    );
}

#[test]
fn test_conformance_qf_uflra() {
    let results = run_conformance_logic("QF_UFLRA", 10);
    if results.is_empty() {
        return;
    }
    assert!(
        results.len() >= 3,
        "QF_UFLRA: expected at least 3 benchmarks"
    );
}

// ===========================================================================
// Cross-logic summary test
// ===========================================================================

struct LogicSummary {
    logic: &'static str,
    total: usize,
    passed: usize,
    unknown: usize,
    errors: usize,
}

fn summarize_logic(logic: &'static str) -> Option<LogicSummary> {
    let results = run_conformance_logic(logic, 10);
    if results.is_empty() {
        return None;
    }
    Some(LogicSummary {
        logic,
        total: results.len(),
        passed: results.iter().filter(|result| result.is_pass()).count(),
        unknown: results
            .iter()
            .filter(|result| matches!(result.actual, Outcome::Unknown))
            .count(),
        errors: results
            .iter()
            .filter(|result| matches!(result.actual, Outcome::Error(_) | Outcome::Timeout))
            .count(),
    })
}

#[test]
fn test_conformance_cross_logic_summary() {
    let logics = [
        "QF_LIA",
        "QF_LRA",
        "QF_UF",
        "QF_BV",
        "QF_ABV",
        "QF_AUFLIA",
        "QF_AX",
        "QF_UFLIA",
        "QF_UFLRA",
    ];

    let logic_reports: Vec<LogicSummary> = logics.into_iter().filter_map(summarize_logic).collect();
    let grand_total = logic_reports
        .iter()
        .map(|report| report.total)
        .sum::<usize>();
    let grand_pass = logic_reports
        .iter()
        .map(|report| report.passed)
        .sum::<usize>();
    let grand_unknown = logic_reports
        .iter()
        .map(|report| report.unknown)
        .sum::<usize>();
    let grand_error = logic_reports
        .iter()
        .map(|report| report.errors)
        .sum::<usize>();

    // Print summary table
    eprintln!();
    eprintln!("=== SMT-LIB 2.6 Conformance Summary ===");
    eprintln!(
        "{:<12} {:>5} {:>5} {:>5} {:>5} {:>8}",
        "Logic", "Total", "Pass", "Unkn", "Err", "Rate"
    );
    eprintln!("{}", "-".repeat(46));

    for report in &logic_reports {
        let rate = 100.0 * (report.passed as f64 / report.total as f64);
        eprintln!(
            "{:<12} {:>5} {:>5} {:>5} {:>5} {:>7.0}%",
            report.logic, report.total, report.passed, report.unknown, report.errors, rate
        );
    }

    eprintln!("{}", "-".repeat(46));
    let grand_rate = if grand_total > 0 {
        100.0 * (grand_pass as f64 / grand_total as f64)
    } else {
        0.0
    };
    eprintln!(
        "{:<12} {:>5} {:>5} {:>5} {:>5} {:>7.0}%",
        "TOTAL", grand_total, grand_pass, grand_unknown, grand_error, grand_rate
    );

    if grand_total == 0 {
        eprintln!("SKIP: no SMT-LIB conformance corpus present");
        return;
    }

    // Soundness violations already panic in `run_conformance_logic`; this
    // threshold separately prevents broad regressions to `unknown` or errors.
    let pass_rate = grand_pass as f64 / grand_total as f64;
    assert!(
        pass_rate >= 0.75,
        "Pass rate {:.1}% is below 75% threshold ({grand_pass}/{grand_total})",
        pass_rate * 100.0
    );
}
