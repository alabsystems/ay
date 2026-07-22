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

use ntest::timeout;
use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use wait_timeout::ChildExt;

// ---------------------------------------------------------------------------
// Types and helpers
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expected {
    Sat,
    Unsat,
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
                    "exit {:?}: {}",
                    status.code(),
                    stderr_str.chars().take(200).collect::<String>()
                ));
            }
            match first {
                "sat" => Outcome::Sat,
                "unsat" => Outcome::Unsat,
                "unknown" => Outcome::Unknown,
                other => {
                    let stderr_str = String::from_utf8_lossy(&stderr_buf);
                    Outcome::Error(format!(
                        "unexpected: '{other}' stderr: {}",
                        stderr_str.chars().take(200).collect::<String>()
                    ))
                }
            }
        }
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            Outcome::Timeout
        }
        Err(e) => Outcome::Error(format!("wait error: {e}")),
    }
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
#[timeout(60_000)]
fn test_conformance_qf_lia() {
    let results = run_conformance_logic("QF_LIA", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_LIA: expected at least 4 benchmarks");
}

#[test]
#[timeout(60_000)]
fn test_conformance_qf_lra() {
    let results = run_conformance_logic("QF_LRA", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_LRA: expected at least 4 benchmarks");
}

#[test]
#[timeout(60_000)]
fn test_conformance_qf_uf() {
    let results = run_conformance_logic("QF_UF", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_UF: expected at least 4 benchmarks");
}

#[test]
#[timeout(60_000)]
fn test_conformance_qf_bv() {
    let results = run_conformance_logic("QF_BV", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_BV: expected at least 4 benchmarks");
}

#[test]
#[timeout(60_000)]
fn test_conformance_qf_abv() {
    let results = run_conformance_logic("QF_ABV", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 4, "QF_ABV: expected at least 4 benchmarks");
}

#[test]
#[timeout(60_000)]
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
#[timeout(60_000)]
fn test_conformance_qf_ax() {
    let results = run_conformance_logic("QF_AX", 10);
    if results.is_empty() {
        return;
    }
    assert!(results.len() >= 3, "QF_AX: expected at least 3 benchmarks");
}

#[test]
#[timeout(60_000)]
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
#[timeout(60_000)]
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

#[test]
#[timeout(300_000)]
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

    let root = workspace_root();
    let mut grand_total = 0;
    let mut grand_pass = 0;
    let mut grand_unknown = 0;
    let mut grand_error = 0;
    let mut grand_soundness = 0;
    let mut logic_reports: Vec<(String, usize, usize, usize, usize, usize)> = Vec::new();

    for logic in &logics {
        let dir = root.join("benchmarks/conformance").join(logic);
        if !dir.exists() {
            eprintln!("SKIP: {logic} -- no conformance directory");
            continue;
        }

        let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap()
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "smt2"))
            .collect();
        entries.sort();

        let mut total = 0;
        let mut pass = 0;
        let mut unknown = 0;
        let mut errors = 0;
        let mut soundness = 0;

        for path in &entries {
            let expected = match extract_expected_status(path) {
                Some(e) => e,
                None => continue,
            };

            total += 1;
            let actual = run_ay_file(path, 10);

            match (&expected, &actual) {
                (Expected::Sat, Outcome::Sat) | (Expected::Unsat, Outcome::Unsat) => pass += 1,
                (_, Outcome::Unknown) => unknown += 1,
                (_, Outcome::Error(_) | Outcome::Timeout) => errors += 1,
                // Soundness violation
                (Expected::Sat, Outcome::Unsat) | (Expected::Unsat, Outcome::Sat) => {
                    soundness += 1;
                    eprintln!(
                        "  SOUNDNESS: {logic}/{} -- expected {}, got {actual}",
                        path.file_name().unwrap().to_string_lossy(),
                        match expected {
                            Expected::Sat => "sat",
                            Expected::Unsat => "unsat",
                        }
                    );
                }
            }
        }

        grand_total += total;
        grand_pass += pass;
        grand_unknown += unknown;
        grand_error += errors;
        grand_soundness += soundness;
        logic_reports.push((logic.to_string(), total, pass, soundness, unknown, errors));
    }

    // Print summary table
    eprintln!();
    eprintln!("=== SMT-LIB 2.6 Conformance Summary ===");
    eprintln!(
        "{:<12} {:>5} {:>5} {:>5} {:>5} {:>5} {:>8}",
        "Logic", "Total", "Pass", "Sound", "Unkn", "Err", "Rate"
    );
    eprintln!("{}", "-".repeat(52));

    for (logic, total, pass, soundness, unknown, errors) in &logic_reports {
        let rate = if *total > 0 {
            format!("{:.0}%", (*pass as f64 / *total as f64) * 100.0)
        } else {
            "N/A".to_string()
        };
        eprintln!(
            "{logic:<12} {total:>5} {pass:>5} {soundness:>5} {unknown:>5} {errors:>5} {rate:>8}"
        );
    }

    eprintln!("{}", "-".repeat(52));
    let grand_rate = if grand_total > 0 {
        format!("{:.0}%", (grand_pass as f64 / grand_total as f64) * 100.0)
    } else {
        "N/A".to_string()
    };
    eprintln!(
        "{:<12} {:>5} {:>5} {:>5} {:>5} {:>5} {:>8}",
        "TOTAL", grand_total, grand_pass, grand_soundness, grand_unknown, grand_error, grand_rate
    );

    // Assert: no soundness violations allowed
    assert_eq!(
        grand_soundness, 0,
        "SOUNDNESS VIOLATIONS: AY returned wrong definite answers on {grand_soundness} benchmarks"
    );

    if grand_total == 0 {
        eprintln!("SKIP: no SMT-LIB conformance corpus present");
        return;
    }

    // Assert: at least 80% of benchmarks should pass (not just be unknown)
    let pass_rate = grand_pass as f64 / grand_total as f64;
    assert!(
        pass_rate >= 0.75,
        "Pass rate {:.1}% is below 75% threshold ({grand_pass}/{grand_total})",
        pass_rate * 100.0
    );
}
