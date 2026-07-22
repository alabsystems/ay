// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CaDiCaL cross-validation: AY SAT vs CaDiCaL on all available CNF benchmarks.
//!
//! Part of #4542 — differential testing expansion.
//!
//! Runs AY's SAT solver and CaDiCaL on each `.cnf` file found in
//! `benchmarks/sat/` and checks for SAT/UNSAT disagreements.
//! Skips gracefully if CaDiCaL is not built or benchmarks are missing.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;
use wait_timeout::ChildExt;

use super::common::{workspace_root, OracleResult};

/// Per-solver timeout: shorter in debug builds where AY is much slower.
const SOLVER_TIMEOUT: Duration = if cfg!(debug_assertions) {
    Duration::from_secs(3)
} else {
    Duration::from_secs(10)
};

/// Overall time budget for corpus tests: bail out before hitting the outer
/// `ntest::timeout` so we get a clean summary instead of an abrupt kill.
const CORPUS_BUDGET: Duration = if cfg!(debug_assertions) {
    Duration::from_mins(2)
} else {
    Duration::from_mins(10)
};

/// Discover all `.cnf` files under a directory, sorted smallest-first.
///
/// Smallest-first ordering maximizes the number of benchmarks tested within
/// a time budget: tiny files finish fast, so more get validated before the
/// budget is exhausted (#8138).
fn discover_cnf_benchmarks(dir: &Path) -> Vec<PathBuf> {
    let mut results = Vec::new();
    if !dir.is_dir() {
        return results;
    }
    collect_cnf_recursive(dir, &mut results);
    // Sort by file size ascending so the smallest (fastest) benchmarks run first.
    results.sort_by_key(|p| std::fs::metadata(p).map(|m| m.len()).unwrap_or(u64::MAX));
    results
}

fn collect_cnf_recursive(dir: &Path, results: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cnf_recursive(&path, results);
        } else if path.extension().is_some_and(|ext| ext == "cnf") {
            // Skip very large files (>5M lines) to avoid timeout
            results.push(path);
        }
    }
}

/// Run CaDiCaL on a CNF file with a timeout.
fn run_cadical(cadical_path: &Path, cnf_path: &Path) -> OracleResult {
    let mut child = match Command::new(cadical_path)
        .arg("-q")
        .arg(cnf_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => return OracleResult::Unavailable,
    };

    match child.wait_timeout(SOLVER_TIMEOUT) {
        Ok(Some(status)) => match status.code() {
            Some(10) => OracleResult::Sat,
            Some(20) => OracleResult::Unsat,
            _ => OracleResult::Unknown,
        },
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            OracleResult::Unknown // timeout
        }
        Err(_) => OracleResult::Unknown,
    }
}

/// Run AY SAT solver on a CNF string with a timeout via interruptible solve.
fn run_ay(cnf_content: &str) -> (OracleResult, Option<Vec<bool>>) {
    let formula = match parse_dimacs(cnf_content) {
        Ok(f) => f,
        Err(_) => return (OracleResult::Unknown, None),
    };
    let original_clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();

    let stop = Arc::new(AtomicBool::new(false));
    let stop_clone = stop.clone();
    let timeout_thread = std::thread::spawn(move || {
        std::thread::sleep(SOLVER_TIMEOUT);
        stop_clone.store(true, Ordering::Relaxed);
    });

    let result = solver
        .solve_interruptible(|| stop.load(Ordering::Relaxed))
        .into_inner();

    // Clean up timeout thread (it will exit on its own, but don't wait)
    drop(timeout_thread);

    match result {
        SatResult::Sat(ref model) => {
            // Verify model before trusting the SAT answer
            let valid = original_clauses.iter().all(|clause| {
                clause.iter().any(|lit| {
                    let idx = lit.variable().index();
                    let val = model.get(idx).copied().unwrap_or(false);
                    if lit.is_positive() {
                        val
                    } else {
                        !val
                    }
                })
            });
            if valid {
                (OracleResult::Sat, Some(model.clone()))
            } else {
                // Model validation failed — treat as bug
                panic!("AY returned SAT but model does not satisfy all clauses");
            }
        }
        SatResult::Unsat(_) => (OracleResult::Unsat, None),
        SatResult::Unknown => (OracleResult::Unknown, None),
        _ => (OracleResult::Unknown, None),
    }
}

/// CaDiCaL cross-validation on all UNSAT benchmarks under benchmarks/sat/unsat/.
///
/// These are small, fast benchmarks where both solvers should agree.
/// Uses `CORPUS_BUDGET` to bail out cleanly before the outer ntest timeout (#8138).
#[test]
#[timeout(120_000)]
fn cadical_cross_validate_unsat_benchmarks() {
    let root = workspace_root();
    let cadical_path = root.join("reference/cadical/build/cadical");
    if !cadical_path.exists() {
        eprintln!("SKIP: CaDiCaL binary not found");
        return;
    }

    let unsat_dir = root.join("benchmarks/sat/unsat");
    let benchmarks = discover_cnf_benchmarks(&unsat_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: no UNSAT benchmarks found");
        return;
    }

    let start = std::time::Instant::now();
    let mut tested = 0;
    let mut disagreements = Vec::new();

    for path in &benchmarks {
        if start.elapsed() >= CORPUS_BUDGET {
            eprintln!(
                "unsat budget exhausted after {:?} ({tested} tested)",
                start.elapsed()
            );
            break;
        }

        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let cnf = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("SKIP {name}: read error: {e}");
                continue;
            }
        };

        let (ay_result, cadical_result) = run_both_solvers(&cadical_path, path, &cnf);

        if cadical_result == OracleResult::Unknown || ay_result == OracleResult::Unknown {
            eprintln!(
                "SKIP {name}: timeout or unknown (cadical={cadical_result:?}, ay={ay_result:?})"
            );
            continue;
        }

        tested += 1;
        if ay_result != cadical_result {
            disagreements.push(format!(
                "{name}: AY={ay_result:?} CaDiCaL={cadical_result:?}"
            ));
        }
    }

    eprintln!(
        "CaDiCaL cross-validate UNSAT: {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "CaDiCaL cross-validation disagreements on UNSAT benchmarks:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested > 0,
        "Expected at least 1 UNSAT benchmark to be tested"
    );
}

/// Run AY and CaDiCaL in parallel on a single benchmark.
///
/// Returns `(ay_result, cadical_result)`. Running both solvers concurrently
/// nearly halves the wall-clock time per benchmark (#8138).
fn run_both_solvers(
    cadical_path: &Path,
    cnf_path: &Path,
    cnf_content: &str,
) -> (OracleResult, OracleResult) {
    std::thread::scope(|s| {
        let cadical_handle = s.spawn(|| run_cadical(cadical_path, cnf_path));
        let (ay_result, _model) = run_ay(cnf_content);
        let cadical_result = cadical_handle.join().expect("cadical thread panicked");
        (ay_result, cadical_result)
    })
}

/// CaDiCaL cross-validation on SAT-COMP sample benchmarks.
///
/// Runs AY and CaDiCaL on available CNF files from benchmarks/sat/
/// (excluding the unsat/ subdir which has its own test).
/// Uses a per-solver timeout (shorter in debug) and a corpus-level
/// time budget to keep the test bounded (#8138).
#[test]
#[timeout(600_000)]
fn cadical_cross_validate_satcomp_benchmarks() {
    let root = workspace_root();
    let cadical_path = root.join("reference/cadical/build/cadical");
    if !cadical_path.exists() {
        eprintln!("SKIP: CaDiCaL binary not found");
        return;
    }

    let sat_dir = root.join("benchmarks/sat");
    let all_benchmarks = discover_cnf_benchmarks(&sat_dir);

    // Filter out the unsat/ subdir (tested separately) and very large files
    let benchmarks: Vec<_> = all_benchmarks
        .into_iter()
        .filter(|p| {
            let in_unsat = p.components().any(|c| c.as_os_str() == "unsat");
            if in_unsat {
                return false;
            }
            // Skip files larger than 500KB to avoid timeouts
            match std::fs::metadata(p) {
                Ok(meta) => meta.len() < 500_000,
                Err(_) => false,
            }
        })
        .collect();

    if benchmarks.is_empty() {
        eprintln!("SKIP: no SAT-COMP benchmarks found (or all too large)");
        return;
    }

    let start = std::time::Instant::now();
    let mut tested = 0;
    let mut skipped_timeout = 0;
    let mut disagreements = Vec::new();

    for path in &benchmarks {
        if start.elapsed() >= CORPUS_BUDGET {
            eprintln!(
                "satcomp budget exhausted after {:?} ({tested} tested)",
                start.elapsed()
            );
            break;
        }

        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let cnf = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("SKIP {name}: read error: {e}");
                continue;
            }
        };

        let (ay_result, cadical_result) = run_both_solvers(&cadical_path, path, &cnf);

        if cadical_result == OracleResult::Unknown || ay_result == OracleResult::Unknown {
            skipped_timeout += 1;
            continue;
        }

        tested += 1;
        if ay_result != cadical_result {
            disagreements.push(format!(
                "{name}: AY={ay_result:?} CaDiCaL={cadical_result:?}"
            ));
        }
    }

    eprintln!(
        "CaDiCaL cross-validate SAT-COMP: {tested} tested, {skipped_timeout} skipped (timeout), {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "CaDiCaL cross-validation disagreements on SAT-COMP benchmarks:\n{}",
        disagreements.join("\n")
    );
}

/// CaDiCaL cross-validation across the full benchmarks/sat/ tree.
///
/// This is a summary test that reports overall statistics.
/// It covers all available CNF benchmarks including 2022, 2023, and SAT-COMP
/// 2024 samples, with a per-solver timeout and an overall time budget.
///
/// In debug builds this test is compiled out (#8146): the `unsat_benchmarks`
/// and `satcomp_benchmarks` tests already provide complete coverage of the
/// same corpus without the redundant re-testing. This avoids the combined
/// wall-clock time of three overlapping corpus scans in slow debug builds.
///
/// Optimization (#8138): AY and CaDiCaL run in parallel per-benchmark via
/// `std::thread::scope`, and benchmarks are sorted smallest-first to
/// maximize coverage within the time budget.
#[test]
#[cfg(not(debug_assertions))]
#[timeout(700_000)]
fn cadical_cross_validate_full_corpus() {
    let root = workspace_root();
    let cadical_path = root.join("reference/cadical/build/cadical");
    if !cadical_path.exists() {
        eprintln!("SKIP: CaDiCaL binary not found");
        return;
    }

    let sat_dir = root.join("benchmarks/sat");
    // discover_cnf_benchmarks already sorts smallest-first (#8138).
    let benchmarks = discover_cnf_benchmarks(&sat_dir);
    if benchmarks.is_empty() {
        eprintln!("SKIP: no CNF benchmarks found");
        return;
    }

    let start = std::time::Instant::now();
    let mut tested = 0;
    let mut both_sat = 0;
    let mut both_unsat = 0;
    let mut skipped = 0;
    let mut budget_exhausted = false;
    let mut disagreements = Vec::new();

    // In debug builds, use a tighter file-size limit to avoid slow formulas.
    let max_file_size: u64 = if cfg!(debug_assertions) {
        500_000
    } else {
        2_000_000
    };

    for path in &benchmarks {
        // Check overall time budget before each benchmark.
        if start.elapsed() >= CORPUS_BUDGET {
            eprintln!(
                "corpus budget exhausted after {:?} ({tested} tested, {skipped} skipped)",
                start.elapsed()
            );
            budget_exhausted = true;
            break;
        }

        let name = path
            .strip_prefix(&sat_dir)
            .unwrap_or(path)
            .to_string_lossy()
            .to_string();

        // Skip very large files
        let file_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(u64::MAX);
        if file_size > max_file_size {
            skipped += 1;
            continue;
        }

        let cnf = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };

        // Run AY and CaDiCaL in parallel to nearly halve wall-clock time (#8138).
        let (ay_result, cadical_result) = run_both_solvers(&cadical_path, path, &cnf);

        if cadical_result == OracleResult::Unknown || ay_result == OracleResult::Unknown {
            skipped += 1;
            continue;
        }

        tested += 1;
        match (ay_result, cadical_result) {
            (OracleResult::Sat, OracleResult::Sat) => both_sat += 1,
            (OracleResult::Unsat, OracleResult::Unsat) => both_unsat += 1,
            _ => {
                disagreements.push(format!(
                    "{name}: AY={ay_result:?} CaDiCaL={cadical_result:?}"
                ));
            }
        }
    }

    eprintln!(
        "CaDiCaL cross-validate full corpus: {tested} tested ({both_sat} SAT, {both_unsat} UNSAT), \
         {skipped} skipped, {} disagreements, elapsed {:?}{}",
        disagreements.len(),
        start.elapsed(),
        if budget_exhausted { " (budget exhausted)" } else { "" },
    );
    assert!(
        disagreements.is_empty(),
        "CaDiCaL cross-validation disagreements:\n{}",
        disagreements.join("\n")
    );
    // The available benchmark corpus has ~31 CNF files. The UNSAT subdir
    // (26 files) and a few small SAT files typically pass within the budget.
    assert!(
        tested >= 5,
        "Expected at least 5 benchmarks tested, got {tested}"
    );
}
