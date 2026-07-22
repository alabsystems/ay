// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PAR-2 benchmark harness for AY SAT solver.
//!
//! Computes PAR-2 scores over a held-out corpus of 100+ SAT instances.
//! PAR-2 scoring: for each instance, if solved within timeout T, score = wall-clock
//! time in seconds; if not solved (timeout or unknown), score = 2*T. Total PAR-2 is
//! the sum of all instance scores.
//!
//! **Gating:** This test is gated behind the `AY_PAR2_BENCHMARK` environment variable.
//! It will NOT run during normal `cargo test`. To run:
//!
//! ```bash
//! AY_PAR2_BENCHMARK=1 cargo test -p ay-sat --release --test par2_benchmark -- --nocapture
//! ```
//!
//! **Corpus sources (in search order):**
//! 1. `benchmarks/sat/` — hand-curated SAT instances (UNSAT, SAT-COMP 2024, eq_atree_braun, etc.)
//! 2. `benchmarks/satcomp/` — additional SAT competition instances
//! 3. `reference/creusat/tests/cnf-hard/sat/` — 100 uf250 uniform random 3-SAT instances
//! 4. `reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/` — SAT-2009 preprocessed
//! 5. `reference/creusat/tests/cnf-hard/` — remaining hard instances (manol-pipe, ddr, etc.)
//!
//! Part of #7925 — held-out PAR-2 benchmark harness.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use super::common::workspace_root;
use ay_sat::{parse_dimacs, SatResult};

/// Per-instance timeout in seconds.
const TIMEOUT_SECS: u64 = 5;
/// Per-instance timeout as `Duration`.
const TIMEOUT: Duration = Duration::from_secs(TIMEOUT_SECS);

/// Result of a single benchmark instance.
#[derive(Debug)]
struct InstanceResult {
    /// Relative path from workspace root (for display).
    name: String,
    /// Outcome: Sat, Unsat, Timeout, ParseError, ReadError.
    outcome: Outcome,
    /// Wall-clock time spent solving (includes parse time for simplicity).
    wall_time: Duration,
    /// PAR-2 score contribution: wall_time if solved, 2*T if not.
    par2_score: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Sat,
    Unsat,
    Timeout,
    ParseError,
    ReadError,
}

impl std::fmt::Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "SAT"),
            Self::Unsat => write!(f, "UNSAT"),
            Self::Timeout => write!(f, "TIMEOUT"),
            Self::ParseError => write!(f, "PARSE_ERR"),
            Self::ReadError => write!(f, "READ_ERR"),
        }
    }
}

/// Recursively discover all `.cnf` files under `dir`.
fn discover_cnf_files(dir: &Path) -> Vec<PathBuf> {
    let mut results = Vec::new();
    if !dir.is_dir() {
        return results;
    }
    collect_cnf_recursive(dir, &mut results);
    results.sort();
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
            results.push(path);
        }
    }
}

/// Deduplicate paths by canonical path, preserving order of first occurrence.
fn dedup_by_canonical(paths: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::with_capacity(paths.len());
    for p in paths {
        let canonical = p.canonicalize().unwrap_or_else(|_| p.clone());
        if seen.insert(canonical) {
            result.push(p);
        }
    }
    result
}

/// Build the full benchmark corpus from all known source directories.
fn build_corpus(root: &Path) -> Vec<PathBuf> {
    let search_dirs = [
        // Primary: hand-curated benchmarks
        root.join("benchmarks/sat"),
        root.join("benchmarks/satcomp"),
        // Secondary: CreuSAT reference corpus (uf250 + harder instances)
        root.join("reference/creusat/tests/cnf-hard/sat"),
        root.join("reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy"),
        // Tertiary: remaining hard instances (manol-pipe, ddr, etc.)
        root.join("reference/creusat/tests/cnf-hard"),
        // SAT-race 2015 instances (if present)
        root.join("reference/creusat/tests/2015"),
    ];

    let mut all_paths = Vec::new();
    for dir in &search_dirs {
        all_paths.extend(discover_cnf_files(dir));
    }
    dedup_by_canonical(all_paths)
}

/// Run AY SAT solver on a CNF string with the configured timeout.
///
/// Returns (outcome, wall_time).
fn run_ay_timed(cnf_content: &str) -> (Outcome, Duration) {
    let start = Instant::now();

    let formula = match parse_dimacs(cnf_content) {
        Ok(f) => f,
        Err(_) => return (Outcome::ParseError, start.elapsed()),
    };
    let mut solver = formula.into_solver();

    let stop = Arc::new(AtomicBool::new(false));
    let stop_clone = stop.clone();
    let timeout_thread = std::thread::spawn(move || {
        std::thread::sleep(TIMEOUT);
        stop_clone.store(true, Ordering::Relaxed);
    });

    let result = solver
        .solve_interruptible(|| stop.load(Ordering::Relaxed))
        .into_inner();

    let elapsed = start.elapsed();

    // Clean up: the timeout thread will eventually exit on its own.
    drop(timeout_thread);

    let outcome = match result {
        SatResult::Sat(_) => Outcome::Sat,
        SatResult::Unsat(_) => Outcome::Unsat,
        SatResult::Unknown => Outcome::Timeout,
        _ => Outcome::Timeout,
    };

    (outcome, elapsed)
}

/// Compute PAR-2 score for a single instance.
fn par2_score(outcome: Outcome, wall_time: Duration) -> f64 {
    match outcome {
        Outcome::Sat | Outcome::Unsat => wall_time.as_secs_f64(),
        Outcome::Timeout | Outcome::ParseError | Outcome::ReadError => 2.0 * TIMEOUT_SECS as f64,
    }
}

/// Format a duration for table display.
fn fmt_duration(d: Duration) -> String {
    let secs = d.as_secs_f64();
    if secs < 0.001 {
        format!("{:.1}us", secs * 1_000_000.0)
    } else if secs < 1.0 {
        format!("{:.1}ms", secs * 1000.0)
    } else {
        format!("{secs:.3}s")
    }
}

/// The main PAR-2 benchmark test.
///
/// Gated behind `AY_PAR2_BENCHMARK=1` to avoid running during normal `cargo test`.
#[test]
fn par2_benchmark_corpus() {
    if std::env::var("AY_PAR2_BENCHMARK").is_err() {
        eprintln!(
            "SKIP: PAR-2 benchmark not enabled. Set AY_PAR2_BENCHMARK=1 to run.\n\
             Example: AY_PAR2_BENCHMARK=1 cargo test -p ay-sat --release \
             --test par2_benchmark -- --nocapture"
        );
        return;
    }

    let root = workspace_root();
    let corpus = build_corpus(&root);

    if corpus.is_empty() {
        eprintln!(
            "SKIP: No CNF benchmark files found. Expected files in:\n\
             - benchmarks/sat/\n\
             - benchmarks/satcomp/\n\
             - reference/creusat/tests/cnf-hard/sat/"
        );
        return;
    }

    eprintln!(
        "PAR-2 benchmark: {} instances, timeout={}s",
        corpus.len(),
        TIMEOUT_SECS
    );
    eprintln!("{}", "=".repeat(100));
    eprintln!(
        "{:<60} {:>10} {:>10} {:>10} {:>8}",
        "Instance", "Size", "Result", "Time", "PAR-2"
    );
    eprintln!("{}", "-".repeat(100));

    let mut results: Vec<InstanceResult> = Vec::with_capacity(corpus.len());

    for path in &corpus {
        let name = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .to_string_lossy()
            .to_string();

        let file_bytes = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);

        // Read the file
        let cnf_content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => {
                let score = par2_score(Outcome::ReadError, Duration::ZERO);
                let inst = InstanceResult {
                    name: name.clone(),
                    outcome: Outcome::ReadError,
                    wall_time: Duration::ZERO,
                    par2_score: score,
                };
                eprintln!(
                    "{:<60} {:>9}B {:>10} {:>10} {:>8.2}",
                    truncate_name(&name, 60),
                    file_bytes,
                    inst.outcome,
                    fmt_duration(inst.wall_time),
                    inst.par2_score
                );
                results.push(inst);
                continue;
            }
        };

        let (outcome, wall_time) = run_ay_timed(&cnf_content);
        let score = par2_score(outcome, wall_time);

        let inst = InstanceResult {
            name: name.clone(),
            outcome,
            wall_time,
            par2_score: score,
        };

        eprintln!(
            "{:<60} {:>9}B {:>10} {:>10} {:>8.2}",
            truncate_name(&name, 60),
            file_bytes,
            inst.outcome,
            fmt_duration(inst.wall_time),
            inst.par2_score
        );

        results.push(inst);
    }

    // --- Summary ---
    eprintln!("{}", "=".repeat(100));

    let total_instances = results.len();
    let solved_sat = results.iter().filter(|r| r.outcome == Outcome::Sat).count();
    let solved_unsat = results
        .iter()
        .filter(|r| r.outcome == Outcome::Unsat)
        .count();
    let timeouts = results
        .iter()
        .filter(|r| r.outcome == Outcome::Timeout)
        .count();
    let parse_errors = results
        .iter()
        .filter(|r| r.outcome == Outcome::ParseError)
        .count();
    let read_errors = results
        .iter()
        .filter(|r| r.outcome == Outcome::ReadError)
        .count();
    let solved_total = solved_sat + solved_unsat;
    let total_par2: f64 = results.iter().map(|r| r.par2_score).sum();
    let avg_par2 = if total_instances > 0 {
        total_par2 / total_instances as f64
    } else {
        0.0
    };

    let total_solve_time: Duration = results
        .iter()
        .filter(|r| r.outcome == Outcome::Sat || r.outcome == Outcome::Unsat)
        .map(|r| r.wall_time)
        .sum();

    // Virtual best score (all solved instantly = 0)
    // Virtual worst score (all timed out = 2*T*N)
    let vbs = 0.0_f64;
    let vws = 2.0 * TIMEOUT_SECS as f64 * total_instances as f64;

    eprintln!();
    eprintln!("PAR-2 BENCHMARK SUMMARY");
    eprintln!("{}", "-".repeat(50));
    eprintln!("Corpus size:         {total_instances}");
    eprintln!("Solved:              {solved_total} ({solved_sat} SAT + {solved_unsat} UNSAT)");
    eprintln!("Timeouts:            {timeouts}");
    if parse_errors > 0 {
        eprintln!("Parse errors:        {parse_errors}");
    }
    if read_errors > 0 {
        eprintln!("Read errors:         {read_errors}");
    }
    eprintln!(
        "Solve rate:          {:.1}%",
        if total_instances > 0 {
            100.0 * solved_total as f64 / total_instances as f64
        } else {
            0.0
        }
    );
    eprintln!(
        "Total solve time:    {:.3}s",
        total_solve_time.as_secs_f64()
    );
    eprintln!("{}", "-".repeat(50));
    eprintln!("PAR-2 total:         {total_par2:.2}");
    eprintln!("PAR-2 average:       {avg_par2:.4}");
    eprintln!("Virtual best (VBS):  {vbs:.2}");
    eprintln!("Virtual worst (VWS): {vws:.2}");
    eprintln!(
        "PAR-2 normalized:    {:.4} (0=VBS, 1=VWS)",
        if vws > 0.0 { total_par2 / vws } else { 0.0 }
    );
    eprintln!("Timeout:             {TIMEOUT_SECS}s per instance");
    eprintln!("{}", "-".repeat(50));

    // Print slowest solved instances
    let mut solved: Vec<&InstanceResult> = results
        .iter()
        .filter(|r| r.outcome == Outcome::Sat || r.outcome == Outcome::Unsat)
        .collect();
    solved.sort_by(|a, b| b.wall_time.cmp(&a.wall_time));

    if !solved.is_empty() {
        let top_n = solved.len().min(10);
        eprintln!();
        eprintln!("TOP {top_n} SLOWEST SOLVED INSTANCES:");
        eprintln!("{:<60} {:>10} {:>10}", "Instance", "Result", "Time");
        for inst in &solved[..top_n] {
            eprintln!(
                "{:<60} {:>10} {:>10}",
                truncate_name(&inst.name, 60),
                inst.outcome,
                fmt_duration(inst.wall_time)
            );
        }
    }

    // Print timed-out instances
    let timed_out: Vec<&InstanceResult> = results
        .iter()
        .filter(|r| r.outcome == Outcome::Timeout)
        .collect();
    if !timed_out.is_empty() {
        let show_n = timed_out.len().min(20);
        eprintln!();
        eprintln!(
            "TIMED OUT INSTANCES ({} total, showing {show_n}):",
            timed_out.len()
        );
        for inst in &timed_out[..show_n] {
            eprintln!("  {}", inst.name);
        }
        if timed_out.len() > show_n {
            eprintln!("  ... and {} more", timed_out.len() - show_n);
        }
    }

    eprintln!();

    // Sanity check: we expect 100+ instances in the corpus.
    assert!(
        total_instances >= 100,
        "PAR-2 corpus too small: found {total_instances} instances, expected >= 100. \
         Ensure benchmarks/sat/ and reference/creusat/tests/cnf-hard/sat/ are populated."
    );

    // Informational: no assertion on PAR-2 score itself. This harness reports
    // the score for tracking; regressions should be caught by comparing scores
    // across commits, not by a fixed threshold.
    eprintln!(
        "PAR-2 benchmark complete: {total_instances} instances, \
         {solved_total} solved, PAR-2={total_par2:.2}"
    );
}

/// Truncate a name for table display, adding "..." prefix if needed.
fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else {
        let suffix_len = max_len.saturating_sub(3);
        format!("...{}", &name[name.len() - suffix_len..])
    }
}

#[cfg(test)]
mod unit {
    use super::*;

    #[test]
    fn par2_score_solved_uses_wall_time() {
        let score = par2_score(Outcome::Sat, Duration::from_millis(1234));
        assert!((score - 1.234).abs() < 0.01);
    }

    #[test]
    fn par2_score_timeout_uses_penalty() {
        let score = par2_score(Outcome::Timeout, Duration::from_secs(5));
        assert!((score - 10.0).abs() < f64::EPSILON);
    }

    #[test]
    fn par2_score_parse_error_uses_penalty() {
        let score = par2_score(Outcome::ParseError, Duration::ZERO);
        assert!((score - 10.0).abs() < f64::EPSILON);
    }

    #[test]
    fn truncate_short_name_unchanged() {
        assert_eq!(truncate_name("foo.cnf", 60), "foo.cnf");
    }

    #[test]
    fn truncate_long_name_ellipsis() {
        let long = "a".repeat(80);
        let truncated = truncate_name(&long, 60);
        assert!(truncated.len() <= 60);
        assert!(truncated.starts_with("..."));
    }

    #[test]
    fn dedup_handles_duplicates() {
        // Use paths that exist on the filesystem for canonical resolution.
        let root = workspace_root();
        let p = root.join("Cargo.toml");
        let paths = vec![p.clone(), p];
        let deduped = dedup_by_canonical(paths);
        assert_eq!(deduped.len(), 1);
    }

    #[test]
    fn corpus_discovery_finds_files() {
        let root = workspace_root();
        let corpus = build_corpus(&root);
        // Even without all reference submodules, benchmarks/sat/ should have files.
        // Do not assert a specific count here; the main test asserts >= 100.
        eprintln!(
            "corpus_discovery_finds_files: found {} CNF files",
            corpus.len()
        );
    }
}
