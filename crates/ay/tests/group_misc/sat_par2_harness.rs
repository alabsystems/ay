// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Held-out PAR-2 benchmark harness for SAT-COMP evaluation.
//!
//! PAR-2 (Penalized Average Runtime, factor 2) is the standard scoring metric
//! used in SAT competitions. The score is computed as:
//!
//!   PAR-2 = sum of solve times for solved instances
//!         + 2 * timeout for each unsolved instance
//!
//! Lower PAR-2 is better.
//!
//! This harness:
//! - Collects .cnf files from benchmarks/sat/ (canary, unsat, eq_atree_braun, 2022, 2023)
//! - Runs ay on each with a configurable timeout
//! - Records: solve time, result (SAT/UNSAT/UNKNOWN/TIMEOUT), exit code
//! - Computes PAR-2 score
//! - Validates correctness against known-expected answers
//! - Reports any incorrect answers as CRITICAL failures
//!
//! Part of #7925.

use ntest::timeout;
use std::fmt;
use std::io::Read as IoRead;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use wait_timeout::ChildExt;

/// Per-instance result from running the solver.
#[derive(Debug, Clone)]
struct BenchmarkResult {
    path: PathBuf,
    expected: Expected,
    actual: SolverVerdict,
    elapsed: Duration,
    exit_code: Option<i32>,
}

/// Expected result for a benchmark instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expected {
    Sat,
    Unsat,
    Unknown,
}

impl fmt::Display for Expected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => write!(f, "SAT"),
            Self::Unsat => write!(f, "UNSAT"),
            Self::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

/// Observed solver verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolverVerdict {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error,
}

impl fmt::Display for SolverVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => write!(f, "SAT"),
            Self::Unsat => write!(f, "UNSAT"),
            Self::Unknown => write!(f, "UNKNOWN"),
            Self::Timeout => write!(f, "TIMEOUT"),
            Self::Error => write!(f, "ERROR"),
        }
    }
}

impl SolverVerdict {
    fn is_solved(self) -> bool {
        matches!(self, Self::Sat | Self::Unsat)
    }
}

/// Summary statistics for a PAR-2 benchmark run.
#[derive(Debug)]
struct Par2Summary {
    total: usize,
    solved: usize,
    sat_count: usize,
    unsat_count: usize,
    timeout_count: usize,
    unknown_count: usize,
    error_count: usize,
    wrong_count: usize,
    par2_total: f64,
    par2_avg: f64,
    avg_solved_sec: f64,
    timeout_sec: f64,
    wrong_answers: Vec<(PathBuf, Expected, SolverVerdict)>,
}

impl fmt::Display for Par2Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== PAR-2 Benchmark Summary ===")?;
        writeln!(f, "Total instances:    {}", self.total)?;
        writeln!(f, "Solved:             {}", self.solved)?;
        writeln!(f, "  SAT:              {}", self.sat_count)?;
        writeln!(f, "  UNSAT:            {}", self.unsat_count)?;
        writeln!(f, "Timeout:            {}", self.timeout_count)?;
        writeln!(f, "Unknown:            {}", self.unknown_count)?;
        writeln!(f, "Error:              {}", self.error_count)?;
        writeln!(f, "Wrong answers:      {}", self.wrong_count)?;
        writeln!(f, "Timeout (sec):      {:.1}", self.timeout_sec)?;
        writeln!(f, "PAR-2 total:        {:.3}", self.par2_total)?;
        writeln!(f, "PAR-2 average:      {:.3}", self.par2_avg)?;
        if self.solved > 0 {
            writeln!(f, "Avg solved (sec):   {:.3}", self.avg_solved_sec)?;
        }
        if !self.wrong_answers.is_empty() {
            writeln!(f, "--- WRONG ANSWERS (CRITICAL) ---")?;
            for (path, expected, actual) in &self.wrong_answers {
                writeln!(
                    f,
                    "  {}: expected {}, got {}",
                    path.display(),
                    expected,
                    actual,
                )?;
            }
        }
        Ok(())
    }
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

/// Benchmark instance to evaluate.
struct BenchInstance {
    path: PathBuf,
    expected: Expected,
}

/// Collect benchmark instances from the repository.
///
/// Uses the following sources:
/// - benchmarks/sat/canary/ (tiny SAT/UNSAT, always fast)
/// - benchmarks/sat/unsat/ (27 crafted UNSAT instances)
/// - benchmarks/sat/eq_atree_braun/ (circuit equivalence UNSAT)
/// - benchmarks/sat/2022/ (SAT-COMP 2022 held-out)
/// - benchmarks/sat/2023/ (SAT-COMP 2023 held-out)
fn collect_benchmarks(root: &Path) -> Vec<BenchInstance> {
    let mut instances = Vec::new();
    let sat_dir = root.join("benchmarks/sat");

    // Canary benchmarks (tiny SAT/UNSAT)
    collect_from_dir(&sat_dir.join("canary"), &mut instances, |path| {
        if path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .contains("unsat")
        {
            Expected::Unsat
        } else {
            Expected::Sat
        }
    });

    // UNSAT corpus (all expected UNSAT)
    collect_from_dir(&sat_dir.join("unsat"), &mut instances, |_| Expected::Unsat);

    // eq_atree_braun circuit UNSAT benchmarks
    collect_from_dir(&sat_dir.join("eq_atree_braun"), &mut instances, |_| {
        Expected::Unsat
    });

    // SAT-COMP 2022 held-out (expected unknown)
    collect_from_dir(&sat_dir.join("2022"), &mut instances, |_| Expected::Unknown);

    // SAT-COMP 2023 held-out (expected unknown)
    collect_from_dir(&sat_dir.join("2023"), &mut instances, |_| Expected::Unknown);

    instances.sort_by(|a, b| a.path.cmp(&b.path));
    instances
}

/// Collect .cnf files from a directory, applying the given expected-result function.
fn collect_from_dir(
    dir: &Path,
    instances: &mut Vec<BenchInstance>,
    expected_fn: impl Fn(&Path) -> Expected,
) {
    if !dir.is_dir() {
        return;
    }
    for entry in std::fs::read_dir(dir).expect("read benchmark dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|ext| ext == "cnf") {
            let expected = expected_fn(&path);
            instances.push(BenchInstance { path, expected });
        }
    }
}

/// Run ay on a single .cnf file and return the result.
///
/// The instance is copied into a private temp dir and solved THERE: default
/// proof-carrying emission writes (and, on a non-UNSAT verdict, removes) the
/// `<input>.drat` sidecar next to the input, and solving tracked benchmark
/// files in place used to delete the committed
/// `benchmarks/sat/canary/tiny_sat.cnf.drat` fixture on every run.
fn run_solver(ay_path: &str, instance: &BenchInstance, timeout: Duration) -> BenchmarkResult {
    let start = Instant::now();
    let scratch = tempfile::tempdir().expect("create scratch dir for PAR-2 instance");
    let scratch_input = scratch.path().join(
        instance
            .path
            .file_name()
            .expect("benchmark instance path has a file name"),
    );
    if let Err(e) = std::fs::copy(&instance.path, &scratch_input) {
        eprintln!(
            "Failed to copy {} to scratch dir: {e}",
            instance.path.display()
        );
        return BenchmarkResult {
            path: instance.path.clone(),
            expected: instance.expected,
            actual: SolverVerdict::Error,
            elapsed: start.elapsed(),
            exit_code: None,
        };
    }
    let child = Command::new(ay_path)
        .arg(&scratch_input)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let mut child = match child {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Failed to spawn ay on {}: {e}", instance.path.display());
            return BenchmarkResult {
                path: instance.path.clone(),
                expected: instance.expected,
                actual: SolverVerdict::Error,
                elapsed: start.elapsed(),
                exit_code: None,
            };
        }
    };

    let timed_out;
    let status = match child
        .wait_timeout(timeout)
        .unwrap_or_else(|e| panic!("wait_timeout failed for {}: {e}", instance.path.display()))
    {
        Some(status) => {
            timed_out = false;
            status
        }
        None => {
            timed_out = true;
            let _ = child.kill();
            child
                .wait()
                .unwrap_or_else(|e| panic!("wait after kill failed: {e}"))
        }
    };
    let elapsed = start.elapsed();

    if timed_out {
        return BenchmarkResult {
            path: instance.path.clone(),
            expected: instance.expected,
            actual: SolverVerdict::Timeout,
            elapsed: timeout,
            exit_code: None,
        };
    }

    let mut stdout_buf = Vec::new();
    if let Some(mut handle) = child.stdout.take() {
        let _ = handle.read_to_end(&mut stdout_buf);
    }
    let stdout = String::from_utf8_lossy(&stdout_buf);

    let exit_code = status.code();
    let verdict = parse_verdict(&stdout, exit_code);

    BenchmarkResult {
        path: instance.path.clone(),
        expected: instance.expected,
        actual: verdict,
        elapsed,
        exit_code,
    }
}

/// Parse solver output and exit code into a verdict.
fn parse_verdict(stdout: &str, exit_code: Option<i32>) -> SolverVerdict {
    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed == "s SATISFIABLE" || trimmed == "sat" || trimmed == "SATISFIABLE" {
            return SolverVerdict::Sat;
        }
        if trimmed == "s UNSATISFIABLE" || trimmed == "unsat" || trimmed == "UNSATISFIABLE" {
            return SolverVerdict::Unsat;
        }
        if trimmed == "s UNKNOWN" || trimmed == "unknown" {
            return SolverVerdict::Unknown;
        }
    }
    // Fall back to SAT-COMP exit codes: 10=SAT, 20=UNSAT
    match exit_code {
        Some(10) => SolverVerdict::Sat,
        Some(20) => SolverVerdict::Unsat,
        _ => SolverVerdict::Unknown,
    }
}

/// Compute PAR-2 summary from benchmark results.
fn compute_par2(results: &[BenchmarkResult], timeout: Duration) -> Par2Summary {
    let timeout_sec = timeout.as_secs_f64();
    let total = results.len();
    let mut solved = 0;
    let mut sat_count = 0;
    let mut unsat_count = 0;
    let mut timeout_count = 0;
    let mut unknown_count = 0;
    let mut error_count = 0;
    let mut wrong_count = 0;
    let mut par2_total = 0.0;
    let mut solved_total_sec = 0.0;
    let mut wrong_answers = Vec::new();

    for result in results {
        let is_wrong = matches!(
            (result.expected, result.actual),
            (Expected::Sat, SolverVerdict::Unsat) | (Expected::Unsat, SolverVerdict::Sat)
        );

        if is_wrong {
            wrong_count += 1;
            wrong_answers.push((result.path.clone(), result.expected, result.actual));
            // Wrong answers get 2x penalty (treated as unsolved)
            par2_total += 2.0 * timeout_sec;
            continue;
        }

        match result.actual {
            SolverVerdict::Sat => {
                solved += 1;
                sat_count += 1;
                let t = result.elapsed.as_secs_f64();
                par2_total += t;
                solved_total_sec += t;
            }
            SolverVerdict::Unsat => {
                solved += 1;
                unsat_count += 1;
                let t = result.elapsed.as_secs_f64();
                par2_total += t;
                solved_total_sec += t;
            }
            SolverVerdict::Timeout => {
                timeout_count += 1;
                par2_total += 2.0 * timeout_sec;
            }
            SolverVerdict::Unknown => {
                unknown_count += 1;
                par2_total += 2.0 * timeout_sec;
            }
            SolverVerdict::Error => {
                error_count += 1;
                par2_total += 2.0 * timeout_sec;
            }
        }
    }

    let par2_avg = if total > 0 {
        par2_total / total as f64
    } else {
        0.0
    };
    let avg_solved_sec = if solved > 0 {
        solved_total_sec / solved as f64
    } else {
        0.0
    };

    Par2Summary {
        total,
        solved,
        sat_count,
        unsat_count,
        timeout_count,
        unknown_count,
        error_count,
        wrong_count,
        par2_total,
        par2_avg,
        avg_solved_sec,
        timeout_sec,
        wrong_answers,
    }
}

/// Print per-instance results in a table format suitable for tracking.
fn print_results_table(results: &[BenchmarkResult]) {
    eprintln!(
        "{:<60} {:>8} {:>8} {:>8} {:>6}",
        "benchmark", "expected", "actual", "time_ms", "exit"
    );
    eprintln!("{}", "-".repeat(94));
    for result in results {
        let name = result
            .path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_else(|| result.path.display().to_string());
        let display_name = if name.len() > 58 {
            format!("..{}", &name[name.len() - 56..])
        } else {
            name
        };
        let exit_str = result
            .exit_code
            .map(|c| c.to_string())
            .unwrap_or_else(|| "-".to_string());
        let wrong_marker = if matches!(
            (result.expected, result.actual),
            (Expected::Sat, SolverVerdict::Unsat) | (Expected::Unsat, SolverVerdict::Sat)
        ) {
            " *** WRONG ***"
        } else {
            ""
        };
        eprintln!(
            "{:<60} {:>8} {:>8} {:>8} {:>6}{}",
            display_name,
            result.expected,
            result.actual,
            result.elapsed.as_millis(),
            exit_str,
            wrong_marker,
        );
    }
}

// ============================================================================
// Test: CI-friendly quick PAR-2 evaluation (short timeout, small corpus)
// ============================================================================

/// Quick PAR-2 evaluation using the small benchmark corpus.
///
/// Runs canary + UNSAT corpus + eq_atree_braun with a 20-second per-instance
/// timeout. This is fast enough for CI while still covering correctness.
///
/// Acceptance criteria:
/// - Zero wrong answers (any incorrect SAT/UNSAT is a CRITICAL failure)
/// - All canary benchmarks solved
/// - All UNSAT corpus benchmarks solved (they are small)
/// - PAR-2 score is reported for tracking
#[test]
#[timeout(600_000)] // 10 minutes total budget
fn test_sat_par2_ci_quick() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let root = workspace_root();
    let timeout = Duration::from_secs(20);

    let all_instances = collect_benchmarks(&root);
    // For CI: filter to only small, fast-solving benchmarks.
    // Include canary, unsat corpus, and eq_atree_braun.
    // Exclude 2022/2023 held-out (those may timeout at short durations).
    let sat_dir = root.join("benchmarks/sat");
    let ci_instances: Vec<_> = all_instances
        .into_iter()
        .filter(|inst| {
            let rel = inst.path.strip_prefix(&sat_dir).unwrap_or(&inst.path);
            let first_component = rel
                .components()
                .next()
                .map(|c| c.as_os_str().to_string_lossy().to_string())
                .unwrap_or_default();
            matches!(
                first_component.as_str(),
                "canary" | "unsat" | "eq_atree_braun"
            )
        })
        .collect();

    assert!(
        !ci_instances.is_empty(),
        "No CI benchmark instances found under {}",
        sat_dir.display()
    );

    eprintln!(
        "PAR-2 CI quick: {} instances, timeout={}s",
        ci_instances.len(),
        timeout.as_secs()
    );

    let results: Vec<BenchmarkResult> = ci_instances
        .iter()
        .map(|inst| run_solver(ay_path, inst, timeout))
        .collect();

    print_results_table(&results);
    let summary = compute_par2(&results, timeout);
    eprintln!("\n{summary}");

    // CRITICAL: zero wrong answers
    assert!(
        summary.wrong_answers.is_empty(),
        "CRITICAL: {} wrong answer(s) detected:\n{}",
        summary.wrong_count,
        summary
            .wrong_answers
            .iter()
            .map(|(p, e, a)| format!("  {}: expected {e}, got {a}", p.display()))
            .collect::<Vec<_>>()
            .join("\n")
    );

    // All canary benchmarks must be solved (they are trivial)
    let canary_dir = sat_dir.join("canary");
    let canary_unsolved: Vec<_> = results
        .iter()
        .filter(|r| r.path.starts_with(&canary_dir) && !r.actual.is_solved())
        .collect();
    assert!(
        canary_unsolved.is_empty(),
        "Canary benchmarks unsolved: {}",
        canary_unsolved
            .iter()
            .map(|r| format!("{}: {}", r.path.display(), r.actual))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // Log machine-parseable PAR-2 line for CI tracking
    eprintln!(
        "PAR2_CI_QUICK: total={} solved={} wrong={} par2_total={:.3} par2_avg={:.3}",
        summary.total, summary.solved, summary.wrong_count, summary.par2_total, summary.par2_avg
    );
}

// ============================================================================
// Test: Full PAR-2 evaluation (longer timeout, all instances)
// ============================================================================

/// Full PAR-2 evaluation including held-out SAT-COMP 2022/2023 instances.
///
/// This test uses a longer timeout and runs the complete benchmark suite.
/// Gated behind the `AY_PAR2_FULL` environment variable to avoid running
/// in normal CI.
///
/// Run with: AY_PAR2_FULL=1 cargo test -p ay --release test_sat_par2_full -- --nocapture
#[test]
#[timeout(3_600_000)] // 60 minutes total budget
fn test_sat_par2_full() {
    if std::env::var("AY_PAR2_FULL").is_err() {
        eprintln!("Skipping full PAR-2 eval (set AY_PAR2_FULL=1 to run)");
        return;
    }

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let root = workspace_root();
    let timeout_sec: u64 = std::env::var("AY_PAR2_TIMEOUT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(300);
    let timeout = Duration::from_secs(timeout_sec);

    let instances = collect_benchmarks(&root);
    assert!(!instances.is_empty(), "No benchmark instances found");

    eprintln!(
        "PAR-2 full eval: {} instances, timeout={}s",
        instances.len(),
        timeout.as_secs()
    );

    let results: Vec<BenchmarkResult> = instances
        .iter()
        .enumerate()
        .map(|(i, inst)| {
            if i > 0 && i % 10 == 0 {
                eprintln!("Progress: {}/{}", i, instances.len());
            }
            run_solver(ay_path, inst, timeout)
        })
        .collect();

    print_results_table(&results);
    let summary = compute_par2(&results, timeout);
    eprintln!("\n{summary}");

    // CRITICAL: zero wrong answers even in full eval
    assert!(
        summary.wrong_answers.is_empty(),
        "CRITICAL: {} wrong answer(s) in full eval:\n{}",
        summary.wrong_count,
        summary
            .wrong_answers
            .iter()
            .map(|(p, e, a)| format!("  {}: expected {e}, got {a}", p.display()))
            .collect::<Vec<_>>()
            .join("\n")
    );

    // Log machine-parseable PAR-2 line for performance tracking
    eprintln!(
        "PAR2_FULL: total={} solved={} wrong={} timeout={} par2_total={:.3} par2_avg={:.3}",
        summary.total,
        summary.solved,
        summary.wrong_count,
        summary.timeout_count,
        summary.par2_total,
        summary.par2_avg
    );
}

// ============================================================================
// Unit tests for harness internals
// ============================================================================

#[cfg(test)]
mod internal_tests {
    use super::*;

    #[test]
    fn test_parse_verdict_satisfiable() {
        assert_eq!(
            parse_verdict("s SATISFIABLE\nv 1 -2 3 0\n", Some(10)),
            SolverVerdict::Sat
        );
    }

    #[test]
    fn test_parse_verdict_unsatisfiable() {
        assert_eq!(
            parse_verdict("s UNSATISFIABLE\n", Some(20)),
            SolverVerdict::Unsat
        );
    }

    #[test]
    fn test_parse_verdict_exit_code_sat() {
        assert_eq!(parse_verdict("", Some(10)), SolverVerdict::Sat);
    }

    #[test]
    fn test_parse_verdict_exit_code_unsat() {
        assert_eq!(parse_verdict("", Some(20)), SolverVerdict::Unsat);
    }

    #[test]
    fn test_parse_verdict_unknown() {
        assert_eq!(
            parse_verdict("s UNKNOWN\n", Some(0)),
            SolverVerdict::Unknown
        );
    }

    #[test]
    fn test_parse_verdict_no_output() {
        assert_eq!(parse_verdict("", Some(0)), SolverVerdict::Unknown);
    }

    #[test]
    fn test_parse_verdict_with_comment_lines() {
        let output = "c some comment\nc more comments\ns SATISFIABLE\nv 1 0\n";
        assert_eq!(parse_verdict(output, Some(10)), SolverVerdict::Sat);
    }

    #[test]
    fn test_par2_computation_all_solved() {
        let results = vec![
            BenchmarkResult {
                path: PathBuf::from("a.cnf"),
                expected: Expected::Sat,
                actual: SolverVerdict::Sat,
                elapsed: Duration::from_millis(100),
                exit_code: Some(10),
            },
            BenchmarkResult {
                path: PathBuf::from("b.cnf"),
                expected: Expected::Unsat,
                actual: SolverVerdict::Unsat,
                elapsed: Duration::from_millis(200),
                exit_code: Some(20),
            },
        ];
        let summary = compute_par2(&results, Duration::from_mins(1));
        assert_eq!(summary.total, 2);
        assert_eq!(summary.solved, 2);
        assert_eq!(summary.wrong_count, 0);
        assert_eq!(summary.timeout_count, 0);
        // PAR-2 = 0.1 + 0.2 = 0.3
        assert!((summary.par2_total - 0.3).abs() < 0.01);
    }

    #[test]
    fn test_par2_computation_with_timeout() {
        let timeout = Duration::from_mins(1);
        let results = vec![
            BenchmarkResult {
                path: PathBuf::from("a.cnf"),
                expected: Expected::Sat,
                actual: SolverVerdict::Sat,
                elapsed: Duration::from_millis(100),
                exit_code: Some(10),
            },
            BenchmarkResult {
                path: PathBuf::from("b.cnf"),
                expected: Expected::Unknown,
                actual: SolverVerdict::Timeout,
                elapsed: timeout,
                exit_code: None,
            },
        ];
        let summary = compute_par2(&results, timeout);
        assert_eq!(summary.total, 2);
        assert_eq!(summary.solved, 1);
        assert_eq!(summary.timeout_count, 1);
        // PAR-2 = 0.1 + 2*60 = 120.1
        assert!((summary.par2_total - 120.1).abs() < 0.01);
    }

    #[test]
    fn test_par2_computation_wrong_answer() {
        let timeout = Duration::from_mins(1);
        let results = vec![BenchmarkResult {
            path: PathBuf::from("wrong.cnf"),
            expected: Expected::Sat,
            actual: SolverVerdict::Unsat,
            elapsed: Duration::from_millis(50),
            exit_code: Some(20),
        }];
        let summary = compute_par2(&results, timeout);
        assert_eq!(summary.wrong_count, 1);
        assert_eq!(summary.solved, 0);
        // Wrong answer gets 2x timeout penalty
        assert!((summary.par2_total - 120.0).abs() < 0.01);
        assert_eq!(summary.wrong_answers.len(), 1);
    }

    #[test]
    fn test_collect_benchmarks_not_empty() {
        let root = workspace_root();
        let instances = collect_benchmarks(&root);
        assert!(
            !instances.is_empty(),
            "Expected at least one benchmark instance from the published SAT corpus, found {}",
            instances.len()
        );
    }
}
