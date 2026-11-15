// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF Benchmark Tests
//!
//! Run QBFLIB-style benchmarks to verify solver correctness.

use ay_qbf::{parse_qdimacs, QbfResult, QbfSolver};
use std::fs;
use std::path::PathBuf;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::{Duration, Instant};

type TestResult = Result<(), Box<dyn std::error::Error>>;

/// Per-test wall-clock limit (the former `#[timeout(60000)]`).
const BENCHMARK_TIMEOUT: Duration = Duration::from_millis(60_000);

/// Benchmark test case
struct BenchmarkCase {
    name: &'static str,
    expected: ExpectedResult,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpectedResult {
    Sat,
    Unsat,
}

/// Run a single benchmark file and return the result
fn run_benchmark(path: &PathBuf) -> Result<QbfResult, String> {
    let content = fs::read_to_string(path)
        .map_err(|error| format!("Failed to read benchmark file: {error:?}"))?;
    let formula =
        parse_qdimacs(&content).map_err(|error| format!("Failed to parse QDIMACS: {error:?}"))?;
    let mut solver = QbfSolver::new(formula);
    Ok(solver.solve())
}

/// Run the named benchmark and fail unless the solver returns `expected`.
fn expect_benchmark(name: &str, expected: ExpectedResult) -> Result<(), String> {
    let path = benchmarks_dir().join(name);
    let actual = match run_benchmark(&path)? {
        QbfResult::Sat(_) => Some(ExpectedResult::Sat),
        QbfResult::Unsat(_) => Some(ExpectedResult::Unsat),
        QbfResult::Unknown => None,
    };
    if actual != Some(expected) {
        return Err(format!("{name}: expected {expected:?}, got {actual:?}"));
    }
    Ok(())
}

/// Describe a panic payload caught from the test body.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

/// Describe why no outcome arrived from the test body's thread.
fn receive_failure(error: RecvTimeoutError, started: Instant, limit: Duration) -> String {
    if matches!(error, RecvTimeoutError::Timeout) {
        format!(
            "timeout: the function call took {} ms. Max time {} ms",
            started.elapsed().as_millis(),
            limit.as_millis()
        )
    } else {
        "thread disconnected unexpectedly".to_string()
    }
}

/// Run `body` on its own thread and fail if it errors, panics, or takes
/// longer than `limit`. This is the `ntest::timeout` harness with every
/// failure returned as an error instead of re-raised as a panic. Each
/// `Result` is consumed whole (`map_err` + `?`), never destructured.
fn run_with_timeout<F>(limit: Duration, body: F) -> TestResult
where
    F: FnOnce() -> Result<(), String> + Send + 'static,
{
    let started = Instant::now();
    let (sender, receiver) = mpsc::channel();
    std::thread::Builder::new().spawn(move || {
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(body));
        // Send fails only if the receiver already timed out; that is expected.
        let _ = sender.send(outcome);
    })?;
    let outcome = receiver
        .recv_timeout(limit)
        .map_err(|error| receive_failure(error, started, limit))?;
    let body_result =
        outcome.map_err(|payload| format!("panicked: {}", panic_message(payload.as_ref())))?;
    body_result.map_err(Into::into)
}

/// Get the path to benchmarks directory
fn benchmarks_dir() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop(); // crates/
    path.pop(); // root
    path.push("benchmarks");
    path.push("qbf");
    path
}

/// Known benchmark results
fn known_benchmarks() -> Vec<BenchmarkCase> {
    vec![
        BenchmarkCase {
            name: "simple_sat.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "simple_unsat.qdimacs",
            expected: ExpectedResult::Unsat,
        },
        BenchmarkCase {
            name: "forall_tautology.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "exists_forall_sat.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "exists_forall_unsat.qdimacs",
            expected: ExpectedResult::Unsat,
        },
        BenchmarkCase {
            name: "forall_exists_sat.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "three_level_sat.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "universal_reduction_test.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "php_2_1.qdimacs",
            expected: ExpectedResult::Unsat,
        },
        BenchmarkCase {
            name: "php_3_2.qdimacs",
            expected: ExpectedResult::Unsat,
        },
        BenchmarkCase {
            name: "blocked_clause.qdimacs",
            expected: ExpectedResult::Sat, // Tautology
        },
        BenchmarkCase {
            name: "counter_2bit.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "double_forall_unsat.qdimacs",
            expected: ExpectedResult::Unsat,
        },
        BenchmarkCase {
            name: "complex_sat.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "dependency_sat.qdimacs",
            expected: ExpectedResult::Sat,
        },
        BenchmarkCase {
            name: "dependency_unsat.qdimacs",
            expected: ExpectedResult::Unsat,
        },
    ]
}

#[test]
#[allow(clippy::print_stderr)]
fn test_all_benchmarks() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        let dir = benchmarks_dir();
        let mut passed: usize = 0;
        let mut failed: usize = 0;
        let mut errors: Vec<String> = Vec::new();

        for case in known_benchmarks() {
            let path = dir.join(case.name);
            if !path.exists() {
                errors.push(format!("{}: File not found", case.name));
                failed = failed.saturating_add(1);
                continue;
            }

            let result = run_benchmark(&path)?;
            let actual = match result {
                QbfResult::Sat(_) => ExpectedResult::Sat,
                QbfResult::Unsat(_) => ExpectedResult::Unsat,
                QbfResult::Unknown => {
                    errors.push(format!("{}: Solver returned Unknown", case.name));
                    failed = failed.saturating_add(1);
                    continue;
                }
            };

            if actual == case.expected {
                passed = passed.saturating_add(1);
            } else {
                errors.push(format!(
                    "{}: Expected {:?}, got {:?}",
                    case.name, case.expected, actual
                ));
                failed = failed.saturating_add(1);
            }
        }

        eprintln!("\n=== QBF Benchmark Results ===");
        eprintln!("Passed: {passed}");
        eprintln!("Failed: {failed}");

        if !errors.is_empty() {
            eprintln!("\nErrors:");
            for err in &errors {
                eprintln!("  {err}");
            }
            return Err("Some benchmarks failed".to_string());
        }
        Ok(())
    })
}

// Individual benchmark tests for better CI visibility
#[test]
fn bench_simple_sat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("simple_sat.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_simple_unsat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("simple_unsat.qdimacs", ExpectedResult::Unsat)
    })
}

#[test]
fn bench_forall_tautology() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("forall_tautology.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_exists_forall_sat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("exists_forall_sat.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_exists_forall_unsat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("exists_forall_unsat.qdimacs", ExpectedResult::Unsat)
    })
}

#[test]
fn bench_forall_exists_sat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("forall_exists_sat.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_three_level_sat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("three_level_sat.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_universal_reduction() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("universal_reduction_test.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_php_2_1() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("php_2_1.qdimacs", ExpectedResult::Unsat)
    })
}

#[test]
fn bench_php_3_2() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("php_3_2.qdimacs", ExpectedResult::Unsat)
    })
}

#[test]
fn bench_blocked_clause() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("blocked_clause.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_counter_2bit() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("counter_2bit.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_double_forall_unsat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("double_forall_unsat.qdimacs", ExpectedResult::Unsat)
    })
}

#[test]
fn bench_complex_sat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("complex_sat.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_dependency_sat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("dependency_sat.qdimacs", ExpectedResult::Sat)
    })
}

#[test]
fn bench_dependency_unsat() -> TestResult {
    run_with_timeout(BENCHMARK_TIMEOUT, || {
        expect_benchmark("dependency_unsat.qdimacs", ExpectedResult::Unsat)
    })
}
