// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF Benchmark Tests
//!
//! Run QBFLIB-style benchmarks to verify solver correctness.

use ay_qbf::{parse_qdimacs, QbfResult, QbfSolver};
use ntest::timeout;
use std::fs;
use std::path::PathBuf;

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
fn run_benchmark(path: &PathBuf) -> QbfResult {
    let content = fs::read_to_string(path).expect("Failed to read benchmark file");
    let formula = parse_qdimacs(&content).expect("Failed to parse QDIMACS");
    let mut solver = QbfSolver::new(formula);
    solver.solve()
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
#[timeout(60000)]
#[allow(clippy::print_stderr)]
fn test_all_benchmarks() {
    let dir = benchmarks_dir();
    let mut passed = 0;
    let mut failed = 0;
    let mut errors: Vec<String> = Vec::new();

    for case in known_benchmarks() {
        let path = dir.join(case.name);
        if !path.exists() {
            errors.push(format!("{}: File not found", case.name));
            failed += 1;
            continue;
        }

        let result = run_benchmark(&path);
        let actual = match result {
            QbfResult::Sat(_) => ExpectedResult::Sat,
            QbfResult::Unsat(_) => ExpectedResult::Unsat,
            QbfResult::Unknown => {
                errors.push(format!("{}: Solver returned Unknown", case.name));
                failed += 1;
                continue;
            }
        };

        if actual == case.expected {
            passed += 1;
        } else {
            errors.push(format!(
                "{}: Expected {:?}, got {:?}",
                case.name, case.expected, actual
            ));
            failed += 1;
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
    }

    assert!(errors.is_empty(), "Some benchmarks failed");
}

// Individual benchmark tests for better CI visibility
#[test]
#[timeout(60000)]
fn bench_simple_sat() {
    let path = benchmarks_dir().join("simple_sat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_simple_unsat() {
    let path = benchmarks_dir().join("simple_unsat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
#[timeout(60000)]
fn bench_forall_tautology() {
    let path = benchmarks_dir().join("forall_tautology.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_exists_forall_sat() {
    let path = benchmarks_dir().join("exists_forall_sat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_exists_forall_unsat() {
    let path = benchmarks_dir().join("exists_forall_unsat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
#[timeout(60000)]
fn bench_forall_exists_sat() {
    let path = benchmarks_dir().join("forall_exists_sat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_three_level_sat() {
    let path = benchmarks_dir().join("three_level_sat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_universal_reduction() {
    let path = benchmarks_dir().join("universal_reduction_test.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_php_2_1() {
    let path = benchmarks_dir().join("php_2_1.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
#[timeout(60000)]
fn bench_php_3_2() {
    let path = benchmarks_dir().join("php_3_2.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
#[timeout(60000)]
fn bench_blocked_clause() {
    let path = benchmarks_dir().join("blocked_clause.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_counter_2bit() {
    let path = benchmarks_dir().join("counter_2bit.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_double_forall_unsat() {
    let path = benchmarks_dir().join("double_forall_unsat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
#[timeout(60000)]
fn bench_complex_sat() {
    let path = benchmarks_dir().join("complex_sat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_dependency_sat() {
    let path = benchmarks_dir().join("dependency_sat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
#[timeout(60000)]
fn bench_dependency_unsat() {
    let path = benchmarks_dir().join("dependency_unsat.qdimacs");
    let result = run_benchmark(&path);
    assert!(matches!(result, QbfResult::Unsat(_)));
}
