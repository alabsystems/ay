// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward checker overhead evaluation for issue #5422.
//!
//! Measures the wall-clock time overhead of enabling the online forward DRUP
//! checker in release builds. The forward checker RUP-verifies every derived
//! clause at derivation time, catching proof bugs immediately.
//!
//! This test is release-only: debug builds have the forward checker auto-enabled
//! and include other debug instrumentation that distorts timing.

#![allow(clippy::print_stderr)]

use ay_sat::{parse_dimacs, Solver};
use ntest::timeout;
use std::time::{Duration, Instant};

/// Simple LCG for deterministic pseudo-randomness.
fn generate_random_3sat(num_vars: u32, num_clauses: usize, seed: u64) -> String {
    let mut cnf = format!("p cnf {num_vars} {num_clauses}\n");
    let mut state = seed;
    let lcg_next = |s: &mut u64| {
        *s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
        *s
    };
    for _ in 0..num_clauses {
        for _ in 0..3 {
            let var = ((lcg_next(&mut state) % u64::from(num_vars)) + 1) as i32;
            let sign = if lcg_next(&mut state) % 2 == 0 { 1 } else { -1 };
            cnf.push_str(&format!("{} ", var * sign));
        }
        cnf.push_str("0\n");
    }
    cnf
}

/// Pigeonhole principle formula: n+1 pigeons, n holes. Always UNSAT.
fn generate_pigeonhole(n: u32) -> String {
    let num_pigeons = n + 1;
    let num_holes = n;
    let num_vars = num_pigeons * num_holes;
    let var = |pigeon: u32, hole: u32| -> i32 { (pigeon * num_holes + hole + 1) as i32 };

    let mut clauses: Vec<String> = Vec::new();
    for i in 0..num_pigeons {
        let mut clause = String::new();
        for j in 0..num_holes {
            clause.push_str(&format!("{} ", var(i, j)));
        }
        clause.push('0');
        clauses.push(clause);
    }
    for j in 0..num_holes {
        for i1 in 0..num_pigeons {
            for i2 in (i1 + 1)..num_pigeons {
                clauses.push(format!("-{} -{} 0", var(i1, j), var(i2, j)));
            }
        }
    }
    format!(
        "p cnf {} {}\n{}",
        num_vars,
        clauses.len(),
        clauses.join("\n")
    )
}

struct BenchResult {
    label: String,
    baseline_ms: f64,
    checked_ms: f64,
    overhead_ratio: f64,
    result_match: bool,
}

/// Build a solver from DIMACS with optional forward checker.
///
/// `enable_forward_checker()` must be called BEFORE adding clauses (API contract),
/// so we construct the solver manually rather than using `into_solver()`.
///
/// Inprocessing is disabled for both configurations to ensure a fair comparison.
/// Inprocessing techniques (sweep, congruence) introduce auxiliary variables that
/// the forward checker cannot track in release builds, causing RUP failures.
fn build_solver(dimacs: &str, with_checker: bool) -> Solver {
    let formula = parse_dimacs(dimacs).expect("valid DIMACS");
    let mut solver = Solver::new(formula.num_vars);
    if with_checker {
        // Enable checker BEFORE adding clauses (API contract).
        solver.enable_forward_checker();
    }
    // Disable all inprocessing for fair comparison: inprocessing techniques
    // (sweep, congruence) introduce auxiliary variables that the forward
    // checker cannot track. Both baseline and checked runs use pure CDCL
    // so the overhead measurement is apples-to-apples.
    super::common::disable_all_inprocessing(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    solver
}

/// Solve a formula with and without forward checker, returning timing results.
fn measure_overhead(label: &str, dimacs: &str, iterations: u32) -> BenchResult {
    // Baseline: no forward checker
    let mut baseline_total = Duration::ZERO;
    let mut baseline_result = None;
    for _ in 0..iterations {
        let mut solver = build_solver(dimacs, false);
        let start = Instant::now();
        let result = solver.solve().into_inner();
        baseline_total += start.elapsed();
        baseline_result = Some(result.is_unsat());
    }

    // With forward checker enabled (before clause addition)
    let mut checked_total = Duration::ZERO;
    let mut checked_result = None;
    for _ in 0..iterations {
        let mut solver = build_solver(dimacs, true);
        let start = Instant::now();
        let result = solver.solve().into_inner();
        checked_total += start.elapsed();
        checked_result = Some(result.is_unsat());
    }

    let baseline_ms = baseline_total.as_secs_f64() * 1000.0 / f64::from(iterations);
    let checked_ms = checked_total.as_secs_f64() * 1000.0 / f64::from(iterations);
    let overhead_ratio = if baseline_ms > 0.001 {
        checked_ms / baseline_ms
    } else {
        1.0
    };

    BenchResult {
        label: label.to_string(),
        baseline_ms,
        checked_ms,
        overhead_ratio,
        result_match: baseline_result == checked_result,
    }
}

/// Collect all benchmark formulas for the overhead evaluation.
fn collect_benchmarks() -> Vec<(&'static str, String, u32)> {
    let mut benchmarks: Vec<(&str, String, u32)> = Vec::new();

    // Random 3-SAT at phase transition (ratio ~4.267)
    for &(vars, ratio_x100, iters) in &[
        (100u32, 427u32, 20u32), // small: ~100 vars, fast
        (200, 427, 10),          // medium: ~200 vars
        (250, 427, 5),           // medium-large: uf250 size
    ] {
        let num_clauses = (u64::from(vars) * u64::from(ratio_x100) / 100) as usize;
        let dimacs = generate_random_3sat(vars, num_clauses, 42);
        // Leak label string to get 'static lifetime (test-only, fine)
        let label: &'static str =
            Box::leak(format!("random-3sat ({vars}v, {num_clauses}c)").into_boxed_str());
        benchmarks.push((label, dimacs, iters));
    }

    // Pigeonhole (UNSAT, exercises conflict analysis heavily)
    for &n in &[5u32, 7, 9] {
        let dimacs = generate_pigeonhole(n);
        let iters = if n <= 7 { 5 } else { 1 };
        let label: &'static str = Box::leak(format!("pigeonhole ({n}h, UNSAT)").into_boxed_str());
        benchmarks.push((label, dimacs, iters));
    }

    // Barrel6 benchmark (vendored test fixture)
    benchmarks.push((
        "barrel6 (2810v, UNSAT)",
        super::common::load_barrel6_cnf(),
        1,
    ));

    benchmarks
}

/// Print results table and summary statistics.
fn print_results(results: &[BenchResult]) {
    eprintln!(
        "{:<35} {:>10} {:>10} {:>10} {:>6}",
        "Benchmark", "Base (ms)", "Check (ms)", "Overhead", "Match"
    );
    eprintln!("{}", "-".repeat(75));

    for r in results {
        eprintln!(
            "{:<35} {:>10.2} {:>10.2} {:>9.2}x {:>6}",
            r.label,
            r.baseline_ms,
            r.checked_ms,
            r.overhead_ratio,
            if r.result_match { "OK" } else { "MISMATCH" }
        );
    }

    let ratios: Vec<f64> = results
        .iter()
        .filter(|r| r.baseline_ms > 1.0) // skip sub-millisecond noise
        .map(|r| r.overhead_ratio)
        .collect();

    if !ratios.is_empty() {
        let avg = ratios.iter().sum::<f64>() / ratios.len() as f64;
        let max = ratios.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        let min = ratios.iter().copied().fold(f64::INFINITY, f64::min);
        eprintln!("\n--- Summary (benchmarks > 1ms baseline) ---");
        eprintln!("Overhead range: {min:.2}x - {max:.2}x");
        eprintln!("Average overhead: {avg:.2}x");
        eprintln!("Benchmarks measured: {}", ratios.len());
    }
}

#[test]
#[timeout(300_000)]
fn evaluate_forward_checker_release_overhead() {
    if cfg!(debug_assertions) {
        eprintln!(
            "Skipping forward checker overhead evaluation in debug mode.\n\
             Run with: cargo test --release -p ay-sat --test forward_checker_overhead"
        );
        return;
    }

    eprintln!("\n=== Forward Checker Overhead Evaluation (#5422) ===\n");

    let benchmarks = collect_benchmarks();
    let results: Vec<BenchResult> = benchmarks
        .iter()
        .map(|(label, dimacs, iters)| measure_overhead(label, dimacs, *iters))
        .collect();

    print_results(&results);

    // All results must match (forward checker must not change solve outcome)
    for r in &results {
        assert!(
            r.result_match,
            "Forward checker changed solve result for {}",
            r.label
        );
    }

    eprintln!("\n=== End Forward Checker Overhead Evaluation ===");
}
