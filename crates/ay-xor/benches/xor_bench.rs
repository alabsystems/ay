// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! XOR-aware SAT solving benchmarks
//!
//! Compares XOR-aware solving vs plain SAT solving on cryptographic benchmarks.
//! Requires benchmark files in `benchmarks/sat/crypto/`.

use ay_sat::{parse_dimacs, Solver};
use ay_xor::solve_with_xor_detection;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::fs;
use std::path::PathBuf;

fn get_benchmark_path(filename: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop();
    path.pop();
    path.push("benchmarks/sat/crypto");
    path.push(filename);
    path
}

/// Benchmark XOR-aware solving on par8 benchmarks
fn bench_xor_par8(c: &mut Criterion) {
    let mut group = c.benchmark_group("xor_par8");

    for filename in ["par8-1.cnf", "par8-2.cnf", "par8-3.cnf"] {
        let path = get_benchmark_path(filename);
        if !path.exists() {
            continue;
        }

        let content = fs::read_to_string(&path).expect("read");
        let formula = parse_dimacs(&content).expect("parse");

        group.bench_with_input(BenchmarkId::new("xor", filename), &formula, |b, formula| {
            b.iter(|| {
                solve_with_xor_detection(black_box(formula.num_vars), black_box(&formula.clauses))
            });
        });

        group.bench_with_input(
            BenchmarkId::new("plain", filename),
            &formula,
            |b, formula| {
                b.iter(|| {
                    let mut solver = Solver::new(black_box(formula.num_vars));
                    for clause in black_box(&formula.clauses) {
                        solver.add_clause(clause.clone());
                    }
                    solver.solve()
                });
            },
        );
    }

    group.finish();
}

/// Benchmark XOR detection overhead (preprocessing time)
fn bench_xor_detection_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("xor_detection");

    for filename in ["par8-1.cnf"] {
        let path = get_benchmark_path(filename);
        if !path.exists() {
            continue;
        }

        let content = fs::read_to_string(&path).expect("read");
        let formula = parse_dimacs(&content).expect("parse");

        group.bench_with_input(
            BenchmarkId::new("preprocess", filename),
            &formula,
            |b, formula| {
                b.iter(|| ay_xor::preprocess_clauses_with_stats(black_box(&formula.clauses)));
            },
        );
    }

    group.finish();
}

/// Performance target: XOR solve on par8-1 should be <10ms
fn bench_phase2_target(c: &mut Criterion) {
    let path = get_benchmark_path("par8-1.cnf");
    if !path.exists() {
        return;
    }

    let content = fs::read_to_string(&path).expect("read");
    let formula = parse_dimacs(&content).expect("parse");

    c.bench_function("phase2_target_par8_1", |b| {
        b.iter(|| {
            solve_with_xor_detection(black_box(formula.num_vars), black_box(&formula.clauses))
        });
    });
}

/// Benchmark propagation complexity to verify O(1) amortized claim.
///
/// Creates XOR systems with 100, 1K, 10K equations and measures per-assignment
/// propagation time. If properly O(1) amortized, time should be roughly constant.
fn bench_propagation_complexity(c: &mut Criterion) {
    use ay_xor::{GaussianSolver, XorConstraint};

    let mut group = c.benchmark_group("xor_propagation_complexity");

    for num_equations in [100_usize, 1_000, 10_000] {
        // Create a system of XOR equations with 3 variables each.
        // x_{3i} XOR x_{3i+1} XOR x_{3i+2} = i%2
        let num_vars = num_equations * 3;
        let constraints: Vec<XorConstraint> = (0..num_equations)
            .map(|i| {
                let vars = vec![(3 * i) as u32, (3 * i + 1) as u32, (3 * i + 2) as u32];
                XorConstraint::new(vars, i % 2 == 1)
            })
            .collect();

        let label = format!("{num_equations}_eqs");

        // Measure time to initialize + eliminate + assign half the variables.
        // The key metric is how per-assignment time scales with system size.
        group.bench_with_input(
            BenchmarkId::new("assign_half", &label),
            &constraints,
            |b, constraints| {
                b.iter(|| {
                    let mut solver = GaussianSolver::new(black_box(constraints));
                    let _ = solver.eliminate();
                    // Assign roughly half the variables
                    for v in (0..num_vars / 2).map(|i| i as u32) {
                        let _ = solver.assign(v, v % 2 == 0);
                    }
                });
            },
        );

        // Measure init + eliminate + single assignment baseline.
        // Compare with assign_half: if O(1) amortized holds, assign_half should
        // only add ~linear overhead above this baseline (not quadratic).
        group.bench_with_input(
            BenchmarkId::new("init_elim_baseline", &label),
            &constraints,
            |b, constraints| {
                b.iter(|| {
                    let mut solver = GaussianSolver::new(black_box(constraints));
                    let _ = solver.eliminate();
                    // Single assignment to include minimal assignment overhead
                    let _ = solver.assign(0, false);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_xor_par8,
    bench_xor_detection_overhead,
    bench_phase2_target,
    bench_propagation_complexity,
);

criterion_main!(benches);
