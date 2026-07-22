// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::unnecessary_debug_formatting,
    clippy::format_push_string
)]

//! Criterion benchmarks for ay-sat
//!
//! Measures performance of the CDCL SAT solver on various problem classes.

use ay_sat::{parse_dimacs, Literal, Solver, Variable};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

/// Benchmark solving uf20 (20 variable, 91 clause) satisfiable formulas
///
/// REQUIRES: benchmarks/dimacs directory with .cnf files
fn bench_uf20(c: &mut Criterion) {
    // Find benchmark directory relative to workspace root.
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("CARGO_MANIFEST_DIR should be .../crates/ay-sat");
    let benchmark_dir = workspace_root.join("benchmarks").join("dimacs");

    if !benchmark_dir.exists() {
        eprintln!("[INFO] UF20 benchmarks unavailable: {benchmark_dir:?} not found (#528)");
        eprintln!("[INFO] Run: ./scripts/download_benchmarks.sh");
        return;
    }

    // Load first few uf20 files
    let mut formulas: Vec<(String, String)> = Vec::new();
    let mut cnf_paths: Vec<std::path::PathBuf> = std::fs::read_dir(&benchmark_dir)
        .unwrap()
        .map(|entry| entry.expect("read uf20 benchmark dir entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "cnf"))
        .collect();
    cnf_paths.sort();

    for path in cnf_paths.into_iter().take(10) {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let content = std::fs::read_to_string(&path).unwrap();
        formulas.push((name, content));
    }

    if formulas.is_empty() {
        eprintln!("[INFO] UF20 benchmarks directory has no .cnf files: {benchmark_dir:?} (#528)");
        return;
    }

    let mut group = c.benchmark_group("uf20");
    group.throughput(Throughput::Elements(1));

    for (name, cnf) in &formulas {
        group.bench_with_input(BenchmarkId::new("solve", name), cnf, |b, cnf| {
            b.iter(|| {
                let formula = parse_dimacs(black_box(cnf)).unwrap();
                let mut solver = formula.into_solver();
                solver.solve().into_inner()
            });
        });
    }

    group.finish();
}

/// Benchmark random 3-SAT at different clause/variable ratios
fn bench_random_3sat(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_3sat");

    // Test different sizes
    let configs = [
        (20, 85),   // 20 vars, ~4.25 clause/var ratio (near phase transition)
        (50, 215),  // 50 vars
        (100, 430), // 100 vars
    ];

    for (num_vars, num_clauses) in configs {
        let formula = generate_random_3sat(num_vars, num_clauses, 42);
        let label = format!("{num_vars}v_{num_clauses}c");

        group.throughput(Throughput::Elements(num_clauses as u64));
        group.bench_with_input(BenchmarkId::new("solve", &label), &formula, |b, cnf| {
            b.iter(|| {
                let formula = parse_dimacs(black_box(cnf)).unwrap();
                let mut solver = formula.into_solver();
                solver.solve().into_inner()
            });
        });
    }

    group.finish();
}

/// Benchmark pigeonhole problems (known hard UNSAT)
fn bench_pigeonhole(c: &mut Criterion) {
    let mut group = c.benchmark_group("pigeonhole");

    // Pigeonhole principle: n+1 pigeons into n holes
    // Generates n*(n+1) "at least one hole" clauses + n*C(n+1,2) "no two pigeons" clauses
    for n in [3, 4, 5] {
        let formula = generate_pigeonhole(n);
        let label = format!("php_{n}");

        group.bench_with_input(BenchmarkId::new("solve", &label), &formula, |b, cnf| {
            b.iter(|| {
                let formula = parse_dimacs(black_box(cnf)).unwrap();
                let mut solver = formula.into_solver();
                solver.solve().into_inner()
            });
        });
    }

    group.finish();
}

/// Benchmark unit propagation performance
fn bench_propagation(c: &mut Criterion) {
    let mut group = c.benchmark_group("propagation");

    // Chain of implications: x0 -> x1 -> x2 -> ... -> xn
    for n in [100, 500, 1000] {
        let formula = generate_implication_chain(n);
        let label = format!("chain_{n}");

        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("solve", &label), &formula, |b, cnf| {
            b.iter(|| {
                let formula = parse_dimacs(black_box(cnf)).unwrap();
                let mut solver = formula.into_solver();
                solver.solve().into_inner()
            });
        });
    }

    group.finish();
}

/// Benchmark clause addition (without solving)
fn bench_clause_addition(c: &mut Criterion) {
    let mut group = c.benchmark_group("clause_addition");

    for num_clauses in [1000, 10000, 100000] {
        let label = format!("{num_clauses}_clauses");

        group.throughput(Throughput::Elements(num_clauses as u64));
        group.bench_function(BenchmarkId::new("add_clauses", &label), |b| {
            b.iter(|| {
                let mut solver = Solver::new(1000);
                for i in 0..num_clauses {
                    let v1 = Variable::new((i % 1000) as u32);
                    let v2 = Variable::new(((i + 1) % 1000) as u32);
                    let v3 = Variable::new(((i + 2) % 1000) as u32);
                    solver.add_clause(vec![
                        Literal::positive(v1),
                        Literal::negative(v2),
                        Literal::positive(v3),
                    ]);
                }
                black_box(solver)
            });
        });
    }

    group.finish();
}

/// Benchmark conflict analysis throughput using hard UNSAT formulas (#1759)
///
/// Uses pigeonhole problems which generate many conflicts during solving.
/// The benchmark measures end-to-end solve time with throughput reported as
/// conflicts/second. This provides visibility into conflict analysis performance
/// but includes parsing/setup overhead (typically <5% of solve time).
///
/// Note: Conflict count varies by solver heuristics, not formula structure.
fn bench_conflict_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("conflict_analysis");

    // Pigeonhole problems are hard UNSAT instances that generate many conflicts.
    // Conflict count measured empirically - varies by solver heuristics.
    for n in [3, 4, 5, 6] {
        let formula = generate_pigeonhole(n);
        let label = format!("php_{n}");

        // First, measure total conflicts for this problem
        let parsed = parse_dimacs(&formula).unwrap();
        let mut solver = parsed.into_solver();
        let _ = solver.solve().into_inner();
        let total_conflicts = solver.num_conflicts();

        group.throughput(Throughput::Elements(total_conflicts));
        group.bench_with_input(
            BenchmarkId::new("throughput", &label),
            &formula,
            |b, cnf| {
                b.iter(|| {
                    let formula = parse_dimacs(black_box(cnf)).unwrap();
                    let mut solver = formula.into_solver();
                    solver.solve().into_inner()
                });
            },
        );
    }

    // Also test random 3-SAT at phase transition (generates many conflicts)
    // These have more variable conflict clause sizes
    for num_vars in [30, 50, 75] {
        // Phase transition at ~4.26 clauses/var
        let num_clauses = (f64::from(num_vars) * 4.26) as usize;
        let formula = generate_random_3sat(num_vars, num_clauses, 12345);
        let label = format!("rand_{num_vars}v");

        // Measure conflicts
        let parsed = parse_dimacs(&formula).unwrap();
        let mut solver = parsed.into_solver();
        let _ = solver.solve().into_inner();
        let total_conflicts = solver.num_conflicts();

        if total_conflicts > 0 {
            group.throughput(Throughput::Elements(total_conflicts));
            group.bench_with_input(
                BenchmarkId::new("throughput", &label),
                &formula,
                |b, cnf| {
                    b.iter(|| {
                        let formula = parse_dimacs(black_box(cnf)).unwrap();
                        let mut solver = formula.into_solver();
                        solver.solve().into_inner()
                    });
                },
            );
        }
    }

    group.finish();
}

// ============================================================================
// Helper functions for generating test formulas
// ============================================================================

/// Generate a random 3-SAT formula in DIMACS format
fn generate_random_3sat(num_vars: u32, num_clauses: usize, seed: u64) -> String {
    let mut cnf = format!("p cnf {num_vars} {num_clauses}\n");

    // Simple LCG for deterministic pseudo-randomness
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

/// Generate pigeonhole formula: n+1 pigeons, n holes
/// UNSAT because at least one hole must have 2 pigeons
fn generate_pigeonhole(n: u32) -> String {
    let num_pigeons = n + 1;
    let num_holes = n;
    let num_vars = num_pigeons * num_holes;

    // Variable p(i,j) = pigeon i is in hole j
    // Variables numbered 1..num_vars
    let var = |pigeon: u32, hole: u32| -> i32 { (pigeon * num_holes + hole + 1) as i32 };

    let mut clauses: Vec<String> = Vec::new();

    // Each pigeon must be in some hole
    for i in 0..num_pigeons {
        let mut clause = String::new();
        for j in 0..num_holes {
            clause.push_str(&format!("{} ", var(i, j)));
        }
        clause.push('0');
        clauses.push(clause);
    }

    // No two pigeons in the same hole
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

/// Generate implication chain: x0 -> x1 -> x2 -> ... -> xn
/// With x0 = true, forces all variables to be true (SAT)
fn generate_implication_chain(n: usize) -> String {
    let mut clauses: Vec<String> = Vec::new();

    // x0 is true (unit clause)
    clauses.push("1 0".to_string());

    // xi -> xi+1 (i.e., -xi OR xi+1)
    for i in 0..n {
        clauses.push(format!("-{} {} 0", i + 1, i + 2));
    }

    format!("p cnf {} {}\n{}", n + 1, clauses.len(), clauses.join("\n"))
}

criterion_group!(
    benches,
    bench_uf20,
    bench_random_3sat,
    bench_pigeonhole,
    bench_propagation,
    bench_clause_addition,
    bench_conflict_analysis,
);

criterion_main!(benches);
