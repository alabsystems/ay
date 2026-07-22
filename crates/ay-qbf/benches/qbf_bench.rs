// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF solver performance benchmarks
//!
//! Benchmarks QCIR and QDIMACS solving performance.
//! Requires benchmark files in `benchmarks/qbf/`.

use ay_qbf::{parse_qdimacs, QbfSolver};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::fs;
use std::path::PathBuf;

fn benchmarks_dir() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop();
    path.pop();
    path.push("benchmarks/qbf");
    path
}

/// Benchmark all QDIMACS files in the benchmarks directory
fn bench_qbf_all(c: &mut Criterion) {
    let dir = benchmarks_dir();
    if !dir.exists() {
        return;
    }

    let mut group = c.benchmark_group("qbf_solve");

    let benchmarks = [
        "simple_sat.qdimacs",
        "simple_unsat.qdimacs",
        "nested_sat.qdimacs",
        "nested_unsat.qdimacs",
        "dependency_sat.qdimacs",
        "dependency_unsat.qdimacs",
    ];

    for filename in benchmarks {
        let path = dir.join(filename);
        if !path.exists() {
            continue;
        }

        let content = fs::read_to_string(&path).expect("read");
        let formula = parse_qdimacs(&content).expect("parse");

        group.bench_with_input(
            BenchmarkId::new("solve", filename),
            &formula,
            |b, formula| {
                b.iter(|| {
                    let mut solver = QbfSolver::new(black_box(formula.clone()));
                    solver.solve()
                });
            },
        );
    }

    group.finish();
}

/// Benchmark parsing overhead
fn bench_qbf_parse(c: &mut Criterion) {
    let dir = benchmarks_dir();
    if !dir.exists() {
        return;
    }

    let mut group = c.benchmark_group("qbf_parse");

    let path = dir.join("simple_sat.qdimacs");
    if !path.exists() {
        return;
    }

    let content = fs::read_to_string(&path).expect("read");

    group.bench_function("parse_qdimacs", |b| {
        b.iter(|| parse_qdimacs(black_box(&content)).unwrap());
    });

    group.finish();
}

criterion_group!(benches, bench_qbf_all, bench_qbf_parse);

criterion_main!(benches);
