// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Startup timing benchmark for Kani Fast Priority 2.2.
//!
//! Unlike `tests/startup_timing.rs`, the "full" benchmark intentionally
//! includes parsing so benchmark runs can separate parser cost from
//! executor startup and solving cost.

use ay_dpll::Executor;
use ay_frontend::{parse, Command};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

fn run_commands(commands: &[Command]) {
    let mut executor = Executor::new();
    let mut saw_sat = false;

    for cmd in commands {
        if let Some(output) = executor
            .execute(cmd)
            .expect("startup benchmark commands must execute successfully")
        {
            saw_sat = true;
            black_box(output);
        }
    }

    assert!(saw_sat, "startup benchmark workload must reach check-sat");
}

/// Full startup: parse → executor → execute → check_sat
fn bench_startup_full(c: &mut Criterion) {
    let bv_smt =
        "(set-logic QF_BV)(declare-const x (_ BitVec 32))(assert (bvugt x #x00000000))(check-sat)";
    let propositional_smt =
        "(set-logic QF_BOOL)(declare-const p1 Bool)(declare-const p2 Bool)(assert (or p1 p2))(check-sat)";

    let mut group = c.benchmark_group("startup_full");

    group.bench_function("bv_32bit", |b| {
        b.iter(|| {
            let commands = parse(black_box(bv_smt)).unwrap();
            run_commands(&commands);
        });
    });

    group.bench_function("propositional", |b| {
        b.iter(|| {
            let commands = parse(black_box(propositional_smt)).unwrap();
            run_commands(&commands);
        });
    });

    group.finish();
}

/// Benchmark individual startup phases for breakdown analysis
fn bench_startup_phases(c: &mut Criterion) {
    let smt =
        "(set-logic QF_BV)(declare-const x (_ BitVec 32))(assert (bvugt x #x00000000))(check-sat)";

    let mut group = c.benchmark_group("startup_phases");

    // Phase 1: Parse only
    group.bench_function("parse", |b| b.iter(|| parse(black_box(smt)).unwrap()));

    // Phase 2: Executor construction only
    group.bench_function("executor_new", |b| b.iter(Executor::new));

    // Phase 3: Executor creation + command execution, with parsing excluded.
    let commands = parse(smt).unwrap();
    group.bench_function("executor_and_execute", |b| {
        b.iter(|| run_commands(black_box(&commands)))
    });

    group.finish();
}

/// Multiple instance startup (Kani Fast creates many solver instances)
fn bench_multi_instance_startup(c: &mut Criterion) {
    let smt =
        "(set-logic QF_BV)(declare-const x (_ BitVec 32))(assert (bvugt x #x00000000))(check-sat)";

    let mut group = c.benchmark_group("multi_instance");

    for num_instances in [5, 10, 20] {
        group.bench_with_input(
            BenchmarkId::new("instances", num_instances),
            &num_instances,
            |b, &n| {
                b.iter(|| {
                    for _ in 0..n {
                        let commands = parse(black_box(smt)).unwrap();
                        run_commands(&commands);
                    }
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_startup_full,
    bench_startup_phases,
    bench_multi_instance_startup,
);

criterion_main!(benches);
