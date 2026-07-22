// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Criterion benchmarks for `ay-euf`.
//!
//! Measures congruence-closure rebuild performance as the number of terms grows.
//! Includes both:
//! - Legacy rebuild (`rebuild_closure`, `AY_LEGACY_EUF=1`)
//! - Incremental worklist (`incremental_rebuild`, default)

use ay_core::term::{Symbol, TermId, TermStore};
use ay_core::Sort;
use ay_core::TheorySolver;
use ay_euf::EufSolver;
use ay_test_support::env::{lock_env, ScopedEnvVar};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

struct EufBenchProblem {
    terms: TermStore,
    eq_terms: Vec<TermId>,
}

fn build_chain_problem(num_vars: usize) -> EufBenchProblem {
    let mut terms = TermStore::new();
    let sort_u = Sort::Uninterpreted("U".to_string());
    let f = Symbol::named("f");

    let mut vars: Vec<TermId> = Vec::with_capacity(num_vars);
    for i in 0..num_vars {
        vars.push(terms.mk_var(format!("x{i}"), sort_u.clone()));
    }

    // Create UF applications to exercise congruence closure.
    for &v in &vars {
        let _ = terms.mk_app(f.clone(), vec![v], sort_u.clone());
    }

    // Create a chain of equalities x0=x1, x1=x2, ... to force many merges.
    let mut eq_terms: Vec<TermId> = Vec::with_capacity(num_vars.saturating_sub(1));
    for i in 0..num_vars.saturating_sub(1) {
        eq_terms.push(terms.mk_eq(vars[i], vars[i + 1]));
    }

    EufBenchProblem { terms, eq_terms }
}

fn run_check(problem: &EufBenchProblem) {
    let mut solver = EufSolver::new(&problem.terms);
    for &eq in &problem.eq_terms {
        solver.assert_literal(black_box(eq), true);
    }
    black_box(solver.check());
}

fn bench_congruence_closure(c: &mut Criterion) {
    let mut group = c.benchmark_group("euf_congruence_closure");
    // Serialized + restore-on-exit via the one workspace env choke point.
    let _env_lock = lock_env();

    for num_vars in [100_usize, 1_000, 10_000, 100_000] {
        let problem = build_chain_problem(num_vars);
        let label = format!("{num_vars}_vars");

        // Legacy rebuild path (AY_LEGACY_EUF=1).
        {
            let _legacy = ScopedEnvVar::set("AY_LEGACY_EUF", "1");
            group.bench_with_input(
                BenchmarkId::new("legacy_check", &label),
                &problem,
                |b, p| b.iter(|| run_check(black_box(p))),
            );
        }

        // Incremental rebuild path (default).
        {
            let _incremental = ScopedEnvVar::unset("AY_LEGACY_EUF");
            group.bench_with_input(
                BenchmarkId::new("incremental_check", &label),
                &problem,
                |b, p| b.iter(|| run_check(black_box(p))),
            );
        }
    }

    group.finish();
}

criterion_group!(benches, bench_congruence_closure);
criterion_main!(benches);
