// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BCP profiling test for issue #3099.
//!
//! Measures wall-clock solve time and integer counters (propagations, conflicts,
//! decisions) across uf250 benchmarks. No internal timing instrumentation.
//!
//! Skipped in debug mode: ForwardChecker makes each solve ~100x slower,
//! rendering timing data meaningless and exceeding reasonable timeouts.

#![allow(clippy::print_stderr)]

use ay_sat::parse_dimacs;
use ntest::timeout;
use std::path::PathBuf;
use std::time::{Duration, Instant};

fn collect_cnf_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.ok()?.path();
            (p.extension().is_some_and(|e| e == "cnf")).then_some(p)
        })
        .collect();
    files.sort();
    files
}

#[test]
#[timeout(300_000)]
fn profile_bcp_uf250() {
    if cfg!(debug_assertions) {
        eprintln!("Skipping BCP profile in debug mode (ForwardChecker overhead)");
        return;
    }

    let benchmark_dir = super::common::workspace_root().join("benchmarks/satlib/uf250");
    if !benchmark_dir.exists() {
        eprintln!("Skipping BCP profile: benchmarks/satlib/uf250 not found");
        return;
    }

    let files = collect_cnf_files(&benchmark_dir);
    if files.is_empty() {
        eprintln!("Skipping BCP profile: no .cnf files found");
        return;
    }

    let mut total_solve = Duration::ZERO;
    let mut total_propagations: u64 = 0;
    let mut total_decisions: u64 = 0;
    let mut total_conflicts: u64 = 0;
    let mut solved = 0u32;

    for file in &files {
        let formula = parse_dimacs(&std::fs::read_to_string(file).unwrap()).unwrap();
        let mut solver = formula.into_solver();

        let start = Instant::now();
        let result = solver.solve();
        total_solve += start.elapsed();

        assert!(
            result.is_sat() || result.is_unsat(),
            "uf250 should be SAT or UNSAT, got Unknown for {}",
            file.display()
        );

        total_propagations += solver.num_propagations();
        total_decisions += solver.num_decisions();
        total_conflicts += solver.num_conflicts();
        solved += 1;
    }

    let props_per_sec = total_propagations as f64 / total_solve.as_secs_f64();
    let prop_conflict = total_propagations as f64 / total_conflicts.max(1) as f64;
    eprintln!("\n=== BCP Profile (#3099): uf250 x{solved} ===");
    eprintln!("Total solve time: {total_solve:?}");
    eprintln!("Propagations: {total_propagations} ({props_per_sec:.0}/sec)");
    eprintln!("Conflicts: {total_conflicts}, Decisions: {total_decisions}");
    eprintln!("Prop/conflict ratio: {prop_conflict:.1}");

    assert!(total_solve > Duration::from_millis(1), "solve too fast");
    assert!(total_propagations > 0, "should have propagations");
}
