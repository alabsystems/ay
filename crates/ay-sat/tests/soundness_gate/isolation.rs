// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Single-feature isolation gates.
//!
//! Each inprocessing feature is tested with all other features disabled
//! to verify it doesn't introduce unsoundness on its own.

use std::time::Instant;

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;

use super::common::{
    assert_model_satisfies, load_benchmark, load_repo_benchmark, solver_all_disabled,
    try_load_benchmark, verify_full_stack_unsat_with_native_drat, verify_unsat,
    verify_unsat_with_native_drat, GateFeature, GATE_BENCHMARKS,
};
use super::test_common;

// ============================================================================
// Baseline: no inprocessing (proves the gate infrastructure works)
// ============================================================================

const BASELINE_BENCHMARKS: &[(&str, &str)] = &[
    ("php_4_3", "benchmarks/sat/unsat/php_4_3.cnf"),
    (
        "tseitin_grid_3x3",
        "benchmarks/sat/unsat/tseitin_grid_3x3.cnf",
    ),
];

#[test]
#[timeout(120_000)]
fn gate_baseline_no_inprocessing_php_4_3() {
    run_baseline_case(BASELINE_BENCHMARKS[0].0, BASELINE_BENCHMARKS[0].1);
}

#[test]
#[timeout(120_000)]
fn gate_baseline_no_inprocessing_tseitin_grid_3x3() {
    run_baseline_case(BASELINE_BENCHMARKS[1].0, BASELINE_BENCHMARKS[1].1);
}

fn run_baseline_case(label: &str, path: &str) {
    let content = load_repo_benchmark(path);
    let (mut solver, clauses) = solver_all_disabled(&content);
    verify_unsat(&mut solver, &clauses, &format!("baseline/{label}"));
}

fn is_fail_closed_known_unsat_benchmark(path: &std::path::Path) -> bool {
    if path
        .file_name()
        .is_some_and(|name| name == "tseitin_cycle_10.cnf")
    {
        return false;
    }
    let contents = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
    !contents
        .lines()
        .take_while(|line| !line.starts_with("p cnf"))
        .any(|line| line.contains("expected UNSAT"))
}

#[test]
#[timeout(120_000)]
fn gate_repo_unsat_corpus_full_stack_sweep() {
    let corpus_dir = test_common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_paths: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", corpus_dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .filter(|path| is_fail_closed_known_unsat_benchmark(path))
        .collect();
    cnf_paths.sort();
    assert!(
        !cnf_paths.is_empty(),
        "expected at least one UNSAT benchmark in {}",
        corpus_dir.display()
    );

    for path in cnf_paths {
        let label = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("<unknown>");
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let formula = parse_dimacs(&dimacs)
            .unwrap_or_else(|e| panic!("parse {} failed: {e}", path.display()));
        let original_clauses = formula.clauses.clone();
        let mut solver = formula.into_solver();
        verify_unsat(
            &mut solver,
            &original_clauses,
            &format!("all-enabled-unsat-corpus/{label}"),
        );
    }
}

fn run_shrink_isolation_case(name: &str) {
    let Some(content) = try_load_benchmark(name) else {
        return;
    };
    let (mut solver, clauses) = solver_all_disabled(&content);
    solver.set_shrink_enabled(true);

    let start = Instant::now();
    let result = solver.solve().into_inner();
    let elapsed = start.elapsed();

    eprintln!(
        "SOUNDNESS GATE [shrink/{name}]: elapsed_ms={} conflicts={} propagations={} shrink_attempts={} shrink_successes={}",
        elapsed.as_millis(),
        solver.num_conflicts(),
        solver.num_propagations(),
        solver.shrink_block_attempts(),
        solver.shrink_block_successes(),
    );

    match result {
        SatResult::Unsat(_) => {}
        SatResult::Sat(model) => {
            assert_model_satisfies(&clauses, &model, &format!("shrink/{name}"));
            panic!(
                "SOUNDNESS GATE [shrink/{name}]: returned SAT with valid model on known-UNSAT instance"
            );
        }
        SatResult::Unknown => {
            panic!("SOUNDNESS GATE [shrink/{name}]: returned Unknown on known-UNSAT instance");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Dedicated regression target for #3917.
///
/// The all-features isolation gate also covers shrink, but this focused test
/// keeps the historical timeout target directly runnable and emits
/// shrink-specific telemetry for diagnosis.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_shrink_isolation_barrel6() {
    run_shrink_isolation_case("cmu-bmc-barrel6.cnf");
}

/// Dedicated regression target for #3917 on the larger structured benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn gate_shrink_isolation_longmult15() {
    run_shrink_isolation_case("cmu-bmc-longmult15.cnf");
}

// ============================================================================
// Per-feature isolation gates (loop over GateFeature::ALL)
// ============================================================================

// 13 features × 2 benchmarks = 26 solve calls; individual solves can take
// 5-10s in release mode, so 120s is too tight. Use 600s (10 min).
#[test]
#[timeout(600_000)]
fn gate_all_features_isolation() {
    for feature in GateFeature::ALL {
        for name in GATE_BENCHMARKS {
            let Some(content) = try_load_benchmark(name) else {
                continue;
            };
            let (mut solver, clauses) = solver_all_disabled(&content);
            feature.enable(&mut solver);
            verify_unsat(
                &mut solver,
                &clauses,
                &format!("{}/{name}", feature.label()),
            );
        }
    }
}

// ============================================================================
// Per-feature native DRAT proof verification (#7913)
// Verifies each feature in isolation produces valid DRAT proofs using the
// in-process ay-drat-check. Uses barrel6 (248 vars) for proof-mode solves.
// Decompose and sweep are excluded by the proof-mode capability policy.
// ============================================================================

#[test]
#[timeout(600_000)]
fn gate_all_features_isolation_native_drat_barrel6() {
    let content = load_benchmark("cmu-bmc-barrel6.cnf");
    for feature in GateFeature::ALL {
        if !feature.drat_verified() {
            continue;
        }
        verify_unsat_with_native_drat(
            feature,
            &content,
            &format!("native-drat-isolation/{}/barrel6", feature.label()),
        );
    }
}

// ============================================================================
// Full-stack DRAT proof verification on the UNSAT corpus (#7913 Phase A)
//
// Every UNSAT benchmark in benchmarks/sat/unsat/ is solved with proof output
// enabled and the proof is verified by ay-drat-check. This closes the gap
// where gate_repo_unsat_corpus_full_stack_sweep checks the UNSAT result but
// not the proof artifact.
// ============================================================================

#[test]
#[timeout(600_000)]
fn gate_repo_unsat_corpus_full_stack_drat() {
    let corpus_dir = test_common::workspace_root().join("benchmarks/sat/unsat");
    let mut cnf_paths: Vec<_> = std::fs::read_dir(&corpus_dir)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", corpus_dir.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .filter(|path| is_fail_closed_known_unsat_benchmark(path))
        .collect();
    cnf_paths.sort();
    assert!(
        !cnf_paths.is_empty(),
        "expected at least one UNSAT benchmark in {}",
        corpus_dir.display()
    );

    for path in cnf_paths {
        let label = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("<unknown>");
        let dimacs = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        verify_full_stack_unsat_with_native_drat(
            &dimacs,
            &format!("full-stack-drat-corpus/{label}"),
        );
    }
}

// ============================================================================
// Full-stack DRAT proof verification on gate benchmarks (#7913 Phase A)
//
// Verifies that default-config proof-mode solves produce valid
// DRAT proofs on the gate benchmarks (barrel6, longmult15).
// ============================================================================

#[test]
#[timeout(600_000)]
fn gate_full_stack_drat_gate_benchmarks() {
    for name in GATE_BENCHMARKS {
        let Some(content) = try_load_benchmark(name) else {
            continue;
        };
        verify_full_stack_unsat_with_native_drat(&content, &format!("full-stack-drat/{name}"));
    }
}
