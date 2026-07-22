// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof verification with inprocessing features enabled.
//!
//! The existing `drat_coverage.rs` tests verify DRAT proofs with default solver
//! settings.  This file exercises specific inprocessing configurations to ensure
//! that BVE, subsumption, vivification, and "all-inprocessing" modes emit valid
//! DRAT proofs.
//!
//! For each configuration, a subset of the smallest UNSAT benchmarks is solved
//! with that configuration active, and the resulting DRAT proof is verified
//! using the ay-drat-check in-process forward checker.
//!
//! Part of #7913.

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_sat::{parse_dimacs, ProofOutput, Solver};
use ntest::timeout;
use std::path::{Path, PathBuf};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

/// The 8 smallest UNSAT benchmarks by line count, providing fast test execution
/// while still covering diverse formula structures (cardinality, resolution
/// chains, pigeonhole, graph coloring, mutex, Tseitin).
const BENCHMARKS: &[&str] = &[
    "benchmarks/sat/unsat/cardinality_8.cnf",
    "benchmarks/sat/unsat/blocked_chain_8.cnf",
    "benchmarks/sat/unsat/resolution_chain_12.cnf",
    "benchmarks/sat/unsat/at_most_1_of_5.cnf",
    "benchmarks/sat/unsat/urquhart_3.cnf",
    "benchmarks/sat/unsat/mutex_4proc.cnf",
    "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
    "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
];

/// Inprocessing configuration to apply before solving.
#[derive(Debug, Clone, Copy)]
enum InprocConfig {
    /// Only BVE enabled; all other inprocessing disabled.
    BveOnly,
    /// Only subsumption enabled; all other inprocessing disabled.
    SubsumeOnly,
    /// Only vivification enabled; all other inprocessing disabled.
    VivifyOnly,
    /// All inprocessing features enabled (the default state).
    AllEnabled,
}

impl InprocConfig {
    fn label(self) -> &'static str {
        match self {
            Self::BveOnly => "bve_only",
            Self::SubsumeOnly => "subsume_only",
            Self::VivifyOnly => "vivify_only",
            Self::AllEnabled => "all_enabled",
        }
    }
}

/// Apply the given inprocessing configuration to a solver.
///
/// For the "only" variants, we first disable all inprocessing, then selectively
/// re-enable the technique under test. Preprocessing is left enabled so the
/// technique fires during the preprocess pass (BVE, subsumption) or during
/// inprocessing rounds (vivification).
fn apply_config(solver: &mut Solver, config: InprocConfig) {
    match config {
        InprocConfig::BveOnly => {
            solver.disable_all_inprocessing();
            solver.set_bve_enabled(true);
        }
        InprocConfig::SubsumeOnly => {
            solver.disable_all_inprocessing();
            solver.set_subsume_enabled(true);
        }
        InprocConfig::VivifyOnly => {
            solver.disable_all_inprocessing();
            solver.set_vivify_enabled(true);
        }
        InprocConfig::AllEnabled => {
            // Default state: all techniques already enabled. Nothing to do.
        }
    }
}

/// Solve a benchmark with DRAT proof output under the given inprocessing
/// configuration, then verify the proof using the ay-drat-check forward
/// checker.
///
/// Panics on any failure (solve not UNSAT, proof parse error, verification
/// failure) with a diagnostic message identifying the benchmark and config.
fn solve_and_verify(cnf_relative: &str, config: InprocConfig) {
    let cnf_path = workspace_root().join(cnf_relative);
    let bench_name = cnf_path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    let tag = format!("{}+{}", bench_name, config.label());

    let cnf_text =
        std::fs::read_to_string(&cnf_path).unwrap_or_else(|e| panic!("{tag}: read error: {e}"));

    let formula = parse_dimacs(&cnf_text).unwrap_or_else(|e| panic!("{tag}: parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    apply_config(&mut solver, config);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{tag}: expected UNSAT, got {result:?}");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof flush");

    assert!(!proof_bytes.is_empty(), "{tag}: proof is empty (0 bytes)");

    // Verify with ay-drat-check in-process forward checker.
    let cnf_for_check =
        parse_cnf(cnf_text.as_bytes()).unwrap_or_else(|e| panic!("{tag}: CNF parse: {e}"));
    let steps = parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{tag}: DRAT parse: {e}"));

    assert!(!steps.is_empty(), "{tag}: DRAT proof has 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{tag}: DRAT verification FAILED ({} bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "{tag}: DRAT verified ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

/// Run all benchmarks under a single inprocessing configuration.
fn run_config_suite(config: InprocConfig) {
    let mut failures = Vec::new();
    for &bench in BENCHMARKS {
        let result = std::panic::catch_unwind(|| solve_and_verify(bench, config));
        if let Err(e) = result {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = e.downcast_ref::<&str>() {
                (*s).to_owned()
            } else {
                format!("{bench} panicked")
            };
            failures.push(msg);
        }
    }

    assert!(
        failures.is_empty(),
        "DRAT inprocessing failures for {} ({} of {}):\n{}",
        config.label(),
        failures.len(),
        BENCHMARKS.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Suite tests: one per inprocessing configuration
// ---------------------------------------------------------------------------

/// BVE-only: verify that bounded variable elimination produces valid DRAT proofs
/// on all 8 benchmark formulas.
#[test]
#[timeout(60_000)]
fn test_drat_inprocessing_bve_only() {
    run_config_suite(InprocConfig::BveOnly);
}

/// Subsumption-only: verify that subsumption (forward + self-subsumption)
/// produces valid DRAT proofs on all 8 benchmark formulas.
#[test]
#[timeout(60_000)]
fn test_drat_inprocessing_subsume_only() {
    run_config_suite(InprocConfig::SubsumeOnly);
}

/// Vivification-only: verify that clause vivification produces valid DRAT proofs
/// on all 8 benchmark formulas.
#[test]
#[timeout(60_000)]
fn test_drat_inprocessing_vivify_only() {
    run_config_suite(InprocConfig::VivifyOnly);
}

/// All inprocessing enabled: verify that the full inprocessing pipeline
/// (BVE + subsumption + vivification + probing + decompose + ...) produces
/// valid DRAT proofs on all 8 benchmark formulas.
#[test]
#[timeout(60_000)]
fn test_drat_inprocessing_all_enabled() {
    run_config_suite(InprocConfig::AllEnabled);
}

// ---------------------------------------------------------------------------
// Individual per-benchmark tests for granular CI failure reporting
// ---------------------------------------------------------------------------

macro_rules! individual_drat_inproc_test {
    ($test_name:ident, $bench:expr, $config:expr) => {
        #[test]
        #[timeout(15_000)]
        fn $test_name() {
            solve_and_verify($bench, $config);
        }
    };
}

// BVE-only individual tests
individual_drat_inproc_test!(
    test_drat_bve_cardinality_8,
    "benchmarks/sat/unsat/cardinality_8.cnf",
    InprocConfig::BveOnly
);
individual_drat_inproc_test!(
    test_drat_bve_resolution_chain_12,
    "benchmarks/sat/unsat/resolution_chain_12.cnf",
    InprocConfig::BveOnly
);
individual_drat_inproc_test!(
    test_drat_bve_php_4_3,
    "benchmarks/sat/unsat/at_most_1_of_5.cnf",
    InprocConfig::BveOnly
);
individual_drat_inproc_test!(
    test_drat_bve_mutex_4proc,
    "benchmarks/sat/unsat/mutex_4proc.cnf",
    InprocConfig::BveOnly
);

// Subsumption-only individual tests
individual_drat_inproc_test!(
    test_drat_subsume_cardinality_8,
    "benchmarks/sat/unsat/cardinality_8.cnf",
    InprocConfig::SubsumeOnly
);
individual_drat_inproc_test!(
    test_drat_subsume_tseitin_cycle_11,
    "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
    InprocConfig::SubsumeOnly
);
individual_drat_inproc_test!(
    test_drat_subsume_urquhart_3,
    "benchmarks/sat/unsat/urquhart_3.cnf",
    InprocConfig::SubsumeOnly
);

// Vivification-only individual tests
individual_drat_inproc_test!(
    test_drat_vivify_cardinality_8,
    "benchmarks/sat/unsat/cardinality_8.cnf",
    InprocConfig::VivifyOnly
);
individual_drat_inproc_test!(
    test_drat_vivify_latin_square_2x2,
    "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
    InprocConfig::VivifyOnly
);
individual_drat_inproc_test!(
    test_drat_vivify_blocked_chain_8,
    "benchmarks/sat/unsat/blocked_chain_8.cnf",
    InprocConfig::VivifyOnly
);

// All-enabled individual tests
individual_drat_inproc_test!(
    test_drat_all_cardinality_8,
    "benchmarks/sat/unsat/cardinality_8.cnf",
    InprocConfig::AllEnabled
);
individual_drat_inproc_test!(
    test_drat_all_mutex_4proc,
    "benchmarks/sat/unsat/mutex_4proc.cnf",
    InprocConfig::AllEnabled
);
individual_drat_inproc_test!(
    test_drat_all_tseitin_cycle_11,
    "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
    InprocConfig::AllEnabled
);
individual_drat_inproc_test!(
    test_drat_all_urquhart_3,
    "benchmarks/sat/unsat/urquhart_3.cnf",
    InprocConfig::AllEnabled
);
