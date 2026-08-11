// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof coverage expansion: external drat-trim verification for
//! benchmarks that previously had no DRAT proof checking.
//!
//! Gap 2 in the development design notes: "Only 7.7% of tests use DRAT
//! verification." This file systematically adds drat-trim verification
//! to three categories of UNSAT benchmarks:
//!
//! 1. **benchmarks/sat/unsat/ gaps**: 11 formulas that had no individual
//!    drat-trim test (some were only tested via ay-drat-check or the
//!    corpus test, but not drat-trim).
//!
//! 2. **uuf50 random 3-SAT**: 20 of the 1000 uuf50 benchmarks from
//!    reference/creusat/tests/cnf/unsat/. These are 50-variable random
//!    3-SAT instances that exercise core CDCL proof generation.
//!
//! 3. **uuf250 random 3-SAT**: 10 of the 100 uuf250 benchmarks from
//!    reference/creusat/tests/cnf-hard/unsat/. These are 250-variable
//!    instances that exercise proof generation on harder instances.
//!
//! Part of #7913.

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, ProofOutput, Solver};
use ntest::timeout;

// ---------------------------------------------------------------------------
// Helper: solve with DRAT proof and verify via drat-trim
// ---------------------------------------------------------------------------

/// Solve a benchmark file with DRAT proof output enabled, assert UNSAT,
/// and verify the proof with external drat-trim.
///
/// Returns `false` (and skips gracefully) when the benchmark file is missing
/// outside CI. In CI, a missing benchmark panics immediately.
fn solve_and_verify_drat(cnf_relative_path: &str, label: &str) -> bool {
    let Some(cnf_text) = super::common::load_optional_repo_benchmark(cnf_relative_path) else {
        return false;
    };
    let formula = parse_dimacs(&cnf_text).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let dimacs = super::common::clauses_to_dimacs(formula.num_vars, &formula.clauses);
    super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
    true
}

/// Solve an absolute-path benchmark file with DRAT proof and verify.
///
/// The only caller reads from `reference/creusat`, an OPTIONAL external
/// checkout (no `.gitmodules` entry, not shipped with the repository), so a
/// missing corpus skips loudly instead of failing — the same contract the
/// `creusat_drat_test!` macro in `drat_exhaustive_coverage.rs` already uses.
/// Every assertion below is unchanged and still runs whenever the checkout is
/// present.
fn solve_and_verify_drat_abs(cnf_path: &str, label: &str) {
    let Some(cnf_text) = super::common::load_optional_benchmark(cnf_path) else {
        return;
    };
    let formula = parse_dimacs(&cnf_text).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let dimacs = super::common::clauses_to_dimacs(formula.num_vars, &formula.clauses);
    super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
}

// ===========================================================================
// Category 1: benchmarks/sat/unsat/ formulas without drat-trim coverage
// ===========================================================================
//
// These formulas were previously tested via ay-drat-check (in-process) or
// the corpus test but not verified by the external drat-trim checker.

#[test]
#[timeout(30_000)]
fn drat_coverage_double_parity_5() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/double_parity_5.cnf",
        "drat_double_parity_5",
    );
}

#[test]
#[timeout(30_000)]
fn drat_coverage_graph_coloring_k5_6clique() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/graph_coloring_k5_6clique.cnf",
        "drat_graph_coloring_k5_6clique",
    );
}

#[test]
#[timeout(30_000)]
fn drat_coverage_mutex_6proc() {
    solve_and_verify_drat("benchmarks/sat/unsat/mutex_6proc.cnf", "drat_mutex_6proc");
}

#[test]
#[timeout(30_000)]
fn drat_coverage_ordering_cycle_5() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "drat_ordering_cycle_5",
    );
}

#[test]
#[timeout(30_000)]
fn drat_coverage_php_6_5() {
    solve_and_verify_drat("benchmarks/sat/unsat/php_6_5.cnf", "drat_php_6_5");
}

#[test]
#[timeout(60_000)]
fn drat_coverage_php_7_6() {
    solve_and_verify_drat("benchmarks/sat/unsat/php_7_6.cnf", "drat_php_7_6");
}

#[test]
#[timeout(30_000)]
fn drat_coverage_php_functional_5_4() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/php_functional_5_4.cnf",
        "drat_php_functional_5_4",
    );
}

#[test]
#[timeout(30_000)]
fn drat_coverage_random_3sat_50_s12345() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf",
        "drat_random_3sat_50_s12345",
    );
}

#[test]
#[timeout(30_000)]
fn drat_coverage_random_3sat_50_s12349() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/random_3sat_50_213_s12349.cnf",
        "drat_random_3sat_50_s12349",
    );
}

#[test]
#[timeout(30_000)]
fn drat_coverage_tseitin_k5() {
    solve_and_verify_drat("benchmarks/sat/unsat/tseitin_k5.cnf", "drat_tseitin_k5");
}

#[test]
#[timeout(30_000)]
fn drat_coverage_tseitin_random_15() {
    solve_and_verify_drat(
        "benchmarks/sat/unsat/tseitin_random_15.cnf",
        "drat_tseitin_random_15",
    );
}

// ===========================================================================
// Category 2: uuf50 random 3-SAT UNSAT (50 vars, 218 clauses)
// ===========================================================================
//
// Selected 20 instances spread across the 1000-file corpus for diversity.
// These are trivially fast to solve but exercise core CDCL proof emission.

const UUF50_DIR: &str = "reference/creusat/tests/cnf/unsat";

macro_rules! uuf50_drat_test {
    ($test_name:ident, $file:expr) => {
        #[test]
        #[timeout(15_000)]
        fn $test_name() {
            let path = format!("{}/{}", UUF50_DIR, $file);
            solve_and_verify_drat(&path, concat!("drat_", stringify!($test_name)));
        }
    };
}

uuf50_drat_test!(drat_uuf50_01, "uuf50-01.cnf");
uuf50_drat_test!(drat_uuf50_050, "uuf50-050.cnf");
uuf50_drat_test!(drat_uuf50_0100, "uuf50-0100.cnf");
uuf50_drat_test!(drat_uuf50_0150, "uuf50-0150.cnf");
uuf50_drat_test!(drat_uuf50_0200, "uuf50-0200.cnf");
uuf50_drat_test!(drat_uuf50_0250, "uuf50-0250.cnf");
uuf50_drat_test!(drat_uuf50_0300, "uuf50-0300.cnf");
uuf50_drat_test!(drat_uuf50_0400, "uuf50-0400.cnf");
uuf50_drat_test!(drat_uuf50_0500, "uuf50-0500.cnf");
uuf50_drat_test!(drat_uuf50_0600, "uuf50-0600.cnf");
uuf50_drat_test!(drat_uuf50_0700, "uuf50-0700.cnf");
uuf50_drat_test!(drat_uuf50_0800, "uuf50-0800.cnf");
uuf50_drat_test!(drat_uuf50_0900, "uuf50-0900.cnf");
uuf50_drat_test!(drat_uuf50_01000, "uuf50-01000.cnf");
uuf50_drat_test!(drat_uuf50_0101, "uuf50-0101.cnf");
uuf50_drat_test!(drat_uuf50_0202, "uuf50-0202.cnf");
uuf50_drat_test!(drat_uuf50_0303, "uuf50-0303.cnf");
uuf50_drat_test!(drat_uuf50_0404, "uuf50-0404.cnf");
uuf50_drat_test!(drat_uuf50_0505, "uuf50-0505.cnf");
uuf50_drat_test!(drat_uuf50_0707, "uuf50-0707.cnf");

/// Batch test: solve all 20 uuf50 instances in one test for aggregate timing.
///
/// Skips gracefully when reference/creusat is not initialised.
#[test]
#[timeout(60_000)]
fn drat_uuf50_batch_20() {
    let files = [
        "uuf50-01.cnf",
        "uuf50-050.cnf",
        "uuf50-0100.cnf",
        "uuf50-0150.cnf",
        "uuf50-0200.cnf",
        "uuf50-0250.cnf",
        "uuf50-0300.cnf",
        "uuf50-0400.cnf",
        "uuf50-0500.cnf",
        "uuf50-0600.cnf",
        "uuf50-0700.cnf",
        "uuf50-0800.cnf",
        "uuf50-0900.cnf",
        "uuf50-01000.cnf",
        "uuf50-0101.cnf",
        "uuf50-0202.cnf",
        "uuf50-0303.cnf",
        "uuf50-0404.cnf",
        "uuf50-0505.cnf",
        "uuf50-0707.cnf",
    ];

    let mut verified = 0;
    let mut skipped = 0;
    let mut failures = Vec::new();

    for file in &files {
        let path = format!("{UUF50_DIR}/{file}");
        let label = format!("drat_batch_{file}");
        let result = std::panic::catch_unwind(|| solve_and_verify_drat(&path, &label));
        match result {
            Ok(true) => verified += 1,
            Ok(false) => skipped += 1,
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else {
                    format!("{file}: panicked")
                };
                failures.push(msg);
            }
        }
    }

    eprintln!(
        "uuf50 DRAT batch: {verified}/{} verified, {skipped} skipped",
        files.len()
    );
    assert!(
        failures.is_empty(),
        "uuf50 DRAT failures ({}/{}):\n{}",
        failures.len(),
        files.len(),
        failures.join("\n")
    );
}

// ===========================================================================
// Category 3: uuf250 random 3-SAT UNSAT (250 vars, 1065 clauses)
// ===========================================================================
//
// Harder instances. Selected 10 spread across the 100-file corpus.
// These exercise non-trivial CDCL search + proof generation.

const UUF250_DIR: &str = "reference/creusat/tests/cnf-hard/unsat";

macro_rules! uuf250_drat_test {
    ($test_name:ident, $file:expr) => {
        #[test]
        #[cfg_attr(debug_assertions, timeout(120_000))]
        #[cfg_attr(not(debug_assertions), timeout(60_000))]
        fn $test_name() {
            if cfg!(debug_assertions) {
                eprintln!("SKIP: uuf250 DRAT exceeds debug-mode timeout (#4582)");
                return;
            }
            let path = format!("{}/{}", UUF250_DIR, $file);
            solve_and_verify_drat(&path, concat!("drat_", stringify!($test_name)));
        }
    };
}

uuf250_drat_test!(drat_uuf250_05, "uuf250-05.cnf");
uuf250_drat_test!(drat_uuf250_012, "uuf250-012.cnf");
uuf250_drat_test!(drat_uuf250_024, "uuf250-024.cnf");
uuf250_drat_test!(drat_uuf250_039, "uuf250-039.cnf");
uuf250_drat_test!(drat_uuf250_048, "uuf250-048.cnf");
uuf250_drat_test!(drat_uuf250_058, "uuf250-058.cnf");
uuf250_drat_test!(drat_uuf250_067, "uuf250-067.cnf");
uuf250_drat_test!(drat_uuf250_076, "uuf250-076.cnf");
uuf250_drat_test!(drat_uuf250_088, "uuf250-088.cnf");
uuf250_drat_test!(drat_uuf250_099, "uuf250-099.cnf");

/// Batch test: solve all 10 uuf250 instances. Release-only due to debug
/// mode slowdown.
#[cfg(not(debug_assertions))]
#[test]
#[timeout(180_000)]
fn drat_uuf250_batch_10() {
    let files = [
        "uuf250-05.cnf",
        "uuf250-012.cnf",
        "uuf250-024.cnf",
        "uuf250-039.cnf",
        "uuf250-048.cnf",
        "uuf250-058.cnf",
        "uuf250-067.cnf",
        "uuf250-076.cnf",
        "uuf250-088.cnf",
        "uuf250-099.cnf",
    ];

    let mut verified = 0;
    let mut skipped = 0;
    let mut failures = Vec::new();

    for file in &files {
        let path = format!("{UUF250_DIR}/{file}");
        let label = format!("drat_batch_{file}");
        let result = std::panic::catch_unwind(|| solve_and_verify_drat(&path, &label));
        match result {
            Ok(true) => verified += 1,
            Ok(false) => skipped += 1,
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else {
                    format!("{file}: panicked")
                };
                failures.push(msg);
            }
        }
    }

    eprintln!(
        "uuf250 DRAT batch: {verified}/{} verified, {skipped} skipped",
        files.len()
    );
    assert!(
        failures.is_empty(),
        "uuf250 DRAT failures ({}/{}):\n{}",
        failures.len(),
        files.len(),
        failures.join("\n")
    );
}

// ===========================================================================
// Category 4: CreuSAT easy/unsat benchmarks with drat-trim
// ===========================================================================
//
// barrel6 and minor032 already have DRAT coverage elsewhere. The remaining
// easy/unsat benchmarks (een-tip, manol-pipe-c9) that are solvable in
// release mode within 30s are included here.

#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn drat_coverage_creusat_manol_pipe_c9() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: manol-pipe-c9 DRAT exceeds debug-mode timeout (#4582)");
        return;
    }
    solve_and_verify_drat_abs(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-c9.cnf"
        ),
        "drat_manol_pipe_c9",
    );
}
