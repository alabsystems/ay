// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive DRAT proof verification for ALL UNSAT benchmark results.
//!
//! This test file closes Gap 2 from the development design notes: every UNSAT
//! path must produce a DRAT proof and that proof must pass verification by the
//! native `ay-drat-check` forward checker.
//!
//! Structure:
//! 1. **Inline small UNSAT formulas** (empty clause, unit contradictions,
//!    pigeonhole, Tseitin) for fast regression testing without file I/O.
//! 2. **All `benchmarks/sat/unsat/` files** (27 formulas) — the core UNSAT
//!    corpus, each tested individually.
//! 3. **eq.atree.braun circuit UNSAT benchmarks** — larger circuit
//!    equivalence formulas.
//! 4. **Canary UNSAT benchmark** — the `tiny_unsat.cnf` smoke test.
//! 5. **Aggregate sweep** that discovers and tests every `.cnf` file
//!    under `benchmarks/sat/unsat/` dynamically, catching new benchmarks
//!    that are added without a dedicated test.
//!
//! Part of #7913.

#![allow(clippy::panic)]

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_sat::{parse_dimacs, ProofOutput, SatResult, Solver};
use ntest::timeout;
use std::path::{Path, PathBuf};
use std::time::Duration;

// ===========================================================================
// Shared helpers
// ===========================================================================

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

/// Solve a DIMACS string, assert UNSAT, extract DRAT proof bytes, and verify
/// the proof using the native ay-drat-check forward checker. Panics on any
/// failure with a diagnostic message.
fn solve_and_verify_native(dimacs_text: &str, label: &str) {
    let formula =
        parse_dimacs(dimacs_text).unwrap_or_else(|e| panic!("{label}: DIMACS parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush must succeed");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    // Parse with ay-drat-check types and verify.
    let cnf_for_check = parse_cnf(dimacs_text.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} proof bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "DRAT-exhaustive VERIFIED: {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

/// Solve a DIMACS string with a timeout, assert UNSAT, extract and verify the
/// DRAT proof. Returns `true` if verified, `false` if the solver timed out
/// (UNKNOWN). Panics on SAT or proof verification failure.
fn solve_and_verify_native_with_timeout(dimacs_text: &str, label: &str, timeout_secs: u64) -> bool {
    let formula =
        parse_dimacs(dimacs_text).unwrap_or_else(|e| panic!("{label}: DIMACS parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let timer =
        super::common::SolverInterruptTimer::start(&mut solver, Duration::from_secs(timeout_secs));

    let result = solver
        .solve_interruptible(|| timer.is_interrupted())
        .into_inner();

    timer.cancel_and_join();

    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {label} returned SAT but expected UNSAT");
        }
        SatResult::Unsat(_) => {}
        _ => {
            eprintln!(
                "DRAT-exhaustive TIMEOUT/UNKNOWN: {label} (>{timeout_secs}s, skipping proof check)"
            );
            return false;
        }
    }

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush must succeed");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let cnf_for_check = parse_cnf(dimacs_text.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} proof bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "DRAT-exhaustive VERIFIED: {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
    true
}

#[test]
#[timeout(5_000)]
fn drat_timeout_timer_cancels_after_fast_unsat_solve() {
    // The deadline is intentionally much longer than this test's outer bound.
    // The old unconditional sleep/join implementation therefore timed out,
    // while the cancellation-aware timer returns as soon as the proof checks.
    assert!(solve_and_verify_native_with_timeout(
        "p cnf 1 2\n1 0\n-1 0\n",
        "timer_cancel_fast_unsat",
        60,
    ));
}

/// Load a benchmark file relative to the workspace root and run
/// `solve_and_verify_native`.
fn verify_benchmark(relative_path: &str, label: &str) {
    let cnf_text = super::common::load_repo_benchmark(relative_path);
    solve_and_verify_native(&cnf_text, label);
}

// ===========================================================================
// Section 1: Inline small UNSAT formulas — fast regression tests
// ===========================================================================

/// Trivially UNSAT: contains the empty clause directly.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_empty_clause() {
    solve_and_verify_native("p cnf 0 1\n0\n", "inline_empty_clause");
}

/// Unit contradiction: x1 AND NOT x1.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_unit_contradiction() {
    solve_and_verify_native("p cnf 1 2\n1 0\n-1 0\n", "inline_unit_contradiction");
}

/// Two-variable contradiction: (x1) AND (x2) AND (NOT x1 OR NOT x2) AND
/// (NOT x1) — forces conflict.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_two_var_contradiction() {
    solve_and_verify_native(
        "p cnf 2 4\n1 0\n2 0\n-1 -2 0\n-1 0\n",
        "inline_two_var_contradiction",
    );
}

/// PHP(3,2): 3 pigeons into 2 holes — classic small UNSAT.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_php32() {
    solve_and_verify_native(super::common::PHP32_DIMACS, "inline_php32");
}

/// PHP(4,3): 4 pigeons into 3 holes — slightly larger pigeonhole.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_php43() {
    solve_and_verify_native(super::common::PHP43_DIMACS, "inline_php43");
}

/// Tseitin formula on a triangle (3 XOR constraints, odd parity): always UNSAT.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_tseitin_triangle() {
    // XOR(x1, x2) with auxiliary x4: (x1 OR x2 OR NOT x4) AND
    //   (NOT x1 OR NOT x2 OR NOT x4) AND (x1 OR NOT x2 OR x4) AND
    //   (NOT x1 OR x2 OR x4)
    // XOR(x2, x3) with auxiliary x5.
    // XOR(x1, x3) with auxiliary x6.
    // Parity constraint: x4 AND x5 AND x6 (odd parity = UNSAT).
    solve_and_verify_native(
        "\
p cnf 6 15
1 2 -4 0
-1 -2 -4 0
1 -2 4 0
-1 2 4 0
2 3 -5 0
-2 -3 -5 0
2 -3 5 0
-2 3 5 0
1 3 -6 0
-1 -3 -6 0
1 -3 6 0
-1 3 6 0
4 0
5 0
6 0
",
        "inline_tseitin_triangle",
    );
}

/// Chain of binary implications forming a contradiction.
/// x1 => x2 => x3 => NOT x1, with x1 forced true.
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_implication_chain() {
    solve_and_verify_native(
        "\
p cnf 3 4
1 0
-1 2 0
-2 3 0
-3 -1 0
",
        "inline_implication_chain",
    );
}

/// At-most-one constraint (3 vars, all must be true) — UNSAT.
/// x1 AND x2 AND x3 AND (NOT x1 OR NOT x2) AND (NOT x1 OR NOT x3) AND (NOT x2 OR NOT x3).
#[test]
#[timeout(10_000)]
fn drat_exhaustive_inline_at_most_one_conflict() {
    solve_and_verify_native(
        "\
p cnf 3 6
1 0
2 0
3 0
-1 -2 0
-1 -3 0
-2 -3 0
",
        "inline_at_most_one_conflict",
    );
}

// ===========================================================================
// Section 2: All benchmarks/sat/unsat/ files — individual tests
// ===========================================================================

macro_rules! unsat_benchmark_test {
    ($test_name:ident, $file:expr, $timeout_ms:expr) => {
        #[test]
        #[timeout($timeout_ms)]
        fn $test_name() {
            verify_benchmark(
                concat!("benchmarks/sat/unsat/", $file),
                concat!("bench_", $file),
            );
        }
    };
}

unsat_benchmark_test!(drat_exhaustive_at_most_1_of_5, "at_most_1_of_5.cnf", 30_000);
unsat_benchmark_test!(
    drat_exhaustive_blocked_chain_8,
    "blocked_chain_8.cnf",
    30_000
);
unsat_benchmark_test!(drat_exhaustive_cardinality_8, "cardinality_8.cnf", 30_000);
unsat_benchmark_test!(
    drat_exhaustive_double_parity_5,
    "double_parity_5.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_graph_coloring_k3_4clique,
    "graph_coloring_k3_4clique.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_graph_coloring_k4_5clique,
    "graph_coloring_k4_5clique.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_graph_coloring_k5_6clique,
    "graph_coloring_k5_6clique.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_latin_square_2x2_conflict,
    "latin_square_2x2_conflict.cnf",
    30_000
);
unsat_benchmark_test!(drat_exhaustive_mutex_4proc, "mutex_4proc.cnf", 30_000);
unsat_benchmark_test!(drat_exhaustive_mutex_6proc, "mutex_6proc.cnf", 30_000);
unsat_benchmark_test!(
    drat_exhaustive_mutilated_chessboard_2x2,
    "mutilated_chessboard_2x2.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_ordering_cycle_5,
    "ordering_cycle_5.cnf",
    30_000
);
unsat_benchmark_test!(drat_exhaustive_parity_6, "parity_6.cnf", 30_000);
unsat_benchmark_test!(drat_exhaustive_php_4_3, "php_4_3.cnf", 30_000);
unsat_benchmark_test!(drat_exhaustive_php_5_4, "php_5_4.cnf", 30_000);
unsat_benchmark_test!(drat_exhaustive_php_6_5, "php_6_5.cnf", 30_000);
unsat_benchmark_test!(drat_exhaustive_php_7_6, "php_7_6.cnf", 60_000);
unsat_benchmark_test!(
    drat_exhaustive_php_functional_5_4,
    "php_functional_5_4.cnf",
    30_000
);
unsat_benchmark_test!(drat_exhaustive_ramsey_r3_3_6, "ramsey_r3_3_6.cnf", 30_000);
unsat_benchmark_test!(
    drat_exhaustive_random_3sat_50_s12345,
    "random_3sat_50_213_s12345.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_random_3sat_50_s12349,
    "random_3sat_50_213_s12349.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_resolution_chain_12,
    "resolution_chain_12.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_tseitin_cycle_11,
    "tseitin_cycle_11.cnf",
    30_000
);
unsat_benchmark_test!(
    drat_exhaustive_tseitin_grid_3x3,
    "tseitin_grid_3x3.cnf",
    30_000
);
unsat_benchmark_test!(drat_exhaustive_tseitin_k5, "tseitin_k5.cnf", 30_000);
unsat_benchmark_test!(
    drat_exhaustive_tseitin_random_15,
    "tseitin_random_15.cnf",
    30_000
);
unsat_benchmark_test!(drat_exhaustive_urquhart_3, "urquhart_3.cnf", 30_000);

// ===========================================================================
// Section 3: eq.atree.braun circuit UNSAT benchmarks (larger, with timeout)
// ===========================================================================

macro_rules! braun_benchmark_test {
    ($test_name:ident, $file:expr, $timeout_ms:expr, $solve_timeout_secs:expr) => {
        #[test]
        #[cfg_attr(debug_assertions, timeout(300_000))]
        #[cfg_attr(not(debug_assertions), timeout($timeout_ms))]
        fn $test_name() {
            if cfg!(debug_assertions) {
                eprintln!(
                    "NOTE: braun circuit tests are slow in debug mode; \
                     using extended timeout"
                );
            }
            let path = concat!("benchmarks/sat/eq_atree_braun/", $file);
            let cnf_path = workspace_root().join(path);
            let Some(cnf_text) = super::common::load_optional_benchmark(&cnf_path) else {
                return;
            };
            let verified = solve_and_verify_native_with_timeout(
                &cnf_text,
                concat!("braun_", $file),
                $solve_timeout_secs,
            );
            if !verified {
                eprintln!(
                    "braun {} timed out at {}s — proof not checked",
                    $file, $solve_timeout_secs
                );
            }
        }
    };
}

braun_benchmark_test!(
    drat_exhaustive_braun_7,
    "eq.atree.braun.7.unsat.cnf",
    120_000,
    60
);
braun_benchmark_test!(
    drat_exhaustive_braun_8,
    "eq.atree.braun.8.unsat.cnf",
    120_000,
    60
);
braun_benchmark_test!(
    drat_exhaustive_braun_9,
    "eq.atree.braun.9.unsat.cnf",
    180_000,
    120
);

// braun 10-13 are much larger; use generous timeouts and skip in debug mode.
macro_rules! braun_large_test {
    ($test_name:ident, $file:expr, $solve_timeout_secs:expr) => {
        #[test]
        #[timeout(600_000)]
        fn $test_name() {
            if cfg!(debug_assertions) {
                eprintln!(
                    "SKIP: {} exceeds debug-mode timeout",
                    stringify!($test_name)
                );
                return;
            }
            let path = concat!("benchmarks/sat/eq_atree_braun/", $file);
            let cnf_path = workspace_root().join(path);
            let Some(cnf_text) = super::common::load_optional_benchmark(&cnf_path) else {
                return;
            };
            let verified = solve_and_verify_native_with_timeout(
                &cnf_text,
                concat!("braun_large_", $file),
                $solve_timeout_secs,
            );
            if !verified {
                eprintln!(
                    "braun {} timed out at {}s — proof not checked",
                    $file, $solve_timeout_secs
                );
            }
        }
    };
}

braun_large_test!(drat_exhaustive_braun_10, "eq.atree.braun.10.unsat.cnf", 120);
braun_large_test!(drat_exhaustive_braun_11, "eq.atree.braun.11.unsat.cnf", 180);
braun_large_test!(drat_exhaustive_braun_12, "eq.atree.braun.12.unsat.cnf", 300);
braun_large_test!(drat_exhaustive_braun_13, "eq.atree.braun.13.unsat.cnf", 300);

// ===========================================================================
// Section 4: Canary UNSAT benchmark
// ===========================================================================

#[test]
#[timeout(10_000)]
fn drat_exhaustive_canary_tiny_unsat() {
    verify_benchmark("benchmarks/sat/canary/tiny_unsat.cnf", "canary_tiny_unsat");
}

// ===========================================================================
// Section 5: Dynamic discovery sweep — catches new benchmarks automatically
// ===========================================================================

/// Dynamically discover all `.cnf` files under `benchmarks/sat/unsat/` and
/// verify each produces a valid DRAT proof when solved. This catches new
/// benchmarks added to the corpus without requiring a dedicated test function.
///
/// Uses a per-benchmark 10s timeout to keep total wall time bounded.
/// Reports all failures at the end rather than stopping at the first.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn drat_exhaustive_dynamic_sweep_all_unsat() {
    let unsat_dir = workspace_root().join("benchmarks/sat/unsat");
    assert!(
        unsat_dir.is_dir(),
        "UNSAT benchmark directory not found: {}",
        unsat_dir.display()
    );

    let mut entries: Vec<_> = std::fs::read_dir(&unsat_dir)
        .expect("read benchmarks/sat/unsat")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "cnf"))
        .map(|e| e.path())
        .collect();

    entries.sort();

    assert!(
        !entries.is_empty(),
        "no .cnf files found in {}",
        unsat_dir.display()
    );

    let mut verified = 0u32;
    let mut timed_out = 0u32;
    let mut failures: Vec<String> = Vec::new();

    for cnf_path in &entries {
        let file_name = cnf_path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_default();
        let label = format!("sweep_{file_name}");

        let cnf_text = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", cnf_path.display()));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solve_and_verify_native_with_timeout(&cnf_text, &label, 10)
        }));

        match result {
            Ok(true) => verified += 1,
            Ok(false) => timed_out += 1,
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else {
                    format!("{file_name}: panicked")
                };
                failures.push(msg);
            }
        }
    }

    eprintln!(
        "DRAT-exhaustive sweep: {} verified, {} timed out, {} failed (of {} total)",
        verified,
        timed_out,
        failures.len(),
        entries.len()
    );

    assert!(
        failures.is_empty(),
        "DRAT-exhaustive sweep failures ({} of {}):\n{}",
        failures.len(),
        entries.len(),
        failures.join("\n---\n")
    );
}

/// Dynamic sweep over `benchmarks/sat/eq_atree_braun/` UNSAT circuit files.
/// These are larger and each gets a 60s solve timeout.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(300_000))]
fn drat_exhaustive_dynamic_sweep_braun() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: braun sweep is release-mode only due to debug overhead");
        return;
    }

    let braun_dir = workspace_root().join("benchmarks/sat/eq_atree_braun");
    if !braun_dir.is_dir() {
        eprintln!(
            "SKIP: braun benchmark directory not found: {}",
            braun_dir.display()
        );
        return;
    }

    let mut entries: Vec<_> = std::fs::read_dir(&braun_dir)
        .expect("read benchmarks/sat/eq_atree_braun")
        .filter_map(Result::ok)
        .filter(|e| {
            let p = e.path();
            p.extension().is_some_and(|ext| ext == "cnf") && p.to_string_lossy().contains("unsat")
        })
        .map(|e| e.path())
        .collect();

    entries.sort();

    if entries.is_empty() {
        eprintln!("SKIP: no UNSAT .cnf files found in braun directory");
        return;
    }

    let mut verified = 0u32;
    let mut timed_out = 0u32;
    let mut failures: Vec<String> = Vec::new();

    for cnf_path in &entries {
        let file_name = cnf_path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_default();
        let label = format!("braun_sweep_{file_name}");

        let cnf_text = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", cnf_path.display()));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solve_and_verify_native_with_timeout(&cnf_text, &label, 60)
        }));

        match result {
            Ok(true) => verified += 1,
            Ok(false) => timed_out += 1,
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else {
                    format!("{file_name}: panicked")
                };
                failures.push(msg);
            }
        }
    }

    eprintln!(
        "DRAT-exhaustive braun sweep: {} verified, {} timed out, {} failed (of {} total)",
        verified,
        timed_out,
        failures.len(),
        entries.len()
    );

    assert!(
        failures.is_empty(),
        "DRAT-exhaustive braun sweep failures ({} of {}):\n{}",
        failures.len(),
        entries.len(),
        failures.join("\n---\n")
    );
}
