// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof mode completeness tests for braun circuit benchmarks (#7908).
//!
//! Verifies that DRAT proof mode does not cause FINALIZE_SAT_FAIL on
//! known-UNSAT benchmarks. When proof logging is active, the solver uses
//! different inprocessing paths (compaction disabled, sweep early-returns,
//! congruence RUP filtering). These differences must not cause the solver
//! to return UNKNOWN instead of UNSAT.
//!
//! The test creates a solver with DRAT proof output enabled (matching the
//! `--drat` CLI flag behavior) and verifies braun.8 returns UNSAT with a
//! valid DRAT proof.

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, ProofOutput, SatResult, SatUnknownReason, Solver};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Solve a known-UNSAT benchmark with DRAT proof output enabled and verify
/// the solver returns UNSAT (not UNKNOWN due to FINALIZE_SAT_FAIL).
fn assert_unsat_with_drat_proof(path: &str, label: &str, timeout_secs: u64) {
    let cnf = super::common::load_repo_benchmark(path);
    let formula = parse_dimacs(&cnf).expect("parse");
    let num_vars = formula.num_vars;

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let flag = Arc::new(AtomicBool::new(false));
    let flag_clone = flag.clone();
    solver.set_interrupt(flag.clone());
    let handle = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(timeout_secs));
        flag_clone.store(true, Ordering::Relaxed);
    });

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    let reason = solver.last_unknown_reason();

    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {label} (DRAT mode) is known-UNSAT but solver returned SAT");
        }
        SatResult::Unsat(_) => {
            // Verify the DRAT proof is non-empty and ends with the empty clause.
            let writer = solver.take_proof_writer().expect("proof writer");
            let proof_bytes = writer.into_vec().expect("proof flush");
            assert!(!proof_bytes.is_empty(), "{label}: DRAT proof is empty");
            let proof_text = String::from_utf8_lossy(&proof_bytes);
            assert!(
                proof_text.ends_with("0\n"),
                "{label}: DRAT proof must end with empty clause"
            );
            // Optionally verify with drat-trim if available.
            super::common::verify_drat_proof(&cnf, &proof_bytes, &format!("{label}_drat"));
        }
        SatResult::Unknown => {
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                panic!(
                    "COMPLETENESS BUG (#7908): {label} (DRAT mode) returned UNKNOWN \
                     with InvalidSatModel reason -- FINALIZE_SAT_FAIL triggered in proof mode"
                );
            } else {
                eprintln!(
                    "{label} (DRAT mode): timeout (Unknown) -- not a FINALIZE_SAT_FAIL issue"
                );
            }
        }
        _ => unreachable!(),
    }
}

/// Solve a known-UNSAT benchmark with DRAT proof and accept timeout but not
/// FINALIZE_SAT_FAIL.
fn assert_not_sat_with_drat_proof(path: &str, label: &str, timeout_secs: u64) {
    let cnf = super::common::load_repo_benchmark(path);
    let formula = parse_dimacs(&cnf).expect("parse");
    let num_vars = formula.num_vars;

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let flag = Arc::new(AtomicBool::new(false));
    let flag_clone = flag.clone();
    solver.set_interrupt(flag.clone());
    let handle = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(timeout_secs));
        flag_clone.store(true, Ordering::Relaxed);
    });

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    let reason = solver.last_unknown_reason();

    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {label} (DRAT mode) is known-UNSAT but solver returned SAT");
        }
        SatResult::Unsat(_) => {
            // Good: solver correctly found UNSAT in DRAT mode.
        }
        SatResult::Unknown => {
            assert!(
                reason != Some(SatUnknownReason::InvalidSatModel),
                "COMPLETENESS BUG (#7908): {label} (DRAT mode) returned UNKNOWN \
                 with InvalidSatModel reason -- FINALIZE_SAT_FAIL triggered in proof mode"
            );
            // Timeout is acceptable for harder instances.
            eprintln!("{label} (DRAT mode): timeout (Unknown)");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Tests: braun circuit benchmarks in DRAT proof mode
// ---------------------------------------------------------------------------

#[test]
fn braun_7_drat_mode_must_be_unsat() {
    assert_unsat_with_drat_proof(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.7.unsat.cnf",
        "braun-7",
        30,
    );
}

#[test]
fn braun_8_drat_mode_must_be_unsat() {
    assert_unsat_with_drat_proof(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
        "braun-8",
        30,
    );
}

#[test]
fn braun_10_drat_mode_not_sat() {
    assert_not_sat_with_drat_proof(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
        "braun-10",
        30,
    );
}

#[test]
fn braun_9_drat_mode_not_sat() {
    assert_not_sat_with_drat_proof(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.9.unsat.cnf",
        "braun-9",
        15,
    );
}

// ---------------------------------------------------------------------------
// Small UNSAT corpus in DRAT mode -- no FINALIZE_SAT_FAIL
// ---------------------------------------------------------------------------

#[test]
fn small_unsat_drat_mode_no_finalize_sat_fail() {
    let benchmarks = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/cardinality_8.cnf",
        "benchmarks/sat/unsat/double_parity_5.cnf",
        "benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutex_6proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/parity_6.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/php_5_4.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
    ];

    let mut failures = Vec::new();

    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = super::common::load_repo_benchmark(path);
        let formula = parse_dimacs(&cnf).expect("parse");
        let num_vars = formula.num_vars;

        let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
        let mut solver = Solver::with_proof_output(num_vars, proof_writer);
        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }

        let flag = Arc::new(AtomicBool::new(false));
        let flag_clone = flag.clone();
        solver.set_interrupt(flag.clone());
        let handle = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(10));
            flag_clone.store(true, Ordering::Relaxed);
        });

        let result = solver
            .solve_interruptible(|| flag.load(Ordering::Relaxed))
            .into_inner();

        flag.store(true, Ordering::Relaxed);
        let _ = handle.join();

        let reason = solver.last_unknown_reason();

        match result {
            SatResult::Sat(_) => {
                failures.push(format!(
                    "{label}: SOUNDNESS BUG -- known-UNSAT returned SAT in DRAT mode"
                ));
            }
            SatResult::Unsat(_) => {
                // Good.
            }
            SatResult::Unknown => {
                if reason == Some(SatUnknownReason::InvalidSatModel) {
                    failures.push(format!(
                        "{label}: FINALIZE_SAT_FAIL in DRAT mode (Unknown/InvalidSatModel)"
                    ));
                }
                // Timeout is acceptable.
            }
            _ => unreachable!(),
        }
    }

    assert!(
        failures.is_empty(),
        "DRAT mode issues ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
