// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! SAT soundness regression suite over the SATCOMP benchmark corpus.
//!
//! Recursively discovers all `.cnf` files under `benchmarks/satcomp/` and:
//! - solves each benchmark in-process with `ay-sat`
//! - validates SAT models against the original clauses
//! - validates UNSAT DRAT proofs with in-process `ay-drat-check`
//! - checks for SAT/UNSAT disagreements against CaDiCaL when available
//!
//! This test skips gracefully when the benchmark directory is absent.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use super::common::{workspace_root, OracleResult};
use ay_drat_check::checker::{backward::BackwardChecker, DratChecker};
use ay_sat::{parse_dimacs, Literal, ProofOutput, SatResult, Solver};
use ntest::timeout;
use wait_timeout::ChildExt;

const BENCHMARK_TIMEOUT: Duration = Duration::from_secs(30);

struct AYRun {
    result: SatResult,
    elapsed: Duration,
    proof_bytes: Option<Vec<u8>>,
}

fn discover_cnf_benchmarks(dir: &Path) -> Vec<PathBuf> {
    let mut results = Vec::new();
    if !dir.is_dir() {
        return results;
    }
    collect_cnf_recursive(dir, &mut results);
    results.sort();
    results
}

fn collect_cnf_recursive(dir: &Path, results: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cnf_recursive(&path, results);
        } else if path.extension().is_some_and(|ext| ext == "cnf") {
            results.push(path);
        }
    }
}

fn benchmark_label(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn run_cadical(cadical_path: &Path, cnf_path: &Path) -> OracleResult {
    let mut child = match Command::new(cadical_path)
        .arg("-q")
        .arg(cnf_path)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => return OracleResult::Unavailable,
    };

    match child.wait_timeout(BENCHMARK_TIMEOUT) {
        Ok(Some(status)) => match status.code() {
            Some(10) => OracleResult::Sat,
            Some(20) => OracleResult::Unsat,
            _ => OracleResult::Unknown,
        },
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            OracleResult::Unknown
        }
        Err(_) => OracleResult::Unknown,
    }
}

fn run_ay_with_drat(num_vars: usize, clauses: &[Vec<Literal>]) -> AYRun {
    let mut solver = Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    // Match the DIMACS pure-SAT policy from `DimacsFormula::into_solver()`.
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_subsume_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    let started = Instant::now();
    let result = solver
        .solve_interruptible(|| started.elapsed() >= BENCHMARK_TIMEOUT)
        .into_inner();
    let elapsed = started.elapsed();

    let proof_bytes = if result.is_unsat() {
        let writer = solver
            .take_proof_writer()
            .expect("proof writer should exist");
        Some(writer.into_vec().expect("proof writer flush"))
    } else {
        None
    };

    AYRun {
        result,
        elapsed,
        proof_bytes,
    }
}

fn verify_drat_proof(cnf_dimacs: &str, proof_bytes: &[u8], label: &str) {
    assert!(
        !proof_bytes.is_empty(),
        "{label}: UNSAT proof mode produced an empty DRAT proof"
    );

    let cnf = ay_drat_check::cnf_parser::parse_cnf(cnf_dimacs.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: failed to parse CNF for DRAT checking: {e}"));
    let steps = ay_drat_check::drat_parser::parse_drat(proof_bytes)
        .unwrap_or_else(|e| panic!("{label}: failed to parse DRAT proof: {e}"));

    let mut forward = DratChecker::new(cnf.num_vars, true);
    forward.verify(&cnf.clauses, &steps).unwrap_or_else(|e| {
        let stats = forward.stats();
        panic!(
            "{label}: forward DRAT verification failed: {e}\n\
             stats: original={} additions={} deletions={} checks={} failures={}",
            stats.original, stats.additions, stats.deletions, stats.checks, stats.failures,
        )
    });

    let mut backward = BackwardChecker::new(cnf.num_vars, true);
    backward.verify(&cnf.clauses, &steps).unwrap_or_else(|e| {
        let stats = backward.stats();
        panic!(
            "{label}: backward DRAT verification failed: {e}\n\
             stats: original={} additions={} deletions={} checks={} failures={}",
            stats.original, stats.additions, stats.deletions, stats.checks, stats.failures,
        )
    });
}

#[test]
#[timeout(3_600_000)]
fn satcomp_soundness_regression_suite() {
    let root = workspace_root();
    let benchmark_dir = root.join("benchmarks/satcomp");
    if !benchmark_dir.is_dir() {
        eprintln!(
            "SKIP: benchmark directory not found: {}",
            benchmark_dir.display()
        );
        return;
    }

    let benchmarks = discover_cnf_benchmarks(&benchmark_dir);
    if benchmarks.is_empty() {
        eprintln!(
            "SKIP: no .cnf benchmarks found under {}",
            benchmark_dir.display()
        );
        return;
    }

    let cadical_path = root.join("reference/cadical/build/cadical");
    let cadical_available = cadical_path.is_file();

    let mut failures = Vec::new();
    let mut sat_verified = 0usize;
    let mut unsat_verified = 0usize;
    let mut proof_verified = 0usize;
    let mut ay_timeouts = 0usize;
    let mut cadical_compared = 0usize;
    let mut cadical_skipped = 0usize;

    for path in &benchmarks {
        let label = benchmark_label(&root, path);
        let dimacs = match std::fs::read_to_string(path) {
            Ok(dimacs) => dimacs,
            Err(e) => {
                failures.push(format!("{label}: failed to read benchmark: {e}"));
                continue;
            }
        };

        let formula = match parse_dimacs(&dimacs) {
            Ok(formula) => formula,
            Err(e) => {
                failures.push(format!("{label}: DIMACS parse failed: {e}"));
                continue;
            }
        };
        let original_clauses = formula.clauses.clone();
        let run = run_ay_with_drat(formula.num_vars, &original_clauses);

        let cadical_result = if cadical_available {
            run_cadical(&cadical_path, path)
        } else {
            OracleResult::Unavailable
        };

        match &run.result {
            SatResult::Sat(model) => {
                super::common::assert_model_satisfies(&original_clauses, model, &label);
                sat_verified += 1;
            }
            SatResult::Unsat(_) => {
                let Some(ref proof_bytes) = run.proof_bytes else {
                    failures.push(format!(
                        "{label}: UNSAT result did not preserve a DRAT proof"
                    ));
                    continue;
                };
                verify_drat_proof(&dimacs, proof_bytes, &label);
                unsat_verified += 1;
                proof_verified += 1;
            }
            SatResult::Unknown => {
                if run.elapsed >= BENCHMARK_TIMEOUT {
                    ay_timeouts += 1;
                    eprintln!("SKIP {label}: AY timed out after {BENCHMARK_TIMEOUT:?}");
                    continue;
                }
                failures.push(format!(
                    "{label}: AY returned Unknown before timeout (elapsed {:?})",
                    run.elapsed
                ));
                continue;
            }
            _ => unreachable!(),
        }

        match (&run.result, cadical_result) {
            (SatResult::Sat(_), OracleResult::Sat) | (SatResult::Unsat(_), OracleResult::Unsat) => {
                cadical_compared += 1;
            }
            (SatResult::Sat(_), OracleResult::Unsat) | (SatResult::Unsat(_), OracleResult::Sat) => {
                failures.push(format!(
                    "{label}: disagreement with CaDiCaL (AY={:?}, CaDiCaL={cadical_result:?})",
                    run.result
                ));
            }
            (_, OracleResult::Unknown) | (_, OracleResult::Unavailable) => {
                cadical_skipped += 1;
            }
            (_, OracleResult::Sat) | (_, OracleResult::Unsat) => {
                failures.push(format!(
                    "{label}: unexpected AY result variant during CaDiCaL comparison: {:?}",
                    run.result
                ));
            }
        }
    }

    eprintln!(
        "SATCOMP soundness regression: total={} sat_verified={} unsat_verified={} \
         proof_verified={} ay_timeouts={} cadical_compared={} cadical_skipped={}",
        benchmarks.len(),
        sat_verified,
        unsat_verified,
        proof_verified,
        ay_timeouts,
        cadical_compared,
        cadical_skipped
    );

    assert!(
        sat_verified + unsat_verified > 0,
        "Expected at least one SATCOMP benchmark to complete within the 30s budget"
    );
    assert!(
        failures.is_empty(),
        "SATCOMP soundness regression failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
