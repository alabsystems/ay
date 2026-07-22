// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof verification sweep for ALL known-UNSAT benchmark files (Part of #7904).
//!
//! Every UNSAT benchmark in the repo must have its proof verified by
//! drat-trim, under both default and no-inprocessing configurations.
//!
//! Coverage:
//! - All `benchmarks/sat/unsat/*.cnf` files (27 benchmarks)
//! - All `benchmarks/sat/eq_atree_braun/*.cnf` files (7 benchmarks)
//!
//! SAT on a known-UNSAT benchmark is a soundness bug (immediate panic).
//! Timeouts are tracked and reported but do not fail the test (hard
//! benchmarks like braun.11+ may exceed the per-benchmark budget).

#![allow(clippy::panic)]

use ay_sat::{Literal, ProofOutput, SatResult, Solver, Variable};
use std::fs;
use std::time::{Duration, Instant};

/// Outcome of a single DRAT-verified solve attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DratOutcome {
    Verified,
    Timeout,
}

fn max_variable(clauses: &[Vec<Literal>]) -> Option<Variable> {
    clauses
        .iter()
        .flat_map(|clause| clause.iter().map(|lit| lit.variable()))
        .max_by_key(|var| var.index())
}

fn discover_benchmarks(relative_dir: &str) -> Vec<String> {
    let root = super::common::workspace_root();
    let dir = root.join(relative_dir);
    let mut paths = Vec::new();

    for entry in fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("failed to read benchmark directory {}: {e}", dir.display()))
    {
        let entry =
            entry.unwrap_or_else(|e| panic!("failed to read entry in {}: {e}", dir.display()));
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "cnf") {
            let relative = path
                .strip_prefix(&root)
                .expect("benchmark path must live under workspace root")
                .to_string_lossy()
                .replace('\\', "/");
            paths.push(relative);
        }
    }

    paths.sort();
    assert!(
        !paths.is_empty(),
        "no .cnf benchmarks found in {}",
        dir.display()
    );
    paths
}

/// Solve a known-UNSAT formula with DRAT proof output and verify the proof.
///
/// Returns `DratOutcome::Verified` if UNSAT + DRAT proof verified,
/// `DratOutcome::Timeout` if the solver timed out.
/// Panics on SAT (soundness bug).
fn solve_unsat_with_drat_proof(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    timeout_secs: u64,
    configure: impl FnOnce(&mut Solver),
) -> DratOutcome {
    if let Some(max_var) = max_variable(clauses) {
        assert!(
            max_var.index() < num_vars,
            "{label}: variable {} exceeds DIMACS header {}",
            max_var.index() + 1,
            num_vars,
        );
    }

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    configure(&mut solver);

    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    let started = Instant::now();
    let timeout = Duration::from_secs(timeout_secs);
    let result = solver
        .solve_interruptible(|| started.elapsed() >= timeout)
        .into_inner();

    match result {
        SatResult::Unsat(_) => {
            let writer = solver.take_proof_writer().expect("proof writer");
            let proof_bytes = writer.into_vec().expect("proof flush");
            assert!(!proof_bytes.is_empty(), "{label}: DRAT proof is empty");

            let dimacs = super::common::clauses_to_dimacs(num_vars, clauses);
            super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
            DratOutcome::Verified
        }
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {label} returned SAT on a known-UNSAT benchmark");
        }
        SatResult::Unknown => {
            eprintln!("{label}: timed out after {timeout_secs}s (not a soundness bug)");
            DratOutcome::Timeout
        }
        _ => unreachable!(),
    }
}

/// Sweep all .cnf files in a benchmark directory with DRAT verification.
///
/// Each benchmark is tested under two configurations:
/// 1. Default (all inprocessing enabled)
/// 2. No inprocessing (baseline CDCL only)
///
/// Returns (verified_count, timeout_count).
fn sweep_benchmarks(relative_dir: &str, suite_name: &str, timeout_secs: u64) -> (usize, usize) {
    let mut verified = 0usize;
    let mut timeouts = 0usize;

    for path in discover_benchmarks(relative_dir) {
        let label = path.rsplit('/').next().unwrap_or(path.as_str());
        let cnf = super::common::load_repo_benchmark(&path);
        let formula =
            ay_sat::parse_dimacs(&cnf).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

        // Default configuration
        match solve_unsat_with_drat_proof(
            formula.num_vars,
            &formula.clauses,
            &format!("{suite_name}:{label}:default"),
            timeout_secs,
            |_| {},
        ) {
            DratOutcome::Verified => verified += 1,
            DratOutcome::Timeout => timeouts += 1,
        }

        // No-inprocessing configuration
        match solve_unsat_with_drat_proof(
            formula.num_vars,
            &formula.clauses,
            &format!("{suite_name}:{label}:no-inproc"),
            timeout_secs,
            |solver| {
                super::common::disable_all_inprocessing(solver);
                solver.set_preprocess_enabled(false);
            },
        ) {
            DratOutcome::Verified => verified += 1,
            DratOutcome::Timeout => timeouts += 1,
        }
    }

    (verified, timeouts)
}

/// Sweep all benchmarks/sat/unsat/*.cnf with DRAT proof verification.
///
/// These are small UNSAT benchmarks (PHP, Tseitin, graph coloring, etc.)
/// that should all solve within 30 seconds. At least 40 of 54 runs
/// (27 files x 2 configs) must produce verified DRAT proofs.
#[test]
fn unsat_corpus_drat_sweep() {
    let (verified, timeouts) = sweep_benchmarks("benchmarks/sat/unsat", "unsat", 30);
    eprintln!("unsat_corpus_drat_sweep: {verified} verified, {timeouts} timeouts");
    assert!(
        verified >= 40,
        "expected at least 40 DRAT-verified runs from unsat corpus, got {verified}"
    );
}

/// Sweep all benchmarks/sat/eq_atree_braun/*.cnf with DRAT proof verification.
///
/// The braun circuit equivalence benchmarks range from easy (braun.8) to
/// very hard (braun.13). Timeouts are expected for the larger instances.
/// At least 2 benchmarks (braun.8 and braun.10, the two ay solves) must
/// produce verified DRAT proofs under at least one config.
#[test]
fn eq_atree_braun_drat_sweep() {
    let (verified, timeouts) =
        sweep_benchmarks("benchmarks/sat/eq_atree_braun", "eq_atree_braun", 30);
    eprintln!("eq_atree_braun_drat_sweep: {verified} verified, {timeouts} timeouts");
    assert!(
        verified >= 2,
        "expected at least 2 DRAT-verified runs from eq_atree_braun, got {verified}"
    );
}

// ===========================================================================
// SAT model verification sweep
// ===========================================================================

/// Verify that a model satisfies all original clauses.
fn verify_model_against_clauses(clauses: &[Vec<Literal>], model: &[bool], label: &str) {
    for (ci, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let var_idx = lit.variable().index();
            let val = model.get(var_idx).copied().unwrap_or(false);
            if lit.is_positive() {
                val
            } else {
                !val
            }
        });
        assert!(
            satisfied,
            "SOUNDNESS BUG: [{label}] SAT model violates clause {ci}: {clause:?}"
        );
    }
}

/// Solve a formula and verify SAT models against original clauses.
/// For UNSAT results on known-UNSAT instances, verify DRAT proof.
/// Returns (sat_verified, unsat_drat_verified, timeouts).
fn solve_and_verify_bidirectional(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected_unsat: bool,
    timeout_secs: u64,
    configure: impl FnOnce(&mut Solver),
) -> (usize, usize, usize) {
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    configure(&mut solver);

    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    let started = Instant::now();
    let timeout = Duration::from_secs(timeout_secs);
    let result = solver
        .solve_interruptible(|| started.elapsed() >= timeout)
        .into_inner();

    match result {
        SatResult::Sat(ref model) => {
            assert!(
                !expected_unsat,
                "SOUNDNESS BUG: {label} returned SAT on a known-UNSAT benchmark"
            );
            verify_model_against_clauses(clauses, model, label);
            (1, 0, 0)
        }
        SatResult::Unsat(_) => {
            let writer = solver.take_proof_writer().expect("proof writer");
            let proof_bytes = writer.into_vec().expect("proof flush");
            assert!(!proof_bytes.is_empty(), "{label}: DRAT proof is empty");
            let dimacs = super::common::clauses_to_dimacs(num_vars, clauses);
            super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
            (0, 1, 0)
        }
        SatResult::Unknown => {
            eprintln!("{label}: timed out after {timeout_secs}s");
            (0, 0, 1)
        }
        _ => unreachable!(),
    }
}

/// Bidirectional soundness sweep over the small UNSAT corpus.
///
/// For every benchmarks/sat/unsat/*.cnf file:
/// - SAT results (unexpected): model verified against all original clauses
/// - UNSAT results: DRAT proof generated and verified by drat-trim
///
/// This complements `unsat_corpus_drat_sweep` by also verifying SAT models
/// if any benchmark unexpectedly returns SAT. Both directions are verified
/// by independent means (model checking and proof checking).
#[test]
fn unsat_corpus_bidirectional_sweep() {
    let mut sat_verified = 0usize;
    let mut unsat_drat_verified = 0usize;
    let mut timeouts = 0usize;

    for path in discover_benchmarks("benchmarks/sat/unsat") {
        let label = path.rsplit('/').next().unwrap_or(path.as_str());
        let cnf = super::common::load_repo_benchmark(&path);
        let formula =
            ay_sat::parse_dimacs(&cnf).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

        let (s, u, t) = solve_and_verify_bidirectional(
            formula.num_vars,
            &formula.clauses,
            &format!("bidir:{label}"),
            true, // known UNSAT
            30,
            |_| {},
        );
        sat_verified += s;
        unsat_drat_verified += u;
        timeouts += t;
    }

    eprintln!(
        "unsat_corpus bidirectional: {sat_verified} SAT model-verified, \
         {unsat_drat_verified} UNSAT DRAT-verified, {timeouts} timeouts"
    );
    assert!(
        unsat_drat_verified >= 20,
        "expected at least 20 DRAT-verified runs, got {unsat_drat_verified}"
    );
}

/// Per-inprocessing-feature UNSAT DRAT verification.
///
/// For each inprocessing feature, solve a small UNSAT benchmark with ONLY
/// that feature enabled (all others disabled). This catches soundness bugs
/// introduced by individual inprocessing passes -- the exact class of bug
/// that caused the original P0 (#7900).
#[test]
fn per_feature_isolation_drat_sweep() {
    // Features and their enable functions
    let features: Vec<(&str, Box<dyn Fn(&mut Solver)>)> = vec![
        (
            "vivify",
            Box::new(|s: &mut Solver| s.set_vivify_enabled(true)),
        ),
        (
            "subsume",
            Box::new(|s: &mut Solver| s.set_subsume_enabled(true)),
        ),
        (
            "probe",
            Box::new(|s: &mut Solver| s.set_probe_enabled(true)),
        ),
        (
            "shrink",
            Box::new(|s: &mut Solver| s.set_shrink_enabled(true)),
        ),
        ("bve", Box::new(|s: &mut Solver| s.set_bve_enabled(true))),
        ("bce", Box::new(|s: &mut Solver| s.set_bce_enabled(true))),
        (
            "decompose",
            Box::new(|s: &mut Solver| s.set_decompose_enabled(true)),
        ),
        (
            "factor",
            Box::new(|s: &mut Solver| s.set_factor_enabled(true)),
        ),
        (
            "transred",
            Box::new(|s: &mut Solver| s.set_transred_enabled(true)),
        ),
        ("htr", Box::new(|s: &mut Solver| s.set_htr_enabled(true))),
        ("gate", Box::new(|s: &mut Solver| s.set_gate_enabled(true))),
        (
            "congruence",
            Box::new(|s: &mut Solver| s.set_congruence_enabled(true)),
        ),
        (
            "sweep",
            Box::new(|s: &mut Solver| s.set_sweep_enabled(true)),
        ),
        (
            "condition",
            Box::new(|s: &mut Solver| s.set_condition_enabled(true)),
        ),
        (
            "backbone",
            Box::new(|s: &mut Solver| s.set_backbone_enabled(true)),
        ),
        ("cce", Box::new(|s: &mut Solver| s.set_cce_enabled(true))),
    ];

    // Small UNSAT benchmarks that solve quickly
    let benchmarks = [
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/tseitin_grid_3x3.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
    ];

    let mut verified = 0usize;
    let mut timeouts = 0usize;
    let mut errors = Vec::new();

    for (feat_name, enable_fn) in &features {
        for path in &benchmarks {
            let bench_name = path.rsplit('/').next().unwrap_or(path);
            let label = format!("{feat_name}:{bench_name}");
            let cnf = super::common::load_repo_benchmark(path);
            let formula =
                ay_sat::parse_dimacs(&cnf).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                solve_unsat_with_drat_proof(
                    formula.num_vars,
                    &formula.clauses,
                    &label,
                    15,
                    |solver| {
                        // Disable everything first
                        super::common::disable_all_inprocessing(solver);
                        solver.set_preprocess_enabled(false);
                        // Enable only this one feature
                        enable_fn(solver);
                    },
                )
            }));

            match result {
                Ok(DratOutcome::Verified) => verified += 1,
                Ok(DratOutcome::Timeout) => timeouts += 1,
                Err(e) => {
                    let msg = if let Some(s) = e.downcast_ref::<String>() {
                        s.clone()
                    } else if let Some(s) = e.downcast_ref::<&str>() {
                        (*s).to_string()
                    } else {
                        "unknown panic".to_string()
                    };
                    errors.push(format!("{label}: {msg}"));
                }
            }
        }
    }

    eprintln!(
        "per-feature isolation: {verified} verified, {timeouts} timeouts, {} errors \
         (of {} feature x benchmark combos)",
        errors.len(),
        features.len() * benchmarks.len()
    );

    assert!(
        errors.is_empty(),
        "SOUNDNESS BUGS in per-feature isolation:\n{}",
        errors.join("\n")
    );

    // At least half should verify (some features may timeout on harder benchmarks)
    let expected_min = (features.len() * benchmarks.len()) / 2;
    assert!(
        verified >= expected_min,
        "expected at least {expected_min} verified, got {verified}"
    );
}

/// Canary SAT + UNSAT bidirectional check.
///
/// The canary benchmarks are the minimal smoke test. Both must resolve
/// and be verified: SAT via model check, UNSAT via DRAT proof.
#[test]
fn canary_bidirectional_soundness() {
    // SAT canary: model must satisfy all clauses
    let sat_cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_sat.cnf");
    let sat_formula = ay_sat::parse_dimacs(&sat_cnf).expect("parse canary SAT");
    let (s, _, _) = solve_and_verify_bidirectional(
        sat_formula.num_vars,
        &sat_formula.clauses,
        "canary:tiny_sat",
        false,
        10,
        |_| {},
    );
    assert_eq!(s, 1, "canary tiny_sat must return SAT with verified model");

    // UNSAT canary: DRAT proof must verify
    let unsat_cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_unsat.cnf");
    let unsat_formula = ay_sat::parse_dimacs(&unsat_cnf).expect("parse canary UNSAT");
    let (_, u, _) = solve_and_verify_bidirectional(
        unsat_formula.num_vars,
        &unsat_formula.clauses,
        "canary:tiny_unsat",
        true,
        10,
        |_| {},
    );
    assert_eq!(
        u, 1,
        "canary tiny_unsat must return UNSAT with verified DRAT proof"
    );
}
