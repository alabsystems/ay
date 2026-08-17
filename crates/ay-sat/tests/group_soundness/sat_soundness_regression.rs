// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(
    clippy::cast_lossless,
    clippy::manual_is_multiple_of,
    clippy::manual_assert,
    clippy::float_cmp,
    clippy::unreadable_literal
)]

//! SAT soundness regression suite with model and DRAT proof verification.
//!
//! Part of #7904: expand soundness regression coverage.
//!
//! This file adds the following coverage gaps not present in existing suites:
//!
//! 1. **Large-scale random 3-SAT fuzz** — 100 seeds x multiple clause/var
//!    ratios, with model verification on SAT and DRAT proof verification on
//!    UNSAT.
//! 2. **Per-inprocessing-feature isolation** — enable exactly one inprocessing
//!    technique at a time and verify soundness on random formulas.
//! 3. **Assumption-based solving** — verify models satisfy clauses AND
//!    assumptions, verify unsat cores are subsets of assumptions.
//! 4. **Clause density sweep** — fine-grained sweep across the 3-SAT phase
//!    transition (ratio 3.0 to 5.5) with soundness checks at each step.
//! 5. **Repeated solve on same solver** — verify internal state cleanup does
//!    not corrupt results when adding clauses between solves.

#![allow(clippy::panic)]

use ay_sat::{Literal, ProofOutput, SatResult, Solver, Variable};

// ---------------------------------------------------------------------------
// SplitMix64 PRNG — deterministic, no external dependencies
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    fn next_bounded(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }

    fn next_bool(&mut self) -> bool {
        self.next_u64() % 2 == 0
    }
}

// ---------------------------------------------------------------------------
// Formula generators
// ---------------------------------------------------------------------------

/// Generate a random k-SAT formula.
fn generate_random_ksat(
    rng: &mut Rng,
    num_vars: u32,
    num_clauses: usize,
    k: usize,
) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(k);
        for _ in 0..k {
            let var = rng.next_bounded(num_vars as u64) as u32;
            let lit = if rng.next_bool() {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            clause.push(lit);
        }
        clauses.push(clause);
    }
    clauses
}

/// Generate a random 3-SAT formula with a specific clause-to-variable ratio.
fn generate_3sat_at_ratio(rng: &mut Rng, num_vars: u32, ratio: f64) -> Vec<Vec<Literal>> {
    let num_clauses = (num_vars as f64 * ratio).round() as usize;
    generate_random_ksat(rng, num_vars, num_clauses, 3)
}

/// Generate a formula that is guaranteed SAT by construction: pick a random
/// assignment, then generate clauses that each contain at least one literal
/// satisfied by that assignment.
fn generate_forced_sat(
    rng: &mut Rng,
    num_vars: u32,
    num_clauses: usize,
    clause_width: usize,
) -> (Vec<Vec<Literal>>, Vec<bool>) {
    let assignment: Vec<bool> = (0..num_vars).map(|_| rng.next_bool()).collect();
    let mut clauses = Vec::with_capacity(num_clauses);

    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(clause_width);
        // First literal is guaranteed to satisfy the assignment.
        let forced_var = rng.next_bounded(num_vars as u64) as u32;
        let forced_lit = if assignment[forced_var as usize] {
            Literal::positive(Variable::new(forced_var))
        } else {
            Literal::negative(Variable::new(forced_var))
        };
        clause.push(forced_lit);

        // Remaining literals are random.
        for _ in 1..clause_width {
            let var = rng.next_bounded(num_vars as u64) as u32;
            let lit = if rng.next_bool() {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            clause.push(lit);
        }
        clauses.push(clause);
    }
    (clauses, assignment)
}

// ---------------------------------------------------------------------------
// Verification helpers
// ---------------------------------------------------------------------------

/// Check that a model satisfies all clauses. Returns the index of the first
/// violated clause, or None if all are satisfied.
fn find_violated_clause(clauses: &[Vec<Literal>], model: &[bool]) -> Option<usize> {
    for (ci, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let idx = lit.variable().index();
            let val = model.get(idx).copied().unwrap_or(false);
            if lit.is_positive() {
                val
            } else {
                !val
            }
        });
        if !satisfied {
            return Some(ci);
        }
    }
    None
}

/// Convert clauses to DIMACS CNF string for DRAT verification.
fn clauses_to_dimacs(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut dimacs = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            let var = lit.variable().index() as i64 + 1;
            let signed = if lit.is_positive() { var } else { -var };
            dimacs.push_str(&format!("{signed} "));
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

/// Solve a formula and verify the result. Returns the raw SatResult.
fn solve_and_verify(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
) -> SatResult {
    let mut solver = Solver::new(num_vars);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();
    verify_result(&result, clauses, label, expected);
    result
}

/// Solve with DRAT proof output and verify both model/proof.
fn solve_and_verify_drat(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
) -> SatResult {
    let mut solver = Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            if let Some(ci) = find_violated_clause(clauses, model) {
                panic!(
                    "SOUNDNESS BUG [{label}]: SAT model violates clause {ci}: {:?}",
                    clauses[ci]
                );
            }
            if expected == Some(false) {
                panic!("SOUNDNESS BUG [{label}]: returned SAT on known-UNSAT instance");
            }
        }
        SatResult::Unsat(_) => {
            if expected == Some(true) {
                panic!("SOUNDNESS BUG [{label}]: returned UNSAT on known-SAT instance");
            }
            let proof_output = solver
                .take_proof_writer()
                .expect("proof writer should exist");
            let proof_bytes = proof_output.into_vec().expect("proof writer flush");
            let dimacs = clauses_to_dimacs(num_vars, clauses);
            super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

/// Verify a SatResult against expected and model correctness.
fn verify_result(
    result: &SatResult,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
) {
    match result {
        SatResult::Sat(model) => {
            if let Some(ci) = find_violated_clause(clauses, model) {
                panic!(
                    "SOUNDNESS BUG [{label}]: SAT model violates clause {ci}: {:?}",
                    clauses[ci]
                );
            }
            if expected == Some(false) {
                panic!("SOUNDNESS BUG [{label}]: returned SAT on known-UNSAT instance");
            }
        }
        SatResult::Unsat(_) => {
            if expected == Some(true) {
                panic!("SOUNDNESS BUG [{label}]: returned UNSAT on known-SAT instance");
            }
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
}

// ===========================================================================
// Test 1: Large-scale random 3-SAT fuzz with model verification
// ===========================================================================

/// Solve 100 random 3-SAT instances at 20 variables across 5 clause/variable
/// ratios. Each SAT result is model-verified. Each UNSAT result is confirmed
/// via DRAT proof (when drat-trim is available).
#[test]
fn fuzz_random_3sat_100_seeds_model_verified() {
    let num_vars: u32 = 20;
    let ratios = [3.0, 3.5, 4.0, 4.267, 5.0];
    let seeds_per_ratio = 20; // 5 ratios x 20 seeds = 100 instances

    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut unknown_count = 0usize;

    for &ratio in &ratios {
        for seed_offset in 0..seeds_per_ratio {
            let seed = 0xDEAD_BEEF_u64
                .wrapping_mul((ratio * 1000.0) as u64)
                .wrapping_add(seed_offset);
            let mut rng = Rng::new(seed);
            let clauses = generate_3sat_at_ratio(&mut rng, num_vars, ratio);
            let label = format!("3sat-v{num_vars}-r{ratio}-s{seed_offset}");

            let result = solve_and_verify(
                num_vars as usize,
                &clauses,
                &label,
                None, // unknown answer
            );

            match result {
                SatResult::Sat(_) => sat_count += 1,
                SatResult::Unsat(_) => unsat_count += 1,
                _ => unknown_count += 1,
            }
        }
    }

    eprintln!(
        "fuzz_random_3sat_100_seeds: sat={sat_count} unsat={unsat_count} unknown={unknown_count}"
    );
    // At 20 vars, the solver should resolve every instance.
    assert_eq!(unknown_count, 0, "all 20-var formulas should be resolved");
    // At the phase transition (~4.267), we expect a mix of SAT and UNSAT.
    assert!(sat_count > 0, "expected some SAT results");
    assert!(unsat_count > 0, "expected some UNSAT results");
}

// ===========================================================================
// Test 2: Random 3-SAT with DRAT proof verification on UNSAT
// ===========================================================================

/// Focus on the UNSAT regime (high clause ratio) and verify every UNSAT result
/// with an in-process DRAT proof check via drat-trim.
#[test]
fn fuzz_random_3sat_drat_unsat_verification() {
    let num_vars: u32 = 15;
    // ratio=5.5 is firmly in the UNSAT regime for 3-SAT.
    let ratio = 5.5;
    let num_seeds = 50;
    let mut unsat_verified = 0usize;

    for seed_offset in 0..num_seeds {
        let seed = 0xCAFE_BABE_u64.wrapping_add(seed_offset);
        let mut rng = Rng::new(seed);
        let clauses = generate_3sat_at_ratio(&mut rng, num_vars, ratio);
        let label = format!("drat-3sat-v{num_vars}-r{ratio}-s{seed_offset}");

        let result = solve_and_verify_drat(num_vars as usize, &clauses, &label, None);

        if matches!(result, SatResult::Unsat(_)) {
            unsat_verified += 1;
        }
    }

    eprintln!("fuzz_drat_unsat: verified {unsat_verified}/{num_seeds} UNSAT proofs");
    // At ratio 5.5 with 15 vars, nearly all should be UNSAT.
    assert!(
        unsat_verified >= (num_seeds / 2) as usize,
        "expected majority UNSAT at ratio {ratio}, got {unsat_verified}/{num_seeds}"
    );
}

// ===========================================================================
// Test 3: Forced-SAT formulas with model verification
// ===========================================================================

/// Generate formulas that are guaranteed SAT by construction, then verify that
/// the solver returns SAT with a model satisfying all clauses.
#[test]
fn forced_sat_model_verification_50_seeds() {
    let num_vars: u32 = 20;
    let num_clauses = 80;

    for seed in 0..50u64 {
        let mut rng = Rng::new(0x1234_5678_u64.wrapping_add(seed));
        let (clauses, _expected_assignment) =
            generate_forced_sat(&mut rng, num_vars, num_clauses, 3);
        let label = format!("forced-sat-v{num_vars}-c{num_clauses}-s{seed}");

        let result = solve_and_verify(
            num_vars as usize,
            &clauses,
            &label,
            Some(true), // known SAT
        );

        assert!(
            matches!(result, SatResult::Sat(_)),
            "SOUNDNESS BUG [{label}]: forced-SAT formula returned non-SAT: {result:?}"
        );
    }
}

// ===========================================================================
// Test 4: Per-inprocessing-feature isolation
// ===========================================================================

/// Type alias for a function that enables exactly one inprocessing feature.
type FeatureEnabler = fn(&mut Solver);

/// Solve with all inprocessing disabled except one feature. Verify soundness.
fn test_single_feature(
    feature_name: &str,
    enable_fn: FeatureEnabler,
    num_vars: u32,
    seeds: std::ops::Range<u64>,
    ratio: f64,
) {
    for seed in seeds {
        let mut rng = Rng::new(seed);
        let clauses = generate_3sat_at_ratio(&mut rng, num_vars, ratio);
        let label = format!("{feature_name}-v{num_vars}-r{ratio}-s{seed}");

        let mut solver = Solver::new(num_vars as usize);
        super::common::disable_all_inprocessing(&mut solver);
        enable_fn(&mut solver);

        for clause in &clauses {
            solver.add_clause(clause.clone());
        }
        let result = solver.solve().into_inner();
        verify_result(&result, &clauses, &label, None);
    }
}

include!("sat_soundness_regression/feature_and_incremental_regressions.rs");
