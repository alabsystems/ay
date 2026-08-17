// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Comprehensive SAT soundness regression suite (Part of #7904).
//!
//! This test file strengthens the soundness regression suite beyond what
//! `soundness_circuit_equiv.rs` and `soundness_regression.rs` provide.
//!
//! Coverage:
//! - Programmatically generated pigeonhole principle PHP(n+1,n) instances (UNSAT)
//! - Random 3-SAT instances near the phase transition (ratio ~4.267)
//! - Graph coloring instances on complete graphs (UNSAT)
//! - All existing `benchmarks/sat/unsat/` files with UNSAT verification
//! - Known-SAT benchmarks with model verification against original clauses
//! - Cross-configuration differential testing (default vs no-inprocessing)
//!
//! Every SAT result is verified by checking the model against the original
//! clauses. Every UNSAT result on a known-UNSAT instance is confirmed not-SAT.

#![allow(clippy::panic, unused_must_use)]

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_sat::{Literal, ProofOutput, SatResult, Solver, Variable};
use std::time::Instant;

// ---------------------------------------------------------------------------
// SplitMix64 PRNG for deterministic formula generation
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    fn next_bounded(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }
}

// ---------------------------------------------------------------------------
// Model verification
// ---------------------------------------------------------------------------

/// Verify that a model satisfies all clauses. Returns the index of the first
/// violated clause, or `None` if all clauses are satisfied.
fn find_violated_clause(clauses: &[Vec<Literal>], model: &[bool]) -> Option<usize> {
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
        if !satisfied {
            return Some(ci);
        }
    }
    None
}

/// Verify a DRAT proof using the native ay-drat-check forward checker.
/// Panics if the proof is empty, fails to parse, or fails verification.
fn verify_drat_proof_native(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    proof_bytes: &[u8],
    label: &str,
) {
    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let dimacs = super::common::clauses_to_dimacs(num_vars, clauses);
    let cnf_for_check = parse_cnf(dimacs.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });
}

/// Solve and verify: SAT models must satisfy all clauses, UNSAT results
/// produce and verify a DRAT proof via the native forward checker.
fn solve_and_verify(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>, // Some(true)=SAT, Some(false)=UNSAT, None=unknown
) -> SatResult {
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            if let Some(ci) = find_violated_clause(clauses, model) {
                panic!(
                    "SOUNDNESS BUG: [{label}] SAT model violates clause {ci} \
                     (clause: {:?}, model len: {})",
                    clauses[ci],
                    model.len()
                );
            }
            assert!(
                expected != Some(false),
                "SOUNDNESS BUG: [{label}] solver returned SAT on a known-UNSAT instance"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected != Some(true),
                "SOUNDNESS BUG: [{label}] solver returned UNSAT on a known-SAT instance"
            );
            // Verify the DRAT proof for every UNSAT result.
            let writer = solver
                .take_proof_writer()
                .expect("proof writer must exist after UNSAT solve");
            let proof_bytes = writer.into_vec().expect("proof writer flush");
            verify_drat_proof_native(num_vars, clauses, &proof_bytes, label);
        }
        SatResult::Unknown => {
            // Timeout is acceptable for hard instances.
        }
        _ => unreachable!(),
    }

    result
}

/// Solve with a timeout. Returns the result. UNSAT results have their DRAT
/// proof verified by the native forward checker.
fn solve_and_verify_with_timeout(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
    timeout_secs: u64,
) -> SatResult {
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    let started = Instant::now();
    let timeout = std::time::Duration::from_secs(timeout_secs);
    let result = solver
        .solve_interruptible(|| started.elapsed() >= timeout)
        .into_inner();

    match &result {
        SatResult::Sat(model) => {
            if let Some(ci) = find_violated_clause(clauses, model) {
                panic!(
                    "SOUNDNESS BUG: [{label}] SAT model violates clause {ci} \
                     (clause: {:?}, model len: {})",
                    clauses[ci],
                    model.len()
                );
            }
            assert!(
                expected != Some(false),
                "SOUNDNESS BUG: [{label}] solver returned SAT on a known-UNSAT instance"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected != Some(true),
                "SOUNDNESS BUG: [{label}] solver returned UNSAT on a known-SAT instance"
            );
            // Verify the DRAT proof for every UNSAT result.
            let writer = solver
                .take_proof_writer()
                .expect("proof writer must exist after UNSAT solve");
            let proof_bytes = writer.into_vec().expect("proof writer flush");
            verify_drat_proof_native(num_vars, clauses, &proof_bytes, label);
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }

    result
}

/// Solve with all inprocessing disabled and verify.
fn solve_no_inprocessing_and_verify(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
) -> SatResult {
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            if let Some(ci) = find_violated_clause(clauses, model) {
                panic!("SOUNDNESS BUG: [{label}][no-inproc] SAT model violates clause {ci}");
            }
            assert!(
                expected != Some(false),
                "SOUNDNESS BUG: [{label}][no-inproc] returned SAT on known-UNSAT"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected != Some(true),
                "SOUNDNESS BUG: [{label}][no-inproc] returned UNSAT on known-SAT"
            );
            // Verify the DRAT proof for every UNSAT result.
            let writer = solver
                .take_proof_writer()
                .expect("proof writer must exist after UNSAT solve");
            let proof_bytes = writer.into_vec().expect("proof writer flush");
            verify_drat_proof_native(num_vars, clauses, &proof_bytes, label);
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }

    result
}

// ---------------------------------------------------------------------------
// Formula generators
// ---------------------------------------------------------------------------

/// Generate pigeonhole principle PHP(pigeons, holes).
/// This encodes "pigeons pigeons into holes holes" which is UNSAT when
/// pigeons > holes.
///
/// Variables: x_{p,h} = pigeon p is in hole h (1-indexed, var = p*holes + h)
/// Clauses:
///   1. Each pigeon must be in at least one hole: OR_h x_{p,h}
///   2. No two pigeons in the same hole: NOT(x_{p1,h} AND x_{p2,h})
fn generate_php(pigeons: usize, holes: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = pigeons * holes;
    let mut clauses = Vec::new();

    // Variable index for pigeon p in hole h (0-indexed)
    let var = |p: usize, h: usize| -> Variable { Variable::new((p * holes + h) as u32) };

    // At-least-one: each pigeon must be in some hole
    for p in 0..pigeons {
        let clause: Vec<Literal> = (0..holes).map(|h| Literal::positive(var(p, h))).collect();
        clauses.push(clause);
    }

    // At-most-one: no two pigeons in the same hole
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(var(p1, h)),
                    Literal::negative(var(p2, h)),
                ]);
            }
        }
    }

    (num_vars, clauses)
}

/// Generate a graph coloring instance: can we color a complete graph K_n with
/// k colors? This is UNSAT when k < n.
///
/// Variables: c_{v,color} = vertex v has color c
/// Clauses:
///   1. Each vertex has at least one color
///   2. No vertex has two colors (optional, makes it harder)
///   3. Adjacent vertices have different colors
fn generate_graph_coloring_complete(n: usize, k: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n * k;
    let mut clauses = Vec::new();

    let var = |v: usize, c: usize| -> Variable { Variable::new((v * k + c) as u32) };

    // Each vertex has at least one color
    for v in 0..n {
        let clause: Vec<Literal> = (0..k).map(|c| Literal::positive(var(v, c))).collect();
        clauses.push(clause);
    }

    // Each vertex has at most one color (AMO)
    for v in 0..n {
        for c1 in 0..k {
            for c2 in (c1 + 1)..k {
                clauses.push(vec![
                    Literal::negative(var(v, c1)),
                    Literal::negative(var(v, c2)),
                ]);
            }
        }
    }

    // Adjacent vertices have different colors (complete graph: all pairs)
    for v1 in 0..n {
        for v2 in (v1 + 1)..n {
            for c in 0..k {
                clauses.push(vec![
                    Literal::negative(var(v1, c)),
                    Literal::negative(var(v2, c)),
                ]);
            }
        }
    }

    (num_vars, clauses)
}

/// Generate a random 3-SAT instance with `num_vars` variables and
/// `num_clauses` clauses. Each clause has exactly 3 distinct variables.
fn generate_random_3sat(
    rng: &mut Rng,
    num_vars: u32,
    num_clauses: usize,
) -> (usize, Vec<Vec<Literal>>) {
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let mut vars_in_clause = Vec::with_capacity(3);
        while vars_in_clause.len() < 3 {
            let v = rng.next_bounded(u64::from(num_vars)) as u32;
            if !vars_in_clause.contains(&v) {
                vars_in_clause.push(v);
            }
        }
        let clause: Vec<Literal> = vars_in_clause
            .iter()
            .map(|&v| {
                if rng.next_bounded(2) == 0 {
                    Literal::positive(Variable::new(v))
                } else {
                    Literal::negative(Variable::new(v))
                }
            })
            .collect();
        clauses.push(clause);
    }
    (num_vars as usize, clauses)
}

/// Generate a simple satisfiable formula: unit clauses that force specific
/// assignments, plus random clauses that are consistent with those assignments.
fn generate_forced_sat(rng: &mut Rng, num_vars: u32) -> (usize, Vec<Vec<Literal>>, Vec<bool>) {
    // Generate a random assignment
    let mut assignment = vec![false; num_vars as usize];
    for val in assignment.iter_mut() {
        *val = rng.next_bounded(2) == 0;
    }

    let mut clauses = Vec::new();

    // Add unit clauses for the first few variables to force the assignment
    let forced = (num_vars / 3).max(1);
    for v in 0..forced {
        let lit = if assignment[v as usize] {
            Literal::positive(Variable::new(v))
        } else {
            Literal::negative(Variable::new(v))
        };
        clauses.push(vec![lit]);
    }

    // Add random clauses that are satisfied by the assignment
    let num_random = num_vars as usize * 2;
    for _ in 0..num_random {
        let clause_len = (rng.next_bounded(3) + 2) as usize; // 2-4 literals
        let mut clause = Vec::with_capacity(clause_len);
        let mut used_vars = Vec::new();

        // Ensure at least one literal is satisfied
        let sat_var = rng.next_bounded(u64::from(num_vars)) as u32;
        let sat_lit = if assignment[sat_var as usize] {
            Literal::positive(Variable::new(sat_var))
        } else {
            Literal::negative(Variable::new(sat_var))
        };
        clause.push(sat_lit);
        used_vars.push(sat_var);

        // Add remaining literals (may or may not be satisfied)
        while clause.len() < clause_len {
            let v = rng.next_bounded(u64::from(num_vars)) as u32;
            if !used_vars.contains(&v) {
                let positive = rng.next_bounded(2) == 0;
                clause.push(if positive {
                    Literal::positive(Variable::new(v))
                } else {
                    Literal::negative(Variable::new(v))
                });
                used_vars.push(v);
            }
        }
        clauses.push(clause);
    }

    (num_vars as usize, clauses, assignment)
}

/// Generate an ordering/transitivity constraint that is UNSAT.
/// Encodes: x_01 < x_12 < x_23 < ... < x_{n-1,0} (cyclic, which is impossible).
fn generate_ordering_cycle(n: usize) -> (usize, Vec<Vec<Literal>>) {
    // Variable x_ij means i < j. We need n*(n-1)/2 variables for all pairs.
    // For simplicity, use n variables for the chain: x_01, x_12, ..., x_{n-1,0}
    let num_vars = n;
    let mut clauses = Vec::new();

    // Assert x_i for all i (each ordering holds)
    for i in 0..n {
        clauses.push(vec![Literal::positive(Variable::new(i as u32))]);
    }

    // Transitivity: if x_01 and x_12 then x_02, etc.
    // But x_{n-1,0} contradicts the cycle, so add:
    // NOT(x_01 AND x_12 AND ... AND x_{n-1,0})
    // = at least one must be false
    let neg_all: Vec<Literal> = (0..n)
        .map(|i| Literal::negative(Variable::new(i as u32)))
        .collect();
    clauses.push(neg_all);

    // This is UNSAT because: all unit clauses force all vars true,
    // but the last clause requires at least one false.

    (num_vars, clauses)
}

// ---------------------------------------------------------------------------
// Classify result
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn classify(result: &SatResult) -> Verdict {
    match result {
        SatResult::Sat(_) => Verdict::Sat,
        SatResult::Unsat(_) => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}

include!("soundness_comprehensive/generated_formula_suites.rs");

include!("soundness_comprehensive/benchmark_and_differential_suites.rs");

fn collect_cnf_files(dir: &std::path::Path, results: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cnf_files(&path, results);
        } else if path.extension().is_some_and(|ext| ext == "cnf") {
            results.push(path);
        }
    }
}
