// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expanded SAT soundness regression suite (Part of #7904).
//!
//! This file extends soundness coverage beyond `soundness_comprehensive.rs`
//! and `soundness_circuit_equiv.rs` with:
//!
//! - Tseitin formula generation (structured UNSAT)
//! - XOR/parity constraint generation (hard for CDCL, catches BVE bugs)
//! - At-most-k / cardinality constraint generation
//! - Latin square constraint generation
//! - DRAT proof verification on generated UNSAT instances
//! - Incremental solve soundness (add clauses between solves)
//! - SAT-to-UNSAT transition (add contradicting unit after SAT)
//! - Multi-seed reproducibility (determinism check)
//! - Crafted corner cases (contradicting units, tautological clauses, etc.)
//! - Larger random 3-SAT (200 variables, near phase transition)
//! - SATCOMP 2022/2023 individual benchmark coverage
//! - Cross-config DRAT proof checks (default vs no-inprocessing)
//!
//! Every SAT result is verified by checking the model against the original
//! clauses. Every UNSAT result on a known-UNSAT instance is confirmed not-SAT.

#![allow(clippy::panic)]
#![allow(unused_must_use)]

use ay_sat::{Literal, ProofOutput, SatResult, Solver, Variable};
use std::time::Instant;

// ---------------------------------------------------------------------------
// SplitMix64 PRNG (same as soundness_comprehensive.rs)
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
// Model verification helpers
// ---------------------------------------------------------------------------

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
                "SOUNDNESS BUG: [{label}] returned SAT on a known-UNSAT instance"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected != Some(true),
                "SOUNDNESS BUG: [{label}] returned UNSAT on a known-SAT instance"
            );
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

fn solve_and_verify_with_timeout(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
    timeout_secs: u64,
) -> SatResult {
    let mut solver = Solver::new(num_vars);
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
                "SOUNDNESS BUG: [{label}] returned SAT on a known-UNSAT instance"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected != Some(true),
                "SOUNDNESS BUG: [{label}] returned UNSAT on a known-SAT instance"
            );
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

fn solve_no_inprocessing_and_verify(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    label: &str,
    expected: Option<bool>,
) -> SatResult {
    let mut solver = Solver::new(num_vars);
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
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

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

include!("soundness_expanded_7904/structured_formula_generators.rs");

// ---------------------------------------------------------------------------
// Formula generators: Random 3-SAT / forced SAT
// ---------------------------------------------------------------------------

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

fn generate_forced_sat(rng: &mut Rng, num_vars: u32) -> (usize, Vec<Vec<Literal>>, Vec<bool>) {
    let mut assignment = vec![false; num_vars as usize];
    for val in assignment.iter_mut() {
        *val = rng.next_bounded(2) == 0;
    }
    let mut clauses = Vec::new();
    let forced = (num_vars / 3).max(1);
    for v in 0..forced {
        let lit = if assignment[v as usize] {
            Literal::positive(Variable::new(v))
        } else {
            Literal::negative(Variable::new(v))
        };
        clauses.push(vec![lit]);
    }
    let num_random = num_vars as usize * 2;
    for _ in 0..num_random {
        let clause_len = (rng.next_bounded(3) + 2) as usize;
        let mut clause = Vec::with_capacity(clause_len);
        let mut used_vars = Vec::new();
        let sat_var = rng.next_bounded(u64::from(num_vars)) as u32;
        let sat_lit = if assignment[sat_var as usize] {
            Literal::positive(Variable::new(sat_var))
        } else {
            Literal::negative(Variable::new(sat_var))
        };
        clause.push(sat_lit);
        used_vars.push(sat_var);
        while clause.len() < clause_len {
            let v = rng.next_bounded(u64::from(num_vars)) as u32;
            if !used_vars.contains(&v) {
                clause.push(if rng.next_bounded(2) == 0 {
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

// ---------------------------------------------------------------------------
// DRAT proof helper
// ---------------------------------------------------------------------------

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
                panic!("SOUNDNESS BUG: [{label}] SAT model violates clause {ci}");
            }
            assert!(
                expected != Some(false),
                "SOUNDNESS BUG: [{label}] returned SAT on known-UNSAT"
            )
        }
        SatResult::Unsat(_) => {
            assert!(
                expected != Some(true),
                "SOUNDNESS BUG: [{label}] returned UNSAT on known-SAT"
            );
            let proof_output = solver
                .take_proof_writer()
                .expect("proof writer should exist");
            let proof_bytes = proof_output.into_vec().expect("proof writer flush");
            let dimacs = super::common::clauses_to_dimacs(num_vars, clauses);
            super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
        }
        SatResult::Unknown => {}
        _ => unreachable!(),
    }
    result
}

include!("soundness_expanded_7904/generated_and_corner_cases.rs");

include!("soundness_expanded_7904/differential_and_benchmark_suites.rs");
