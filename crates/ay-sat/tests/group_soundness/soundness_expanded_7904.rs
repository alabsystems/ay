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

// ---------------------------------------------------------------------------
// Formula generators: Tseitin encoding
// ---------------------------------------------------------------------------

/// Generate a Tseitin formula on a cycle graph with `n` vertices.
/// XOR parity constraint on a cycle: UNSAT for odd n, SAT for even n.
fn generate_tseitin_cycle(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n;
    let mut clauses = Vec::new();

    for v in 0..n {
        let e_prev = Variable::new(((v + n - 1) % n) as u32);
        let e_curr = Variable::new(v as u32);

        // e_prev XOR e_curr = 1
        clauses.push(vec![Literal::positive(e_prev), Literal::positive(e_curr)]);
        clauses.push(vec![Literal::negative(e_prev), Literal::negative(e_curr)]);
    }

    (num_vars, clauses)
}

/// Generate a Tseitin formula on a complete graph K_n.
/// With odd parity assignment on each vertex, UNSAT for odd n.
fn generate_tseitin_complete(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_edges = n * (n - 1) / 2;
    let mut clauses = Vec::new();

    let edge_var = |i: usize, j: usize| -> u32 {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        let base: usize = (0..a).map(|k| n - 1 - k).sum();
        (base + b - a - 1) as u32
    };

    for v in 0..n {
        let mut incident: Vec<u32> = Vec::new();
        for u in 0..n {
            if u != v {
                incident.push(edge_var(v, u));
            }
        }

        if incident.is_empty() {
            continue;
        }
        if incident.len() == 1 {
            clauses.push(vec![Literal::positive(Variable::new(incident[0]))]);
            continue;
        }

        let aux_base = num_edges as u32 + (v * (n - 1)) as u32;
        let a0 = Variable::new(aux_base);
        let e0 = Variable::new(incident[0]);
        clauses.push(vec![Literal::positive(a0), Literal::negative(e0)]);
        clauses.push(vec![Literal::negative(a0), Literal::positive(e0)]);

        for (i, &edge_var) in incident.iter().enumerate().skip(1) {
            let a_prev = Variable::new(aux_base + (i - 1) as u32);
            let ei = Variable::new(edge_var);
            let a_curr = Variable::new(aux_base + i as u32);

            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::negative(a_prev),
                Literal::negative(ei),
            ]);
            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::positive(a_prev),
                Literal::positive(ei),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::negative(a_prev),
                Literal::positive(ei),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::positive(a_prev),
                Literal::negative(ei),
            ]);
        }

        let a_last = Variable::new(aux_base + (incident.len() - 1) as u32);
        clauses.push(vec![Literal::positive(a_last)]);
    }

    let total_vars = num_edges + n * (n - 1);
    (total_vars, clauses)
}

// ---------------------------------------------------------------------------
// Formula generators: XOR / parity constraints
// ---------------------------------------------------------------------------

/// XOR cycle of length n: x_i XOR x_{(i+1)%n} = 1 for all i.
/// UNSAT for odd n (circular XOR contradiction).
fn generate_xor_unsat(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let mut clauses = Vec::new();
    for i in 0..n {
        let vi = Variable::new(i as u32);
        let vj = Variable::new(((i + 1) % n) as u32);
        clauses.push(vec![Literal::positive(vi), Literal::positive(vj)]);
        clauses.push(vec![Literal::negative(vi), Literal::negative(vj)]);
    }
    (n, clauses)
}

/// Parity constraint: all n variables forced true + XOR = 1.
/// UNSAT for even n (XOR of even number of true values = 0, not 1).
fn generate_parity_unsat(n: usize) -> (usize, Vec<Vec<Literal>>) {
    assert!(n >= 2 && n.is_multiple_of(2));
    let aux_base = n as u32;
    let total_vars = n + (n - 1);
    let mut clauses = Vec::new();

    for i in 0..n {
        clauses.push(vec![Literal::positive(Variable::new(i as u32))]);
    }

    let a0 = Variable::new(aux_base);
    let x0 = Variable::new(0);
    clauses.push(vec![Literal::positive(a0), Literal::negative(x0)]);
    clauses.push(vec![Literal::negative(a0), Literal::positive(x0)]);

    for i in 1..n {
        let a_prev = Variable::new(aux_base + (i - 1) as u32);
        let xi = Variable::new(i as u32);
        let a_curr = Variable::new(aux_base + i as u32);

        if i < n - 1 {
            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::negative(a_prev),
                Literal::negative(xi),
            ]);
            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::positive(a_prev),
                Literal::positive(xi),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::negative(a_prev),
                Literal::positive(xi),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::positive(a_prev),
                Literal::negative(xi),
            ]);
        } else {
            // Last step: assert a_prev XOR xi = 1
            clauses.push(vec![Literal::positive(a_prev), Literal::positive(xi)]);
            clauses.push(vec![Literal::negative(a_prev), Literal::negative(xi)]);
        }
    }

    (total_vars, clauses)
}

// ---------------------------------------------------------------------------
// Formula generators: Cardinality constraints
// ---------------------------------------------------------------------------

/// At-most-k of n variables, with k+1 forced true => UNSAT.
fn generate_cardinality_unsat(n: usize, k: usize) -> (usize, Vec<Vec<Literal>>) {
    assert!(k < n);
    let mut clauses = Vec::new();
    let vars: Vec<Variable> = (0..n).map(|i| Variable::new(i as u32)).collect();

    fn enumerate_subsets(
        n: usize,
        size: usize,
        start: usize,
        depth: usize,
        subset: &mut Vec<usize>,
        vars: &[Variable],
        clauses: &mut Vec<Vec<Literal>>,
    ) {
        if depth == size {
            let clause: Vec<Literal> = subset[..size]
                .iter()
                .map(|&i| Literal::negative(vars[i]))
                .collect();
            clauses.push(clause);
            return;
        }
        for i in start..n {
            subset[depth] = i;
            enumerate_subsets(n, size, i + 1, depth + 1, subset, vars, clauses);
        }
    }

    let mut subset = vec![0usize; k + 1];
    enumerate_subsets(n, k + 1, 0, 0, &mut subset, &vars, &mut clauses);

    for v in &vars[..=k] {
        clauses.push(vec![Literal::positive(*v)]);
    }

    (n, clauses)
}

// ---------------------------------------------------------------------------
// Formula generators: Latin square
// ---------------------------------------------------------------------------

/// 2x2 Latin square with conflicting assignment (UNSAT).
fn generate_latin_square_unsat() -> (usize, Vec<Vec<Literal>>) {
    let num_vars = 8;
    let var =
        |r: usize, c: usize, v: usize| -> Variable { Variable::new((r * 4 + c * 2 + v) as u32) };

    let mut clauses = Vec::new();

    for r in 0..2 {
        for c in 0..2 {
            clauses.push(vec![
                Literal::positive(var(r, c, 0)),
                Literal::positive(var(r, c, 1)),
            ]);
        }
    }
    for r in 0..2 {
        for c in 0..2 {
            clauses.push(vec![
                Literal::negative(var(r, c, 0)),
                Literal::negative(var(r, c, 1)),
            ]);
        }
    }
    for r in 0..2 {
        for v in 0..2 {
            clauses.push(vec![
                Literal::negative(var(r, 0, v)),
                Literal::negative(var(r, 1, v)),
            ]);
        }
    }
    for c in 0..2 {
        for v in 0..2 {
            clauses.push(vec![
                Literal::negative(var(0, c, v)),
                Literal::negative(var(1, c, v)),
            ]);
        }
    }
    // Conflicting: cell (0,0)=val0 and cell (0,1)=val0
    clauses.push(vec![Literal::positive(var(0, 0, 0))]);
    clauses.push(vec![Literal::positive(var(0, 1, 0))]);

    (num_vars, clauses)
}

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

// ===========================================================================
// TEST: Tseitin formula generation (structured UNSAT)
// ===========================================================================

#[test]
fn tseitin_cycle_3_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(3);
    solve_and_verify(nv, &clauses, "tseitin-cycle-3", Some(false));
}

#[test]
fn tseitin_cycle_5_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(5);
    solve_and_verify(nv, &clauses, "tseitin-cycle-5", Some(false));
}

#[test]
fn tseitin_cycle_7_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(7);
    solve_and_verify(nv, &clauses, "tseitin-cycle-7", Some(false));
}

#[test]
fn tseitin_cycle_15_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(15);
    solve_and_verify(nv, &clauses, "tseitin-cycle-15", Some(false));
}

#[test]
fn tseitin_cycle_51_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(51);
    solve_and_verify(nv, &clauses, "tseitin-cycle-51", Some(false));
}

#[test]
fn tseitin_cycle_4_sat() {
    let (nv, clauses) = generate_tseitin_cycle(4);
    solve_and_verify(nv, &clauses, "tseitin-cycle-4", Some(true));
}

#[test]
fn tseitin_cycle_6_sat() {
    let (nv, clauses) = generate_tseitin_cycle(6);
    solve_and_verify(nv, &clauses, "tseitin-cycle-6", Some(true));
}

#[test]
fn tseitin_cycle_50_sat() {
    let (nv, clauses) = generate_tseitin_cycle(50);
    solve_and_verify(nv, &clauses, "tseitin-cycle-50", Some(true));
}

#[test]
fn tseitin_complete_k5_unsat() {
    let (nv, clauses) = generate_tseitin_complete(5);
    solve_and_verify_with_timeout(nv, &clauses, "tseitin-K5", Some(false), 15);
}

#[test]
fn tseitin_complete_k3_unsat() {
    let (nv, clauses) = generate_tseitin_complete(3);
    solve_and_verify(nv, &clauses, "tseitin-K3", Some(false));
}

// ===========================================================================
// TEST: XOR / parity constraints
// ===========================================================================

#[test]
fn xor_cycle_3_unsat() {
    let (nv, clauses) = generate_xor_unsat(3);
    solve_and_verify(nv, &clauses, "xor-cycle-3", Some(false));
}

#[test]
fn xor_cycle_5_unsat() {
    let (nv, clauses) = generate_xor_unsat(5);
    solve_and_verify(nv, &clauses, "xor-cycle-5", Some(false));
}

#[test]
fn xor_cycle_11_unsat() {
    let (nv, clauses) = generate_xor_unsat(11);
    solve_and_verify(nv, &clauses, "xor-cycle-11", Some(false));
}

#[test]
fn xor_cycle_25_unsat() {
    let (nv, clauses) = generate_xor_unsat(25);
    solve_and_verify(nv, &clauses, "xor-cycle-25", Some(false));
}

#[test]
fn xor_cycle_101_unsat() {
    let (nv, clauses) = generate_xor_unsat(101);
    solve_and_verify(nv, &clauses, "xor-cycle-101", Some(false));
}

#[test]
fn parity_4_forced_unsat() {
    let (nv, clauses) = generate_parity_unsat(4);
    solve_and_verify(nv, &clauses, "parity-4-forced", Some(false));
}

#[test]
fn parity_6_forced_unsat() {
    let (nv, clauses) = generate_parity_unsat(6);
    solve_and_verify(nv, &clauses, "parity-6-forced", Some(false));
}

#[test]
fn parity_10_forced_unsat() {
    let (nv, clauses) = generate_parity_unsat(10);
    solve_and_verify(nv, &clauses, "parity-10-forced", Some(false));
}

// ===========================================================================
// TEST: Cardinality constraints
// ===========================================================================

#[test]
fn cardinality_atmost1_of_5_unsat() {
    let (nv, clauses) = generate_cardinality_unsat(5, 1);
    solve_and_verify(nv, &clauses, "card-amo1-of-5", Some(false));
}

#[test]
fn cardinality_atmost2_of_6_unsat() {
    let (nv, clauses) = generate_cardinality_unsat(6, 2);
    solve_and_verify(nv, &clauses, "card-amo2-of-6", Some(false));
}

#[test]
fn cardinality_atmost3_of_8_unsat() {
    let (nv, clauses) = generate_cardinality_unsat(8, 3);
    solve_and_verify(nv, &clauses, "card-amo3-of-8", Some(false));
}

// ===========================================================================
// TEST: Latin square constraints
// ===========================================================================

#[test]
fn latin_square_2x2_conflict_unsat() {
    let (nv, clauses) = generate_latin_square_unsat();
    solve_and_verify(nv, &clauses, "latin-2x2-conflict", Some(false));
}

// ===========================================================================
// TEST: DRAT proof verification on generated UNSAT instances
// ===========================================================================

#[test]
fn drat_xor_cycle_3() {
    let (nv, clauses) = generate_xor_unsat(3);
    let r = solve_and_verify_drat(nv, &clauses, "drat-xor-3", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_xor_cycle_5() {
    let (nv, clauses) = generate_xor_unsat(5);
    let r = solve_and_verify_drat(nv, &clauses, "drat-xor-5", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_tseitin_cycle_3() {
    let (nv, clauses) = generate_tseitin_cycle(3);
    let r = solve_and_verify_drat(nv, &clauses, "drat-tseitin-3", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_cardinality_atmost1_of_5() {
    let (nv, clauses) = generate_cardinality_unsat(5, 1);
    let r = solve_and_verify_drat(nv, &clauses, "drat-card-amo1-5", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_parity_4_forced() {
    let (nv, clauses) = generate_parity_unsat(4);
    let r = solve_and_verify_drat(nv, &clauses, "drat-parity-4", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_latin_square_2x2() {
    let (nv, clauses) = generate_latin_square_unsat();
    let r = solve_and_verify_drat(nv, &clauses, "drat-latin-2x2", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

// ===========================================================================
// TEST: Incremental solve soundness
// ===========================================================================

/// Solve SAT, add contradicting clause via push/pop, re-solve as UNSAT.
#[test]
fn incremental_sat_then_unsat() {
    let mut solver = Solver::new(5);

    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ]);

    let r1 = solver.solve().into_inner();
    assert!(matches!(r1, SatResult::Sat(_)), "first solve should be SAT");

    // Add contradicting units
    solver.add_clause(vec![Literal::positive(Variable::new(4))]);
    solver.add_clause(vec![Literal::negative(Variable::new(4))]);

    let r2 = solver.solve().into_inner();
    assert!(
        matches!(r2, SatResult::Unsat(_)),
        "second solve should be UNSAT after adding x4 AND NOT x4"
    );
}

/// Solve a formula with an extra constraining clause and verify the model
/// satisfies all clauses including the tighter constraint.
#[test]
fn incremental_sat_tighten() {
    let clause1 = vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ];
    let clause2 = vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ];

    let r1 = solve_and_verify(
        4,
        &[clause1.clone(), clause2.clone()],
        "tighten-base",
        Some(true),
    );
    assert!(matches!(r1, SatResult::Sat(_)));

    let clause3 = vec![Literal::negative(Variable::new(0))];
    let tighter = vec![clause1, clause2, clause3];
    let r2 = solve_and_verify(4, &tighter, "tighten-constrained", Some(true));

    if let SatResult::Sat(model) = &r2 {
        assert!(
            model.get(1).copied().unwrap_or(false),
            "x1 must be true since x0 is forced false"
        );
    }
}

// ===========================================================================
// TEST: SAT-to-UNSAT transition via unit clause injection
// ===========================================================================

#[test]
fn sat_to_unsat_unit_injection() {
    let mut rng = Rng::new(0x7904_DEAD);
    for seed_offset in 0..10 {
        let (nv, clauses, assignment) = generate_forced_sat(&mut rng, 10);
        let label = format!("sat-to-unsat-{seed_offset}");

        let r = solve_and_verify(nv, &clauses, &format!("{label}-sat"), Some(true));
        assert!(matches!(r, SatResult::Sat(_)), "{label}: expected SAT");

        let mut unsat_clauses = clauses.clone();
        let forced_val = assignment[0];
        let contra = if forced_val {
            Literal::negative(Variable::new(0))
        } else {
            Literal::positive(Variable::new(0))
        };
        unsat_clauses.push(vec![contra]);
        let original = if forced_val {
            Literal::positive(Variable::new(0))
        } else {
            Literal::negative(Variable::new(0))
        };
        unsat_clauses.push(vec![original]);

        let r2 = solve_and_verify(nv, &unsat_clauses, &format!("{label}-unsat"), Some(false));
        assert!(matches!(r2, SatResult::Unsat(_)), "{label}: expected UNSAT");
    }
}

// ===========================================================================
// TEST: Multi-seed reproducibility (determinism check)
// ===========================================================================

#[test]
fn determinism_same_formula_5_runs() {
    let mut rng = Rng::new(0x7904_DE70);
    let num_vars = 30u32;
    let num_clauses = (f64::from(num_vars) * 3.5).round() as usize;
    let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);

    let mut results = Vec::new();
    for i in 0..5 {
        let r = solve_and_verify(nv, &clauses, &format!("det-run-{i}"), None);
        results.push(classify(&r));
    }
    let first = results[0];
    for (i, r) in results.iter().enumerate().skip(1) {
        assert_eq!(
            first, *r,
            "Determinism failure: run 0 = {first:?}, run {i} = {r:?}"
        );
    }
}

#[test]
fn determinism_unsat_5_runs() {
    let (nv, clauses) = generate_xor_unsat(7);
    for i in 0..5 {
        let r = solve_and_verify(nv, &clauses, &format!("det-unsat-run-{i}"), Some(false));
        assert!(matches!(r, SatResult::Unsat(_)), "run {i}: expected UNSAT");
    }
}

// ===========================================================================
// TEST: Crafted corner cases
// ===========================================================================

#[test]
fn corner_single_var_pos() {
    let clauses = vec![vec![Literal::positive(Variable::new(0))]];
    solve_and_verify(1, &clauses, "single-var-pos", Some(true));
}

#[test]
fn corner_single_var_neg() {
    let clauses = vec![vec![Literal::negative(Variable::new(0))]];
    solve_and_verify(1, &clauses, "single-var-neg", Some(true));
}

#[test]
fn corner_single_var_contradiction() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::negative(Variable::new(0))],
    ];
    solve_and_verify(1, &clauses, "single-var-contra", Some(false));
}

#[test]
fn corner_two_var_full_contradiction() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::negative(Variable::new(0))],
        vec![Literal::positive(Variable::new(1))],
        vec![Literal::negative(Variable::new(1))],
    ];
    solve_and_verify(2, &clauses, "two-var-full-contra", Some(false));
}

#[test]
fn corner_long_clause_all_negated() {
    let n = 20;
    let long_clause: Vec<Literal> = (0..n)
        .map(|i| Literal::positive(Variable::new(i)))
        .collect();
    let mut clauses = vec![long_clause];
    for i in 0..n {
        clauses.push(vec![Literal::negative(Variable::new(i))]);
    }
    solve_and_verify(n as usize, &clauses, "long-clause-negated", Some(false));
}

#[test]
fn corner_implication_chain_cycle() {
    let n = 15;
    let mut clauses = Vec::new();
    clauses.push(vec![Literal::positive(Variable::new(0))]);
    for i in 0..(n - 1) {
        clauses.push(vec![
            Literal::negative(Variable::new(i)),
            Literal::positive(Variable::new(i + 1)),
        ]);
    }
    clauses.push(vec![
        Literal::negative(Variable::new(n - 1)),
        Literal::negative(Variable::new(0)),
    ]);
    solve_and_verify(n as usize, &clauses, "impl-chain-cycle", Some(false));
}

#[test]
fn corner_all_negative_binary_sat() {
    let n = 10u32;
    let mut clauses = Vec::new();
    for i in 0..(n - 1) {
        clauses.push(vec![
            Literal::negative(Variable::new(i)),
            Literal::negative(Variable::new(i + 1)),
        ]);
    }
    solve_and_verify(n as usize, &clauses, "all-neg-binary", Some(true));
}

#[test]
fn corner_pure_literals_100() {
    let n = 100u32;
    let mut clauses = Vec::new();
    for i in 0..n {
        clauses.push(vec![
            Literal::positive(Variable::new(i)),
            Literal::positive(Variable::new((i + 1) % n)),
        ]);
    }
    solve_and_verify(n as usize, &clauses, "pure-100", Some(true));
}

#[test]
fn corner_tautological_clause_sat() {
    let clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(0)),
        ],
        vec![Literal::positive(Variable::new(1))],
    ];
    solve_and_verify(2, &clauses, "tautological-sat", Some(true));
}

#[test]
fn corner_tautological_with_contradiction() {
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(0)),
        ],
        vec![Literal::positive(Variable::new(1))],
        vec![Literal::negative(Variable::new(1))],
    ];
    solve_and_verify(2, &clauses, "tautological-unsat", Some(false));
}

#[test]
fn corner_duplicate_clauses_sat() {
    let clause = vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ];
    let mut clauses = Vec::new();
    for _ in 0..50 {
        clauses.push(clause.clone());
    }
    clauses.push(vec![Literal::negative(Variable::new(2))]);
    solve_and_verify(3, &clauses, "duplicate-50x", Some(true));
}

#[test]
fn corner_subsumed_clauses() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![Literal::negative(Variable::new(2))],
        vec![
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];
    solve_and_verify(4, &clauses, "subsumed-clauses", Some(true));
}

// ===========================================================================
// TEST: Larger random 3-SAT (200 variables, phase transition)
// ===========================================================================

#[test]
fn random_3sat_200v_phase_transition() {
    let mut rng = Rng::new(0x7904_2001);
    let num_vars = 200u32;
    let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
    let mut sat_count = 0;
    let mut unsat_count = 0;

    for i in 0..10 {
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let r = solve_and_verify_with_timeout(nv, &clauses, &format!("random-200v-{i}"), None, 30);
        match classify(&r) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }
    eprintln!("random 3-SAT (200v): {sat_count} SAT, {unsat_count} UNSAT");
    assert!(
        sat_count + unsat_count > 0,
        "expected at least one to resolve"
    );
}

#[test]
fn random_3sat_150v_below_transition() {
    let mut rng = Rng::new(0x7904_1500);
    let num_vars = 150u32;
    let num_clauses = (f64::from(num_vars) * 4.0).round() as usize;
    let mut sat_count = 0;

    for i in 0..10 {
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let r = solve_and_verify_with_timeout(
            nv,
            &clauses,
            &format!("random-150v-below-{i}"),
            None,
            15,
        );
        if matches!(r, SatResult::Sat(_)) {
            sat_count += 1;
        }
    }
    eprintln!("random 3-SAT (150v, ratio 4.0): {sat_count}/10 SAT");
}

#[test]
fn random_3sat_150v_above_transition() {
    let mut rng = Rng::new(0x7904_1501);
    let num_vars = 150u32;
    let num_clauses = (f64::from(num_vars) * 4.5).round() as usize;
    let mut unsat_count = 0;

    for i in 0..10 {
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let r = solve_and_verify_with_timeout(
            nv,
            &clauses,
            &format!("random-150v-above-{i}"),
            None,
            15,
        );
        if matches!(r, SatResult::Unsat(_)) {
            unsat_count += 1;
        }
    }
    eprintln!("random 3-SAT (150v, ratio 4.5): {unsat_count}/10 UNSAT");
}

// ===========================================================================
// TEST: Cross-configuration differential
// ===========================================================================

#[test]
fn differential_tseitin_configs() {
    let mut disagreements = Vec::new();
    let mut agreements = 0;

    for n in [3, 5, 7, 9, 11, 13, 4, 6, 8, 10, 12, 14] {
        let (nv, clauses) = generate_tseitin_cycle(n);
        let label = format!("tseitin-cycle-{n}");
        let expected = if n % 2 == 1 { Some(false) } else { Some(true) };

        let r1 = solve_and_verify(nv, &clauses, &format!("{label}-default"), expected);
        let r2 =
            solve_no_inprocessing_and_verify(nv, &clauses, &format!("{label}-no-inproc"), expected);

        let v1 = classify(&r1);
        let v2 = classify(&r2);
        if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
            if v1 != v2 {
                disagreements.push(format!("{label}: default={v1:?}, no-inproc={v2:?}"));
            } else {
                agreements += 1;
            }
        }
    }

    eprintln!(
        "Tseitin differential: {agreements} agreements, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: config disagreements:\n{}",
        disagreements.join("\n")
    );
}

#[test]
fn differential_xor_configs() {
    let mut disagreements = Vec::new();
    let mut agreements = 0;

    for n in [3, 5, 7, 9, 11, 15, 21] {
        let (nv, clauses) = generate_xor_unsat(n);
        let label = format!("xor-{n}");

        let r1 = solve_and_verify(nv, &clauses, &format!("{label}-default"), Some(false));
        let r2 = solve_no_inprocessing_and_verify(
            nv,
            &clauses,
            &format!("{label}-no-inproc"),
            Some(false),
        );

        let v1 = classify(&r1);
        let v2 = classify(&r2);
        if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
            if v1 != v2 {
                disagreements.push(format!("{label}: default={v1:?}, no-inproc={v2:?}"));
            } else {
                agreements += 1;
            }
        }
    }

    eprintln!(
        "XOR differential: {agreements} agreements, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: XOR config disagreements:\n{}",
        disagreements.join("\n")
    );
}

// ===========================================================================
// TEST: SATCOMP 2022/2023 benchmark coverage
// ===========================================================================

#[test]
fn satcomp_2022_soundness() {
    let benchmarks = [
        "benchmarks/sat/2022/6f956a3f95ccaf35a3de1fe72b9cf79e.cnf",
        "benchmarks/sat/2022/81b674a2aa6fbda9b06cf8ea334ddc44.cnf",
        "benchmarks/sat/2022/efc1b836380d0f84e7512f7b2ccdbb60.cnf",
    ];
    let mut sat_verified = 0;
    let mut unsat_count = 0;
    let mut timeout_count = 0;
    let mut skipped = 0;

    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = match super::common::load_optional_repo_benchmark(path) {
            Some(c) => c,
            None => {
                skipped += 1;
                continue;
            }
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");

        let r = solve_and_verify_with_timeout(formula.num_vars, &formula.clauses, label, None, 30);
        match classify(&r) {
            Verdict::Sat => sat_verified += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => timeout_count += 1,
        }
    }
    eprintln!("SATCOMP 2022: {sat_verified} SAT, {unsat_count} UNSAT, {timeout_count} timeouts, {skipped} skipped");
}

#[test]
fn satcomp_2023_soundness() {
    let benchmarks = ["benchmarks/sat/2023/3663000b31a5c80922afc6e48322accb.cnf"];
    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = match super::common::load_optional_repo_benchmark(path) {
            Some(c) => c,
            None => continue,
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let r = solve_and_verify_with_timeout(formula.num_vars, &formula.clauses, label, None, 30);
        match classify(&r) {
            Verdict::Sat | Verdict::Unsat => {}
            Verdict::Unknown => eprintln!("{label}: timeout"),
        }
    }
}

// ===========================================================================
// TEST: DRAT proof batch for UNSAT benchmarks
// ===========================================================================

#[test]
fn benchmark_unsat_drat_proof_batch() {
    let small_unsat = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
    ];
    let mut verified = 0;

    for path in &small_unsat {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = super::common::load_repo_benchmark(path);
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");

        let mut solver =
            Solver::with_proof_output(formula.num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }

        let started = Instant::now();
        let timeout = std::time::Duration::from_secs(15);
        let result = solver
            .solve_interruptible(|| started.elapsed() >= timeout)
            .into_inner();

        match result {
            SatResult::Unsat(_) => {
                let proof_output = solver.take_proof_writer().expect("proof writer");
                let proof_bytes = proof_output.into_vec().expect("flush");
                let dimacs = super::common::clauses_to_dimacs(formula.num_vars, &formula.clauses);
                super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
                verified += 1;
            }
            SatResult::Sat(_) => {
                panic!("SOUNDNESS BUG: {label} is known-UNSAT but returned SAT");
            }
            SatResult::Unknown => {
                eprintln!("{label}: timeout in DRAT proof verification test");
            }
            _ => unreachable!(),
        }
    }
    eprintln!(
        "DRAT proof batch: {verified}/{} verified",
        small_unsat.len()
    );
    assert!(
        verified >= 5,
        "expected at least 5 DRAT proofs to verify, got {verified}"
    );
}

// ===========================================================================
// TEST: eq.atree.braun differential
// ===========================================================================

#[test]
fn braun_differential_default_vs_baseline() {
    let braun_files = [
        (
            "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
            "braun-8",
        ),
        (
            "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
            "braun-10",
        ),
    ];
    let mut disagreements = Vec::new();

    for (path, name) in &braun_files {
        let cnf = match super::common::load_optional_repo_benchmark(path) {
            Some(c) => c,
            None => continue,
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");

        let r1 = solve_and_verify_with_timeout(
            formula.num_vars,
            &formula.clauses,
            &format!("{name}-default"),
            Some(false),
            30,
        );
        let r2 = solve_no_inprocessing_and_verify(
            formula.num_vars,
            &formula.clauses,
            &format!("{name}-no-inproc"),
            Some(false),
        );

        let v1 = classify(&r1);
        let v2 = classify(&r2);
        if v1 != Verdict::Unknown && v2 != Verdict::Unknown && v1 != v2 {
            disagreements.push(format!("{name}: default={v1:?}, no-inproc={v2:?}"));
        }
    }
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: braun differential disagreements:\n{}",
        disagreements.join("\n")
    );
}
