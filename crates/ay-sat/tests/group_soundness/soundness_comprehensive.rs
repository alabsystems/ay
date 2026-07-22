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

// ===========================================================================
// TEST: Pigeonhole Principle
// ===========================================================================

#[test]
fn php_3_2_unsat() {
    let (nv, clauses) = generate_php(3, 2);
    solve_and_verify(nv, &clauses, "PHP(3,2)", Some(false));
}

#[test]
fn php_4_3_unsat() {
    let (nv, clauses) = generate_php(4, 3);
    solve_and_verify(nv, &clauses, "PHP(4,3)", Some(false));
}

#[test]
fn php_5_4_unsat() {
    let (nv, clauses) = generate_php(5, 4);
    solve_and_verify(nv, &clauses, "PHP(5,4)", Some(false));
}

#[test]
fn php_6_5_unsat() {
    let (nv, clauses) = generate_php(6, 5);
    solve_and_verify(nv, &clauses, "PHP(6,5)", Some(false));
}

#[test]
fn php_7_6_unsat() {
    let (nv, clauses) = generate_php(7, 6);
    solve_and_verify_with_timeout(nv, &clauses, "PHP(7,6)", Some(false), 15);
}

#[test]
fn php_8_7_unsat() {
    let (nv, clauses) = generate_php(8, 7);
    // PHP(8,7) may timeout; that's acceptable. SAT would be a soundness bug.
    solve_and_verify_with_timeout(nv, &clauses, "PHP(8,7)", Some(false), 15);
}

/// PHP(n, n) is satisfiable (n pigeons, n holes -- each pigeon gets one hole).
#[test]
fn php_3_3_sat() {
    let (nv, clauses) = generate_php(3, 3);
    solve_and_verify(nv, &clauses, "PHP(3,3)", Some(true));
}

#[test]
fn php_4_4_sat() {
    let (nv, clauses) = generate_php(4, 4);
    solve_and_verify(nv, &clauses, "PHP(4,4)", Some(true));
}

#[test]
fn php_5_5_sat() {
    let (nv, clauses) = generate_php(5, 5);
    solve_and_verify(nv, &clauses, "PHP(5,5)", Some(true));
}

// ===========================================================================
// TEST: Pigeonhole with no-inprocessing (differential)
// ===========================================================================

#[test]
fn php_differential_3_2() {
    let (nv, clauses) = generate_php(3, 2);
    let r1 = solve_and_verify(nv, &clauses, "PHP(3,2)-default", Some(false));
    let r2 = solve_no_inprocessing_and_verify(nv, &clauses, "PHP(3,2)-baseline", Some(false));
    assert_eq!(classify(&r1), classify(&r2), "PHP(3,2) disagreement");
}

#[test]
fn php_differential_4_3() {
    let (nv, clauses) = generate_php(4, 3);
    let r1 = solve_and_verify(nv, &clauses, "PHP(4,3)-default", Some(false));
    let r2 = solve_no_inprocessing_and_verify(nv, &clauses, "PHP(4,3)-baseline", Some(false));
    assert_eq!(classify(&r1), classify(&r2), "PHP(4,3) disagreement");
}

#[test]
fn php_differential_5_4() {
    let (nv, clauses) = generate_php(5, 4);
    let r1 = solve_and_verify(nv, &clauses, "PHP(5,4)-default", Some(false));
    let r2 = solve_no_inprocessing_and_verify(nv, &clauses, "PHP(5,4)-baseline", Some(false));
    let v1 = classify(&r1);
    let v2 = classify(&r2);
    if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
        assert_eq!(v1, v2, "PHP(5,4) disagreement");
    }
}

// ===========================================================================
// TEST: Graph Coloring (complete graph)
// ===========================================================================

/// K_4 with 3 colors: UNSAT (chromatic number of K_4 is 4)
#[test]
fn graph_coloring_k4_3colors_unsat() {
    let (nv, clauses) = generate_graph_coloring_complete(4, 3);
    solve_and_verify(nv, &clauses, "K4-3color", Some(false));
}

/// K_5 with 4 colors: UNSAT
#[test]
fn graph_coloring_k5_4colors_unsat() {
    let (nv, clauses) = generate_graph_coloring_complete(5, 4);
    solve_and_verify(nv, &clauses, "K5-4color", Some(false));
}

/// K_6 with 5 colors: UNSAT
#[test]
fn graph_coloring_k6_5colors_unsat() {
    let (nv, clauses) = generate_graph_coloring_complete(6, 5);
    solve_and_verify_with_timeout(nv, &clauses, "K6-5color", Some(false), 15);
}

/// K_3 with 3 colors: SAT (exact chromatic number)
#[test]
fn graph_coloring_k3_3colors_sat() {
    let (nv, clauses) = generate_graph_coloring_complete(3, 3);
    solve_and_verify(nv, &clauses, "K3-3color", Some(true));
}

/// K_4 with 4 colors: SAT
#[test]
fn graph_coloring_k4_4colors_sat() {
    let (nv, clauses) = generate_graph_coloring_complete(4, 4);
    solve_and_verify(nv, &clauses, "K4-4color", Some(true));
}

/// K_5 with 5 colors: SAT
#[test]
fn graph_coloring_k5_5colors_sat() {
    let (nv, clauses) = generate_graph_coloring_complete(5, 5);
    solve_and_verify(nv, &clauses, "K5-5color", Some(true));
}

// ===========================================================================
// TEST: Ordering cycle (UNSAT)
// ===========================================================================

#[test]
fn ordering_cycle_3_unsat() {
    let (nv, clauses) = generate_ordering_cycle(3);
    solve_and_verify(nv, &clauses, "order-cycle-3", Some(false));
}

#[test]
fn ordering_cycle_5_unsat() {
    let (nv, clauses) = generate_ordering_cycle(5);
    solve_and_verify(nv, &clauses, "order-cycle-5", Some(false));
}

#[test]
fn ordering_cycle_10_unsat() {
    let (nv, clauses) = generate_ordering_cycle(10);
    solve_and_verify(nv, &clauses, "order-cycle-10", Some(false));
}

#[test]
fn ordering_cycle_20_unsat() {
    let (nv, clauses) = generate_ordering_cycle(20);
    solve_and_verify(nv, &clauses, "order-cycle-20", Some(false));
}

// ===========================================================================
// TEST: Random 3-SAT near phase transition
// ===========================================================================

/// Run a batch of random 3-SAT instances at the phase transition ratio.
/// Verifies SAT models against original clauses. Does not assert SAT/UNSAT
/// outcome since these are random.
#[test]
fn random_3sat_phase_transition_batch() {
    let mut rng = Rng::new(0x7904_DEAD_BEEF_0001);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut unknown_count = 0usize;

    // 50 instances, 20 variables, ~85 clauses (ratio 4.267)
    for i in 0..50 {
        let num_vars = 20u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("random-3sat-20v-{i}");

        let result = solve_and_verify(nv, &clauses, &label, None);
        match classify(&result) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => unknown_count += 1,
        }
    }

    eprintln!(
        "random 3-SAT phase transition (20v): {sat_count} SAT, {unsat_count} UNSAT, {unknown_count} unknown (of 50)"
    );
    // At the phase transition, roughly half should be SAT and half UNSAT.
    // We just need at least some of each to have meaningful coverage.
    assert!(
        sat_count + unsat_count > 0,
        "Expected at least one random 3-SAT to resolve"
    );
}

/// Larger instances: 50 variables, ~213 clauses.
#[test]
fn random_3sat_50v_phase_transition() {
    let mut rng = Rng::new(0x7904_DEAD_BEEF_0002);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..30 {
        let num_vars = 50u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("random-3sat-50v-{i}");

        let result = solve_and_verify_with_timeout(nv, &clauses, &label, None, 10);
        match classify(&result) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!("random 3-SAT phase transition (50v): {sat_count} SAT, {unsat_count} UNSAT (of 30)");
    assert!(
        sat_count + unsat_count > 0,
        "Expected at least one 50v random 3-SAT to resolve within 10s"
    );
}

/// 100 variables near phase transition -- exercises more of the CDCL machinery.
#[test]
fn random_3sat_100v_phase_transition() {
    let mut rng = Rng::new(0x7904_DEAD_BEEF_0003);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..20 {
        let num_vars = 100u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("random-3sat-100v-{i}");

        let result = solve_and_verify_with_timeout(nv, &clauses, &label, None, 10);
        match classify(&result) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!("random 3-SAT phase transition (100v): {sat_count} SAT, {unsat_count} UNSAT (of 20)");
}

// ===========================================================================
// TEST: Known-SAT formulas with model verification
// ===========================================================================

/// Trivially satisfiable: single positive unit clause.
#[test]
fn trivial_sat_unit_clause() {
    let clauses = vec![vec![Literal::positive(Variable::new(0))]];
    solve_and_verify(1, &clauses, "unit-pos", Some(true));
}

/// Satisfiable: 3 independent positive units.
#[test]
fn sat_independent_units() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::positive(Variable::new(1))],
        vec![Literal::positive(Variable::new(2))],
    ];
    solve_and_verify(3, &clauses, "independent-units", Some(true));
}

/// Satisfiable: mixed polarity units (forces a specific assignment).
#[test]
fn sat_mixed_units() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::negative(Variable::new(1))],
        vec![Literal::positive(Variable::new(2))],
        vec![Literal::negative(Variable::new(3))],
    ];
    solve_and_verify(4, &clauses, "mixed-units", Some(true));
}

/// Empty formula is SAT.
#[test]
fn sat_empty_formula() {
    let clauses: Vec<Vec<Literal>> = vec![];
    solve_and_verify(0, &clauses, "empty-formula", Some(true));
}

/// Single empty clause is UNSAT.
#[test]
fn unsat_empty_clause() {
    let clauses = vec![vec![]];
    solve_and_verify(0, &clauses, "empty-clause", Some(false));
}

/// Formula with forced SAT assignment (generated).
#[test]
fn generated_forced_sat_small() {
    let mut rng = Rng::new(0x0790_45A7_0001);
    for i in 0..20 {
        let (nv, clauses, _assignment) = generate_forced_sat(&mut rng, 15);
        let label = format!("forced-sat-15v-{i}");
        solve_and_verify(nv, &clauses, &label, Some(true));
    }
}

/// Larger forced SAT formulas.
#[test]
fn generated_forced_sat_medium() {
    let mut rng = Rng::new(0x0790_45A7_0002);
    for i in 0..10 {
        let (nv, clauses, _assignment) = generate_forced_sat(&mut rng, 50);
        let label = format!("forced-sat-50v-{i}");
        solve_and_verify(nv, &clauses, &label, Some(true));
    }
}

// ===========================================================================
// TEST: Benchmark files from benchmarks/sat/unsat/
// ===========================================================================

/// Verify all benchmarks/sat/unsat/*.cnf files return UNSAT or timeout.
/// This covers the full UNSAT corpus including graph coloring, pigeonhole,
/// Tseitin, mutex, parity, and random 3-SAT benchmarks.
#[test]
fn all_unsat_benchmarks() {
    let benchmarks = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/cardinality_8.cnf",
        "benchmarks/sat/unsat/double_parity_5.cnf",
        "benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k5_6clique.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutex_6proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/parity_6.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/php_5_4.cnf",
        "benchmarks/sat/unsat/php_6_5.cnf",
        "benchmarks/sat/unsat/php_7_6.cnf",
        "benchmarks/sat/unsat/php_functional_5_4.cnf",
        "benchmarks/sat/unsat/ramsey_r3_3_6.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12349.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
        "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
        "benchmarks/sat/unsat/tseitin_grid_3x3.cnf",
        "benchmarks/sat/unsat/tseitin_k5.cnf",
        "benchmarks/sat/unsat/tseitin_random_15.cnf",
        "benchmarks/sat/unsat/urquhart_3.cnf",
    ];

    let mut solved = 0usize;
    let mut timeouts = 0usize;

    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = super::common::load_repo_benchmark(path);
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let original_clauses = formula.clauses.clone();

        let result = solve_and_verify_with_timeout(
            formula.num_vars,
            &original_clauses,
            label,
            Some(false), // known UNSAT
            15,
        );

        match classify(&result) {
            Verdict::Unsat => solved += 1,
            Verdict::Unknown => timeouts += 1,
            Verdict::Sat => {
                // solve_and_verify_with_timeout already panics on SAT for known-UNSAT
                unreachable!();
            }
        }
    }

    eprintln!(
        "UNSAT benchmarks: {solved} solved, {timeouts} timeouts (of {})",
        benchmarks.len()
    );
    // All of these are small enough to solve
    assert!(
        solved >= 20,
        "Expected at least 20 UNSAT benchmarks to solve, got {solved}"
    );
}

// ===========================================================================
// TEST: Known-SAT benchmark file tests with model verification
// ===========================================================================

/// Verify the canary SAT benchmark produces a valid model.
#[test]
fn canary_sat_model_verified() {
    let cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_sat.cnf");
    let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();
    solve_and_verify(
        formula.num_vars,
        &original_clauses,
        "canary-sat",
        Some(true),
    );
}

/// Verify the canary UNSAT benchmark.
#[test]
fn canary_unsat_verified() {
    let cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_unsat.cnf");
    let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();
    solve_and_verify(
        formula.num_vars,
        &original_clauses,
        "canary-unsat",
        Some(false),
    );
}

/// Known SAT benchmarks from must_solve.txt.
#[test]
fn must_solve_sat_benchmarks_model_verified() {
    let sat_benchmarks = [
        "benchmarks/sat/satcomp2024-sample/08ccc34df5d8eb9e9d45278af3dc093d-simon-r16-1.sanitized.cnf",
        "benchmarks/sat/satcomp2024-sample/7083b70c1976162e2693d7a493717ffd-battleship-14-26-sat.cnf",
    ];

    for path in &sat_benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let Some(cnf) = super::common::load_optional_repo_benchmark(path) else {
            eprintln!("SKIP: must-solve SAT benchmark not available at {path}");
            continue;
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let original_clauses = formula.clauses.clone();

        let result = solve_and_verify_with_timeout(
            formula.num_vars,
            &original_clauses,
            label,
            Some(true), // known SAT
            30,
        );

        match classify(&result) {
            Verdict::Sat => {
                // Model already verified in solve_and_verify_with_timeout
            }
            Verdict::Unknown => {
                eprintln!("{label}: timeout (performance regression, not soundness bug)");
            }
            Verdict::Unsat => {
                // solve_and_verify_with_timeout already panics
                unreachable!();
            }
        }
    }
}

// ===========================================================================
// TEST: Cross-configuration differential on generated instances
// ===========================================================================

/// Run generated instances with both default and no-inprocessing configs.
/// Verify that they agree on SAT/UNSAT (when both resolve).
#[test]
fn differential_generated_formulas() {
    let mut rng = Rng::new(0x7904_D1FF_0001);
    let mut agreements = 0usize;
    let mut disagreements = Vec::new();

    for i in 0..40 {
        let num_vars = 15u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("diff-15v-{i}");

        let r1 = solve_and_verify(nv, &clauses, &format!("{label}-default"), None);
        let r2 = solve_no_inprocessing_and_verify(nv, &clauses, &format!("{label}-baseline"), None);

        let v1 = classify(&r1);
        let v2 = classify(&r2);

        if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
            if v1 != v2 {
                disagreements.push(format!("{label}: default={v1:?}, baseline={v2:?}"));
            } else {
                agreements += 1;
            }
        }
    }

    eprintln!(
        "differential test: {agreements} agreements, {} disagreements (of 40)",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: configuration disagreements:\n{}",
        disagreements.join("\n")
    );
}

// ===========================================================================
// TEST: SATCOMP2024 sample benchmarks (mixed SAT/UNSAT)
// ===========================================================================

/// Run SATCOMP2024 sample benchmarks (.cnf and .cnf.xz) with a timeout.
/// Verify SAT models and ensure no false UNSAT on known-SAT instances.
#[test]
fn satcomp2024_sample_model_verification() {
    let root = super::common::workspace_root();
    let sample_dir = root.join("benchmarks/sat/satcomp2024-sample");
    if !sample_dir.is_dir() {
        eprintln!("SKIP: satcomp2024-sample directory not found");
        return;
    }

    let mut sat_verified = 0usize;
    let mut unsat_count = 0usize;
    let mut timeouts = 0usize;
    let mut failures = Vec::new();

    // Collect .cnf and .cnf.xz files. Benchmarks may be stored compressed
    // to save space (#8116).
    let entries: Vec<_> = std::fs::read_dir(&sample_dir)
        .expect("read sample dir")
        .filter_map(Result::ok)
        .filter(|e| {
            let p = e.path();
            p.extension().is_some_and(|ext| ext == "cnf")
                || (p.extension().is_some_and(|ext| ext == "xz")
                    && p.to_string_lossy().ends_with(".cnf.xz"))
        })
        .collect();

    // Limit to first 5 compressed benchmarks to keep test runtime reasonable.
    let max_xz = 5usize;
    let mut xz_count = 0usize;

    for entry in &entries {
        let path = entry.path();
        let is_xz = path.extension().is_some_and(|ext| ext == "xz");
        if is_xz {
            if xz_count >= max_xz {
                continue;
            }
            xz_count += 1;
        }
        let label = path.file_name().unwrap().to_string_lossy().to_string();

        let cnf = match super::common::load_optional_benchmark(&path) {
            Some(s) => s,
            None => continue,
        };

        let formula = match ay_sat::parse_dimacs(&cnf) {
            Ok(f) => f,
            Err(e) => {
                failures.push(format!("{label}: parse error: {e}"));
                continue;
            }
        };

        let original_clauses = formula.clauses.clone();

        // Use timeout since some benchmarks are hard
        let result = solve_and_verify_with_timeout(
            formula.num_vars,
            &original_clauses,
            &label,
            None, // we don't know the expected result for all
            15,
        );

        match classify(&result) {
            Verdict::Sat => sat_verified += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => timeouts += 1,
        }
    }

    eprintln!(
        "SATCOMP2024 sample: {} SAT (model verified), {} UNSAT, {} timeouts, {} failures (of {})",
        sat_verified,
        unsat_count,
        timeouts,
        failures.len(),
        entries.len()
    );

    assert!(
        failures.is_empty(),
        "SATCOMP2024 sample failures:\n{}",
        failures.join("\n")
    );

    if sat_verified + unsat_count == 0 {
        eprintln!(
            "SATCOMP2024 sample: all available benchmarks timed out; no wrong answer observed"
        );
    }
}

// ===========================================================================
// TEST: Inline known formulas
// ===========================================================================

/// PHP(3,2) from common module (cross-check against generated version).
#[test]
fn inline_php32_cross_check() {
    // Parse the DIMACS version from common
    let formula = ay_sat::parse_dimacs(super::common::PHP32_DIMACS).expect("parse PHP(3,2)");
    let result_dimacs = solve_and_verify(
        formula.num_vars,
        &formula.clauses,
        "PHP(3,2)-dimacs",
        Some(false),
    );

    // Compare with generated version
    let (nv, clauses) = generate_php(3, 2);
    let result_gen = solve_and_verify(nv, &clauses, "PHP(3,2)-gen", Some(false));

    assert_eq!(
        classify(&result_dimacs),
        classify(&result_gen),
        "PHP(3,2) DIMACS vs generated should agree"
    );
}

/// PHP(4,3) from common module.
#[test]
fn inline_php43_cross_check() {
    let formula = ay_sat::parse_dimacs(super::common::PHP43_DIMACS).expect("parse PHP(4,3)");
    solve_and_verify(
        formula.num_vars,
        &formula.clauses,
        "PHP(4,3)-dimacs",
        Some(false),
    );
}

// ===========================================================================
// TEST: Regression for the original P0 bug (any public .cnf returning wrong answer)
// ===========================================================================

/// Run all public .cnf files under benchmarks/sat/ (non-recursive, excluding
/// subdirectories already tested) to ensure no wrong answers. This catches
/// the case where a new benchmark is added and ay gives a wrong answer.
#[test]
fn all_benchmark_cnf_no_wrong_answer() {
    let root = super::common::workspace_root();

    // Collect all .cnf files under benchmarks/sat/ recursively.
    // Skip .xz files (decompression is slow).
    let mut all_cnf = Vec::new();
    collect_cnf_files(&root.join("benchmarks/sat"), &mut all_cnf);

    let mut sat_verified = 0usize;
    let mut unsat_count = 0usize;
    let mut timeouts = 0usize;
    let mut errors = Vec::new();

    for path in &all_cnf {
        let label = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .display()
            .to_string();

        let cnf = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue, // skip unreadable files
        };

        let formula = match ay_sat::parse_dimacs(&cnf) {
            Ok(f) => f,
            Err(_) => continue, // skip unparseable files
        };

        let original_clauses = formula.clauses.clone();
        let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
        let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
        for clause in &original_clauses {
            solver.add_clause(clause.clone());
        }

        let started = Instant::now();
        let timeout = std::time::Duration::from_secs(10);
        let result = solver
            .solve_interruptible(|| started.elapsed() >= timeout)
            .into_inner();

        match &result {
            SatResult::Sat(model) => {
                if let Some(ci) = find_violated_clause(&original_clauses, model) {
                    errors.push(format!(
                        "SOUNDNESS BUG: [{label}] SAT model violates clause {ci}"
                    ));
                } else {
                    sat_verified += 1;
                }
            }
            SatResult::Unsat(_) => {
                // Verify the DRAT proof for every UNSAT result.
                if let Some(writer) = solver.take_proof_writer() {
                    let proof_bytes = writer.into_vec().expect("proof writer flush");
                    let check_result =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            verify_drat_proof_native(
                                formula.num_vars,
                                &original_clauses,
                                &proof_bytes,
                                &label,
                            );
                        }));
                    if let Err(e) = check_result {
                        let msg = if let Some(s) = e.downcast_ref::<String>() {
                            s.clone()
                        } else {
                            format!("{label}: DRAT verification panicked")
                        };
                        errors.push(msg);
                    }
                }
                unsat_count += 1;
            }
            SatResult::Unknown => {
                timeouts += 1;
            }
            _ => unreachable!(),
        }
    }

    eprintln!(
        "All benchmark .cnf files: {} SAT verified, {} UNSAT, {} timeouts, {} errors (of {})",
        sat_verified,
        unsat_count,
        timeouts,
        errors.len(),
        all_cnf.len()
    );

    assert!(
        errors.is_empty(),
        "SOUNDNESS BUGS found in benchmark .cnf files:\n{}",
        errors.join("\n")
    );
}

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
