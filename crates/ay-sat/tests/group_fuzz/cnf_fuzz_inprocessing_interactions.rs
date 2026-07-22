// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF-fuzz test for BVE GC assertion with mixed clause lengths and all
//! inprocessing enabled (Part of #8483).
//!
//! The assertion at bve/body.rs checks that no active clause contains an
//! eliminated variable after BVE garbage collection. This test generates
//! random formulas with mixed clause lengths (2-5 literals) and solves them
//! with all inprocessing techniques enabled, targeting the interaction
//! between BVE and other techniques (subsumption, vivification, etc.).

#![allow(clippy::panic)]

use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;

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

    fn next_range(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next_bounded(hi - lo + 1)
    }
}

// ---------------------------------------------------------------------------
// Random CNF formula generation with mixed clause lengths
// ---------------------------------------------------------------------------

/// Generate a random CNF formula with mixed clause lengths (2-5 literals).
/// This is the key trigger: mixed lengths create BVE resolvents of varying
/// sizes that interact differently with subsumption and other techniques.
fn generate_mixed_cnf(rng: &mut Rng, num_vars: u32, num_clauses: usize) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        // Mixed clause lengths: 2-5 literals
        let clause_len = rng.next_range(2, 5) as usize;
        let mut clause = Vec::with_capacity(clause_len);
        for _ in 0..clause_len {
            let var = rng.next_bounded(u64::from(num_vars)) as u32;
            let positive = rng.next_bounded(2) == 0;
            let lit = if positive {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            // Skip duplicate variables in the same clause
            if !clause
                .iter()
                .any(|l: &Literal| l.variable() == lit.variable())
            {
                clause.push(lit);
            }
        }
        if !clause.is_empty() {
            clauses.push(clause);
        }
    }
    clauses
}

// ---------------------------------------------------------------------------
// Solver configurations
// ---------------------------------------------------------------------------

/// Solve with ALL inprocessing techniques enabled (default + explicit enables).
fn solve_all_inprocessing(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    // Explicitly enable all inprocessing techniques
    solver.set_bve_enabled(true);
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    solver.set_probe_enabled(true);
    solver.set_bce_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_factor_enabled(true);
    solver.set_transred_enabled(true);
    solver.set_htr_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_condition_enabled(true);
    solver.set_backbone_enabled(true);
    solver.set_cce_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

/// Solve with all inprocessing disabled (pure CDCL baseline).
fn solve_baseline(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

/// Verify that a model satisfies all clauses.
fn verify_model(clauses: &[Vec<Literal>], model: &[bool]) -> bool {
    for clause in clauses {
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
            return false;
        }
    }
    true
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
// Core fuzz loop
// ---------------------------------------------------------------------------

fn fuzz_mixed_clause_inprocessing(
    seed: u64,
    count: usize,
    min_vars: u64,
    max_vars: u64,
    min_clauses: u64,
    max_clauses: u64,
) {
    let mut rng = Rng::new(seed);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..count {
        let num_vars = rng.next_range(min_vars, max_vars) as u32;
        let num_clauses = rng.next_range(min_clauses, max_clauses) as usize;
        let clauses = generate_mixed_cnf(&mut rng, num_vars, num_clauses);
        let nv = num_vars as usize;

        // Config A: all inprocessing enabled
        let result_all = solve_all_inprocessing(nv, &clauses);
        let verdict_all = classify(&result_all);

        // Config B: baseline (no inprocessing)
        let result_base = solve_baseline(nv, &clauses);
        let verdict_base = classify(&result_base);

        // Verify SAT models
        if let SatResult::Sat(ref model) = result_all {
            assert!(
                verify_model(&clauses, model),
                "SOUNDNESS BUG: all-inprocessing config model is invalid \
                 [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
            );
        }
        if let SatResult::Sat(ref model) = result_base {
            assert!(
                verify_model(&clauses, model),
                "SOUNDNESS BUG: baseline config model is invalid \
                 [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
            );
        }

        // Differential comparison
        if verdict_all != Verdict::Unknown && verdict_base != Verdict::Unknown {
            assert_eq!(
                verdict_all, verdict_base,
                "DISAGREEMENT: all-inprocessing={verdict_all:?} vs baseline={verdict_base:?} \
                 [seed={seed}, formula={i}, vars={num_vars}, clauses={num_clauses}]"
            );
        }

        match verdict_all {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!(
        "cnf-fuzz mixed-clause inprocessing (seed={seed:#x}): {count} formulas, \
         {sat_count} SAT, {unsat_count} UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Test entry points
// ---------------------------------------------------------------------------

/// Small mixed-clause formulas: 5-15 vars, 10-40 clauses, 1000 instances.
/// This is the primary regression test for #8483.
///
/// Regression (wf_ff5991a1 Defect 1): this test and `_dense` caught the
/// congruence complementary-contradiction-edge ICE — merge_or_contradict
/// records the contradicting pair (x, ¬x) as an equivalence edge, whose
/// binaries degenerate to duplicate-literal units and tripped the
/// duplicate-watch debug_assert in clause_add. Fixed by skipping
/// complementary edges at all emission sites (solver/inprocessing/congruence/
/// mod.rs, proof_ladder.rs) and in forward subsumption's UF build.
#[test]
#[timeout(300_000)]
fn cnf_fuzz_inprocessing_mixed_small() {
    fuzz_mixed_clause_inprocessing(0xDEAD_8483_0001, 1000, 5, 15, 10, 40);
}

/// Medium mixed-clause formulas: 10-25 vars, 20-60 clauses, 1000 instances.
#[test]
#[timeout(300_000)]
fn cnf_fuzz_inprocessing_mixed_medium() {
    fuzz_mixed_clause_inprocessing(0xDEAD_8483_0002, 1000, 10, 25, 20, 60);
}

/// Dense mixed-clause formulas: 8-12 vars, 30-80 clauses, 1000 instances.
/// High clause/variable ratio stresses BVE with many elimination candidates.
/// Also a regression witness for the congruence complementary-edge ICE —
/// see `cnf_fuzz_inprocessing_mixed_small` (wf_ff5991a1 Defect 1).
#[test]
#[timeout(300_000)]
fn cnf_fuzz_inprocessing_mixed_dense() {
    fuzz_mixed_clause_inprocessing(0xDEAD_8483_0003, 1000, 8, 12, 30, 80);
}

/// Sparse mixed-clause formulas: 15-30 vars, 10-30 clauses, 1000 instances.
/// Low clause/variable ratio produces mostly SAT, testing reconstruction.
#[test]
#[timeout(300_000)]
fn cnf_fuzz_inprocessing_mixed_sparse() {
    fuzz_mixed_clause_inprocessing(0xDEAD_8483_0004, 1000, 15, 30, 10, 30);
}
