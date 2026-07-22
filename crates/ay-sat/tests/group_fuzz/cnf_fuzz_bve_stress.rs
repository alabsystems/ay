// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE stress differential tests targeting known corner cases (Part of #7927).
//!
//! This file adds targeted fuzz tests for BVE (bounded variable elimination)
//! patterns that have historically caused soundness bugs:
//!
//! - **Gate-structured formulas** (#7916): BVE drops gate-defining clauses
//! - **Growth guard stress** (#7900): High-occurrence variables cause
//!   resolution explosion that the growth guard must handle correctly
//! - **BVE + CCE interaction**: Covered clause elimination modifies the
//!   clause database before/during BVE
//! - **BVE preprocessing vs inprocessing**: Different code paths for the
//!   same BVE algorithm must agree
//! - **Resolution explosion**: Variables with many positive AND many negative
//!   occurrences stress resolvent generation
//!
//! Each test generates 200 random formulas with a seeded PRNG, solves with
//! BVE-enabled and no-inprocessing configurations, and verifies that:
//! 1. SAT/UNSAT verdicts agree (when both are decidable)
//! 2. SAT models satisfy all original clauses

#![allow(clippy::panic)]

use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;

// ---------------------------------------------------------------------------
// SplitMix64 PRNG (same as cnf_fuzz_bve_differential.rs)
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
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
// Random CNF formula generation
// ---------------------------------------------------------------------------

fn generate_random_cnf(
    rng: &mut Rng,
    num_vars: u32,
    num_clauses: usize,
    max_clause_len: usize,
) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let clause_len = rng.next_range(1, max_clause_len as u64) as usize;
        let mut clause = Vec::with_capacity(clause_len);
        for _ in 0..clause_len {
            let var = rng.next_bounded(u64::from(num_vars)) as u32;
            let positive = rng.next_bounded(2) == 0;
            let lit = if positive {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
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

fn solve_default(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

fn solve_no_inprocessing(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

fn solve_bve_with_preprocessing(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

fn solve_bve_inprocessing_only(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

fn solve_bve_plus_cce(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_bve_enabled(true);
    solver.set_cce_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

// ---------------------------------------------------------------------------
// Helpers
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

/// Verify SAT model and check verdict agreement.
fn check_results(
    label: &str,
    clauses: &[Vec<Literal>],
    result_a: &SatResult,
    result_b: &SatResult,
    label_a: &str,
    label_b: &str,
    context: &str,
) {
    if let SatResult::Sat(ref model) = result_a {
        if let Some(ci) = find_violated_clause(clauses, model) {
            panic!("{label}: {label_a} model violates clause {ci} [{context}]");
        }
    }
    if let SatResult::Sat(ref model) = result_b {
        if let Some(ci) = find_violated_clause(clauses, model) {
            panic!("{label}: {label_b} model violates clause {ci} [{context}]");
        }
    }

    let v_a = classify(result_a);
    let v_b = classify(result_b);
    if v_a != Verdict::Unknown && v_b != Verdict::Unknown {
        assert_eq!(
            v_a, v_b,
            "{label}: {label_a}={v_a:?} vs {label_b}={v_b:?} [{context}]"
        );
    }
}

// ===========================================================================
// Test 1: BVE preprocessing vs inprocessing
// ===========================================================================

/// Differential: BVE during preprocessing vs BVE during inprocessing only.
/// Both paths must agree on SAT/UNSAT and produce valid models.
///
/// Catches bugs where preprocessing BVE applies elimination in a different
/// order or with different growth bounds than inprocessing BVE.
#[test]
#[timeout(180_000)]
fn differential_bve_preprocess_vs_inprocess() {
    let mut rng = Rng::new(0xDEAD_BEEF_7927_0101);

    for i in 0..200 {
        let num_vars = rng.next_range(10, 30) as u32;
        let num_clauses = rng.next_range(30, 100) as usize;
        let clauses = generate_random_cnf(&mut rng, num_vars, num_clauses, 4);
        let nv = num_vars as usize;

        let result_preproc = solve_bve_with_preprocessing(nv, &clauses);
        let result_inproc = solve_bve_inprocessing_only(nv, &clauses);

        check_results(
            "BVE-PREPROC-VS-INPROC",
            &clauses,
            &result_preproc,
            &result_inproc,
            "preproc",
            "inproc",
            &format!("formula={i}, vars={num_vars}, clauses={num_clauses}"),
        );
    }

    eprintln!("differential_bve_preprocess_vs_inprocess: 200 formulas compared");
}

// ===========================================================================
// Test 2: BVE + CCE interaction
// ===========================================================================

/// Differential: BVE+CCE vs no-inprocessing baseline. CCE was missing from
/// the existing fuzz tests. This catches any interaction between covered
/// clause elimination and bounded variable elimination.
#[test]
#[timeout(180_000)]
fn differential_bve_plus_cce() {
    let mut rng = Rng::new(0xDEAD_BEEF_7927_CCE1);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..200 {
        let num_vars = rng.next_range(10, 35) as u32;
        let num_clauses = rng.next_range(25, 100) as usize;
        let clauses = generate_random_cnf(&mut rng, num_vars, num_clauses, 4);
        let nv = num_vars as usize;

        let result_bve_cce = solve_bve_plus_cce(nv, &clauses);
        let result_base = solve_no_inprocessing(nv, &clauses);

        check_results(
            "BVE+CCE",
            &clauses,
            &result_bve_cce,
            &result_base,
            "bve+cce",
            "baseline",
            &format!("formula={i}, vars={num_vars}, clauses={num_clauses}"),
        );

        match classify(&result_bve_cce) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!("differential_bve_plus_cce: 200 formulas, {sat_count} SAT, {unsat_count} UNSAT");
}

// ===========================================================================
// Test 3: Gate-structured formulas (#7916)
// ===========================================================================

/// Generate a CNF with explicit gate structure. Gate clauses are the pattern
/// where BVE soundness bugs (like #7916) manifest: a gate variable `g` is
/// defined by clauses encoding `g <=> (a AND b)`, and BVE must not drop
/// gate-defining clauses during elimination.
fn generate_gate_structured_cnf(
    rng: &mut Rng,
    num_input_vars: u32,
    num_gates: u32,
) -> (u32, Vec<Vec<Literal>>) {
    let total_vars = num_input_vars + num_gates;
    let mut clauses = Vec::new();

    for g in 0..num_gates {
        let gate_var = num_input_vars + g;
        let input_a = rng.next_bounded(u64::from(num_input_vars)) as u32;
        let mut input_b = rng.next_bounded(u64::from(num_input_vars)) as u32;
        if input_b == input_a {
            input_b = (input_a + 1) % num_input_vars;
        }

        let g_pos = Literal::positive(Variable::new(gate_var));
        let g_neg = Literal::negative(Variable::new(gate_var));
        let a_pos = Literal::positive(Variable::new(input_a));
        let a_neg = Literal::negative(Variable::new(input_a));
        let b_pos = Literal::positive(Variable::new(input_b));
        let b_neg = Literal::negative(Variable::new(input_b));

        // g => (a OR b): (-g OR a OR b)
        clauses.push(vec![g_neg, a_pos, b_pos]);
        // (a AND b) => g: (-a OR g) AND (-b OR g)
        clauses.push(vec![a_neg, g_pos]);
        clauses.push(vec![b_neg, g_pos]);
    }

    // Random clauses connecting gate outputs
    let num_random = rng.next_range(u64::from(num_gates), u64::from(num_gates * 3)) as usize;
    for _ in 0..num_random {
        let clause_len = rng.next_range(2, 4) as usize;
        let mut clause = Vec::with_capacity(clause_len);
        for _ in 0..clause_len {
            let var = rng.next_bounded(u64::from(total_vars)) as u32;
            let positive = rng.next_bounded(2) == 0;
            let lit = if positive {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
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

    (total_vars, clauses)
}

/// Differential fuzz on gate-structured formulas. Targets #7916 bug pattern.
#[test]
#[timeout(180_000)]
fn differential_bve_gate_structured() {
    let mut rng = Rng::new(0xDEAD_BEEF_7927_6A7E);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..200 {
        let num_inputs = rng.next_range(5, 15) as u32;
        let num_gates = rng.next_range(3, 10) as u32;
        let (total_vars, clauses) = generate_gate_structured_cnf(&mut rng, num_inputs, num_gates);
        let nv = total_vars as usize;

        let result_bve = solve_default(nv, &clauses);
        let result_base = solve_no_inprocessing(nv, &clauses);

        check_results(
            "GATE-BVE",
            &clauses,
            &result_bve,
            &result_base,
            "bve",
            "baseline",
            &format!("formula={i}, inputs={num_inputs}, gates={num_gates}"),
        );

        match classify(&result_bve) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!(
        "differential_bve_gate_structured: 200 formulas, {sat_count} SAT, {unsat_count} UNSAT",
    );
}

// ===========================================================================
// Test 4: High variable-occurrence density (#7900 growth guard)
// ===========================================================================

/// Generate formulas where some variables appear in many clauses.
fn generate_high_occurrence_cnf(
    rng: &mut Rng,
    num_vars: u32,
    num_clauses: usize,
    hot_vars: u32,
) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::with_capacity(num_clauses);

    for _ in 0..num_clauses {
        let clause_len = rng.next_range(2, 5) as usize;
        let mut clause = Vec::with_capacity(clause_len);

        // First literal biased toward hot variables (70% chance)
        let first_var = if rng.next_bounded(10) < 7 {
            rng.next_bounded(u64::from(hot_vars)) as u32
        } else {
            rng.next_bounded(u64::from(num_vars)) as u32
        };
        let positive = rng.next_bounded(2) == 0;
        clause.push(if positive {
            Literal::positive(Variable::new(first_var))
        } else {
            Literal::negative(Variable::new(first_var))
        });

        for _ in 1..clause_len {
            let var = rng.next_bounded(u64::from(num_vars)) as u32;
            let pos = rng.next_bounded(2) == 0;
            let lit = if pos {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
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

/// Differential fuzz with high-occurrence formulas. Tests the BVE growth
/// guard (#7900) on formulas where hot variables have many occurrences.
#[test]
#[timeout(180_000)]
fn differential_bve_high_occurrence() {
    let mut rng = Rng::new(0xDEAD_BEEF_7927_0C01);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..200 {
        let num_vars = rng.next_range(8, 25) as u32;
        let num_clauses = rng.next_range(20, 80) as usize;
        let hot_vars = rng.next_range(2, 4.min(u64::from(num_vars))) as u32;
        let clauses = generate_high_occurrence_cnf(&mut rng, num_vars, num_clauses, hot_vars);
        let nv = num_vars as usize;

        let result_bve = solve_default(nv, &clauses);
        let result_base = solve_no_inprocessing(nv, &clauses);

        check_results(
            "HIGH-OCC-BVE",
            &clauses,
            &result_bve,
            &result_base,
            "bve",
            "baseline",
            &format!("formula={i}, vars={num_vars}, clauses={num_clauses}, hot={hot_vars}"),
        );

        match classify(&result_bve) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!(
        "differential_bve_high_occurrence: 200 formulas, {sat_count} SAT, {unsat_count} UNSAT",
    );
}

// ===========================================================================
// Test 5: Resolution explosion
// ===========================================================================

/// Generate formulas with a target variable having many positive AND many
/// negative occurrences, creating a resolution-explosion scenario.
fn generate_resolution_explosion_cnf(
    rng: &mut Rng,
    num_vars: u32,
    target_var: u32,
    pos_occs: usize,
    neg_occs: usize,
    extra_clauses: usize,
) -> Vec<Vec<Literal>> {
    let mut clauses = Vec::new();
    let target_pos = Literal::positive(Variable::new(target_var));
    let target_neg = Literal::negative(Variable::new(target_var));

    for _ in 0..pos_occs {
        let clause_len = rng.next_range(2, 4) as usize;
        let mut clause = vec![target_pos];
        for _ in 1..clause_len {
            let var = loop {
                let v = rng.next_bounded(u64::from(num_vars)) as u32;
                if v != target_var {
                    break v;
                }
            };
            let pos = rng.next_bounded(2) == 0;
            let lit = if pos {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            if !clause
                .iter()
                .any(|l: &Literal| l.variable() == lit.variable())
            {
                clause.push(lit);
            }
        }
        clauses.push(clause);
    }

    for _ in 0..neg_occs {
        let clause_len = rng.next_range(2, 4) as usize;
        let mut clause = vec![target_neg];
        for _ in 1..clause_len {
            let var = loop {
                let v = rng.next_bounded(u64::from(num_vars)) as u32;
                if v != target_var {
                    break v;
                }
            };
            let pos = rng.next_bounded(2) == 0;
            let lit = if pos {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
            if !clause
                .iter()
                .any(|l: &Literal| l.variable() == lit.variable())
            {
                clause.push(lit);
            }
        }
        clauses.push(clause);
    }

    for _ in 0..extra_clauses {
        let clause_len = rng.next_range(2, 4) as usize;
        let mut clause = Vec::with_capacity(clause_len);
        for _ in 0..clause_len {
            let var = rng.next_bounded(u64::from(num_vars)) as u32;
            let pos = rng.next_bounded(2) == 0;
            let lit = if pos {
                Literal::positive(Variable::new(var))
            } else {
                Literal::negative(Variable::new(var))
            };
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

/// Differential fuzz with resolution-explosion patterns. The target variable
/// has 3-6 positive and 3-6 negative occurrences, creating 9-36 potential
/// resolvents. BVE must handle this correctly: either the growth guard
/// rejects elimination, or all resolvents are added.
#[test]
#[timeout(180_000)]
fn differential_bve_resolution_explosion() {
    let mut rng = Rng::new(0xDEAD_BEEF_7927_0E50);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..200 {
        let num_vars = rng.next_range(10, 25) as u32;
        let target_var = rng.next_bounded(u64::from(num_vars)) as u32;
        let pos_occs = rng.next_range(3, 6) as usize;
        let neg_occs = rng.next_range(3, 6) as usize;
        let extra = rng.next_range(10, 40) as usize;

        let clauses = generate_resolution_explosion_cnf(
            &mut rng, num_vars, target_var, pos_occs, neg_occs, extra,
        );
        let nv = num_vars as usize;

        let result_bve = solve_default(nv, &clauses);
        let result_base = solve_no_inprocessing(nv, &clauses);

        check_results(
            "RES-EXPLOSION-BVE",
            &clauses,
            &result_bve,
            &result_base,
            "bve",
            "baseline",
            &format!(
                "formula={i}, vars={num_vars}, target={target_var}, \
                 pos_occs={pos_occs}, neg_occs={neg_occs}"
            ),
        );

        match classify(&result_bve) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!(
        "differential_bve_resolution_explosion: 200 formulas, {sat_count} SAT, {unsat_count} UNSAT",
    );
}
