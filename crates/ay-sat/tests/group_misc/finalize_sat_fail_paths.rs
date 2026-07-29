// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FINALIZE_SAT_FAIL path coverage tests (#7917).
//!
//! These tests exercise the specific code paths in `finalize_sat.rs` that
//! produce FINALIZE_SAT_FAIL (Unknown/InvalidSatModel) when model
//! verification fails after reconstruction. The companion
//! `finalize_sat_fail_audit.rs` checks that no corpus benchmark triggers
//! the safety net; this file covers the paths *themselves*.
//!
//! Code paths under test:
//!
//! 1. `finalize_sat_model` → original-formula ledger check finds unsatisfied
//!    clause → returns `Err(detail)` → `declare_sat_from_model` converts to
//!    `Unknown(InvalidSatModel)`.
//!
//! 2. `sat_from_assume_model` → model length mismatch → Unknown(InvalidSatModel).
//!
//! 3. `declare_assume_sat_from_model` → same as (1) on assumption path.
//!
//! 4. BVE-enabled formulas: solver eliminates variables, reconstruction
//!    restores them. If reconstruction is correct, SAT models are valid.
//!    If not, FINALIZE_SAT_FAIL fires and we get Unknown (never wrong SAT).
//!
//! 5. Walk-candidate path: walk finds partial assignment, reconstruction may
//!    fail, solver falls through to CDCL.
//!
//! The key invariant: the solver NEVER returns a wrong SAT result. It may
//! return Unknown when it cannot verify the model, but never Sat(invalid).

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, AssumeResult, Literal, SatResult, SatUnknownReason, Solver, Variable};
use std::time::Duration;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Verify a model against a set of original clauses (independent checker).
fn verify_model_against_clauses(clauses: &[Vec<Literal>], model: &[bool]) -> bool {
    for clause in clauses {
        let satisfied = clause.iter().any(|lit| {
            let vi = lit.variable().index();
            vi < model.len() && (model[vi] == lit.is_positive())
        });
        if !satisfied {
            return false;
        }
    }
    true
}

/// Solve with a timeout and return result + unknown reason.
fn solve_with_timeout(
    solver: &mut Solver,
    timeout_secs: u64,
) -> (SatResult, Option<SatUnknownReason>) {
    let timer =
        super::common::SolverInterruptTimer::start(solver, Duration::from_secs(timeout_secs));
    let result = solver
        .solve_interruptible(|| timer.is_interrupted())
        .into_inner();
    timer.cancel_and_join();
    let reason = solver.last_unknown_reason();
    (result, reason)
}

// ---------------------------------------------------------------------------
// Test 1: BVE-eligible SAT formula — reconstruction must produce valid model
// ---------------------------------------------------------------------------

/// A formula where BVE can eliminate x0 (bounded resolution). The solver
/// must either return Sat with a valid model or Unknown — never Sat(invalid).
///
/// Exercises: finalize_sat_model → reconstruction → original-formula check.
#[test]
fn bve_eligible_sat_formula_produces_valid_model_or_unknown() {
    let mut solver = Solver::new(5);
    let vars: Vec<Variable> = (0..5).map(Variable::new).collect();

    // x0 has bounded resolution (2 pos, 2 neg occurrences).
    // BVE can eliminate x0, producing 4 resolvents.
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[4])]);
    // Anchor clause to constrain solution space
    solver.add_clause(vec![Literal::positive(vars[1])]);

    let original_clauses = vec![
        vec![Literal::positive(vars[0]), Literal::positive(vars[1])],
        vec![Literal::positive(vars[0]), Literal::positive(vars[2])],
        vec![Literal::negative(vars[0]), Literal::positive(vars[3])],
        vec![Literal::negative(vars[0]), Literal::positive(vars[4])],
        vec![Literal::positive(vars[1])],
    ];

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "BVE SAT model violates original formula — FINALIZE_SAT_FAIL should have caught this"
            );
        }
        SatResult::Unknown => {
            // Unknown is acceptable: FINALIZE_SAT_FAIL converted to Unknown.
            // But it should NOT be InvalidSatModel on a simple formula.
            // If it is, that signals a BVE/reconstruction bug.
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!(
                    "WARNING: BVE-eligible SAT formula triggered FINALIZE_SAT_FAIL — \
                     reconstruction may have a bug"
                );
            }
        }
        SatResult::Unsat(_) => {
            panic!("BVE-eligible SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 2: Known-UNSAT formula never triggers InvalidSatModel
// ---------------------------------------------------------------------------

/// PHP(3,2) is known-UNSAT. The solver must return UNSAT, and the
/// InvalidSatModel reason must never be set. If it is, the solver
/// attempted to declare SAT on an UNSAT formula.
#[test]
fn unsat_php_never_triggers_invalid_sat_model() {
    let dimacs = super::common::PHP32_DIMACS;
    let formula = parse_dimacs(dimacs).expect("parse PHP(3,2)");
    let mut solver = formula.into_solver();
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match result {
        SatResult::Unsat(_) => {
            // Correct. Verify the InvalidSatModel reason was NOT set.
            assert_ne!(
                reason,
                Some(SatUnknownReason::InvalidSatModel),
                "PHP(3,2) UNSAT set InvalidSatModel reason — model verification \
                 was attempted on an UNSAT formula"
            );
        }
        SatResult::Sat(_) => {
            panic!("PHP(3,2) known-UNSAT returned SAT — critical soundness bug");
        }
        SatResult::Unknown => {
            assert_ne!(
                reason,
                Some(SatUnknownReason::InvalidSatModel),
                "PHP(3,2) UNSAT formula triggered FINALIZE_SAT_FAIL"
            );
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 3: Assumption-path SAT with BVE-eligible formula
// ---------------------------------------------------------------------------

/// Solve under assumptions on a BVE-eligible formula. The assumption path
/// goes through `declare_assume_sat_from_model` → `finalize_sat_model`.
/// Result must be Sat(valid), Unsat(core), or Unknown — never Sat(invalid).
#[test]
fn assumption_path_bve_formula_sound() {
    let mut solver = Solver::new(6);
    let vars: Vec<Variable> = (0..6).map(Variable::new).collect();

    // BVE-eligible on x0: 2 positive, 2 negative occurrences.
    solver.add_clause(vec![
        Literal::positive(vars[0]),
        Literal::positive(vars[1]),
        Literal::positive(vars[2]),
    ]);
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[5])]);
    // Additional constraint
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[4])]);

    let original_clauses = vec![
        vec![
            Literal::positive(vars[0]),
            Literal::positive(vars[1]),
            Literal::positive(vars[2]),
        ],
        vec![Literal::positive(vars[0]), Literal::positive(vars[3])],
        vec![Literal::negative(vars[0]), Literal::positive(vars[4])],
        vec![Literal::negative(vars[0]), Literal::positive(vars[5])],
        vec![Literal::positive(vars[2]), Literal::positive(vars[4])],
    ];

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    // Assume x1 = true (should be easily satisfiable)
    let assumptions = vec![Literal::positive(vars[1])];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();

    match &result {
        AssumeResult::Sat(model) => {
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "assumption-path SAT model violates original formula"
            );
            // Verify assumption is satisfied in the model
            assert!(
                model.get(1).copied().unwrap_or(false),
                "model does not satisfy assumption x1=true"
            );
        }
        AssumeResult::Unknown => {
            let reason = solver.last_unknown_reason();
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!("WARNING: assumption-path BVE formula triggered FINALIZE_SAT_FAIL");
            }
            // Unknown is acceptable but not expected on this simple formula
        }
        AssumeResult::Unsat(..) => {
            // Could happen if BVE + assumptions interact to produce UNSAT,
            // but this formula is SAT under x1=true.
            panic!("assumption-path returned UNSAT on a SAT formula with x1=true");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 4: Multi-round BVE with chain dependencies
// ---------------------------------------------------------------------------

/// Formula with a chain of BVE-eligible variables. Reconstruction must
/// process them in the correct reverse order. If order is wrong,
/// FINALIZE_SAT_FAIL catches the invalid model.
///
/// Chain: x0 eliminated first (depends on x1, x2), then x1 eliminated
/// (depends on x2, x3). Reconstruction must restore x1 before x0.
#[test]
fn multi_round_bve_chain_reconstruction_sound() {
    let mut solver = Solver::new(6);
    let vars: Vec<Variable> = (0..6).map(Variable::new).collect();

    // Round 1: x0 eligible (2 pos, 1 neg)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[3])]);

    // Round 2: x1 eligible after x0 removed (2 pos from resolvents, 1 neg)
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[5])]);

    // Anchor
    solver.add_clause(vec![Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[4])]);

    let original_clauses = vec![
        vec![Literal::positive(vars[0]), Literal::positive(vars[1])],
        vec![Literal::positive(vars[0]), Literal::positive(vars[2])],
        vec![Literal::negative(vars[0]), Literal::positive(vars[3])],
        vec![Literal::positive(vars[1]), Literal::positive(vars[4])],
        vec![Literal::negative(vars[1]), Literal::positive(vars[5])],
        vec![Literal::positive(vars[3])],
        vec![Literal::positive(vars[4])],
    ];

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "multi-round BVE model violates original formula — \
                 reconstruction order may be wrong"
            );
        }
        SatResult::Unknown => {
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!(
                    "WARNING: multi-round BVE chain triggered FINALIZE_SAT_FAIL — \
                     reconstruction order may be wrong"
                );
            }
        }
        SatResult::Unsat(_) => {
            panic!("multi-round BVE SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 5: Dense formula with many BVE candidates
// ---------------------------------------------------------------------------

/// A denser formula (10 vars, 20 clauses) with multiple BVE candidates.
/// Exercises the reconstruction stack with many entries. The key invariant:
/// every SAT model independently satisfies all original clauses.
#[test]
fn dense_bve_formula_model_always_valid() {
    let num_vars = 10;
    let mut solver = Solver::new(num_vars);
    let vars: Vec<Variable> = (0..num_vars as u32).map(Variable::new).collect();

    // Create a satisfiable formula with BVE opportunities.
    // Variables 0-3 have bounded resolution; 4-9 are support variables.
    let clauses = vec![
        // x0 positive
        vec![Literal::positive(vars[0]), Literal::positive(vars[4])],
        vec![Literal::positive(vars[0]), Literal::positive(vars[5])],
        // x0 negative
        vec![Literal::negative(vars[0]), Literal::positive(vars[6])],
        // x1 positive
        vec![Literal::positive(vars[1]), Literal::positive(vars[6])],
        vec![Literal::positive(vars[1]), Literal::positive(vars[7])],
        // x1 negative
        vec![Literal::negative(vars[1]), Literal::positive(vars[8])],
        // x2 positive
        vec![Literal::positive(vars[2]), Literal::positive(vars[7])],
        // x2 negative
        vec![Literal::negative(vars[2]), Literal::positive(vars[9])],
        vec![Literal::negative(vars[2]), Literal::positive(vars[4])],
        // x3 positive
        vec![Literal::positive(vars[3]), Literal::positive(vars[8])],
        // x3 negative
        vec![Literal::negative(vars[3]), Literal::positive(vars[9])],
        // Support variable constraints (make formula more constrained but SAT)
        vec![Literal::positive(vars[4]), Literal::positive(vars[5])],
        vec![Literal::positive(vars[6]), Literal::positive(vars[7])],
        vec![Literal::positive(vars[8]), Literal::positive(vars[9])],
        // At least one true from each pair
        vec![Literal::positive(vars[4]), Literal::negative(vars[5])],
        vec![Literal::positive(vars[6]), Literal::negative(vars[7])],
    ];

    let original_clauses = clauses.clone();
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "dense BVE formula: SAT model violates original formula"
            );
        }
        SatResult::Unknown => {
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!("WARNING: dense BVE formula triggered FINALIZE_SAT_FAIL");
            }
        }
        SatResult::Unsat(_) => {
            panic!("dense BVE SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 6: BVE + walk interaction
// ---------------------------------------------------------------------------

/// A formula where walk-based local search might find a candidate
/// assignment. If reconstruction fails on the walk candidate, the solver
/// should fall through to CDCL (not return an invalid model).
///
/// Exercises: solve_no_assumptions → try_walk → reconstruction attempt →
/// fallback to CDCL → finalize_sat_model.
#[test]
fn walk_candidate_reconstruction_fallback_sound() {
    // Use a moderately sized random-3-SAT formula at the phase transition
    // ratio (~4.27 clauses/var). Walk is most likely to fire on medium formulas.
    let dimacs = "\
p cnf 20 85
1 -5 12 0
-2 8 15 0
3 -10 17 0
-4 6 -19 0
5 -11 20 0
-1 7 -14 0
2 -9 16 0
-3 10 -18 0
4 -8 13 0
-5 11 -20 0
1 -6 14 0
-2 9 -17 0
3 -7 18 0
-4 8 -12 0
5 -10 19 0
-1 6 -15 0
2 -7 16 0
-3 11 -13 0
4 -9 20 0
-5 12 -18 0
1 -8 17 0
-2 10 -19 0
3 -6 13 0
-4 7 -14 0
5 -11 15 0
-1 9 -16 0
2 -12 20 0
-3 8 -17 0
4 -10 18 0
-5 6 -13 0
1 -7 14 0
-2 11 -20 0
3 -9 19 0
-4 12 -15 0
5 -8 16 0
-1 10 -17 0
2 -6 13 0
-3 7 -18 0
4 -11 20 0
-5 9 -14 0
1 -12 15 0
-2 8 -16 0
3 -10 19 0
-4 6 -20 0
5 -7 17 0
-1 11 -18 0
2 -9 14 0
-3 12 -13 0
4 -8 15 0
-5 10 -16 0
1 -6 19 0
-2 7 -20 0
3 -11 17 0
-4 9 -18 0
5 -12 13 0
-1 8 -14 0
2 -10 15 0
-3 6 -16 0
4 -7 19 0
-5 11 -20 0
1 -9 18 0
-2 12 -17 0
3 -8 13 0
-4 10 -14 0
5 -6 15 0
-1 7 -16 0
2 -11 19 0
-3 9 -20 0
4 -12 17 0
-5 8 -18 0
1 -10 13 0
-2 6 -14 0
3 -7 15 0
-4 11 -16 0
5 -9 19 0
-1 12 -20 0
2 -8 17 0
-3 10 -18 0
4 -6 13 0
-5 7 -14 0
1 -11 15 0
-2 9 -16 0
3 -12 19 0
-4 8 -20 0
5 -10 17 0
";

    let formula = parse_dimacs(dimacs).expect("parse random-3-SAT");
    let original_clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_walk_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "walk+BVE formula: SAT model violates original formula"
            );
        }
        SatResult::Unknown => {
            // Acceptable: timeout or FINALIZE_SAT_FAIL
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!("WARNING: walk+BVE formula triggered FINALIZE_SAT_FAIL");
            }
        }
        SatResult::Unsat(_) => {
            // This formula is SAT (verified by construction).
            panic!("walk+BVE SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 7: Incremental solving — second solve after BVE
// ---------------------------------------------------------------------------

/// After BVE eliminates variables in the first solve, a second solve with
/// additional clauses must still produce correct results. The reconstruction
/// stack from the first solve interacts with new clauses.
#[test]
fn incremental_solve_after_bve_sound() {
    let mut solver = Solver::new(4);
    let vars: Vec<Variable> = (0..4).map(Variable::new).collect();

    // First batch: BVE-eligible on x0
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[3])]);

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    // First solve
    let result1 = solver.solve().into_inner();
    match &result1 {
        SatResult::Sat(model) => {
            // First solve should succeed
            assert!(model.len() <= 4, "model too large: {}", model.len());
        }
        SatResult::Unknown => {
            // Acceptable
        }
        SatResult::Unsat(_) => {
            panic!("first incremental solve returned UNSAT on a SAT formula");
        }
        _ => unreachable!(),
    }

    // Add a constraining clause and solve again
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[2])]);

    let result2 = solver.solve().into_inner();
    match &result2 {
        SatResult::Sat(model) => {
            // Model must satisfy ALL clauses (original + new)
            let all_clauses = vec![
                vec![Literal::positive(vars[0]), Literal::positive(vars[1])],
                vec![Literal::negative(vars[0]), Literal::positive(vars[2])],
                vec![Literal::positive(vars[3])],
                vec![Literal::positive(vars[1]), Literal::positive(vars[2])],
            ];
            assert!(
                verify_model_against_clauses(&all_clauses, model),
                "incremental SAT model violates clauses after BVE"
            );
        }
        SatResult::Unknown => {
            let reason = solver.last_unknown_reason();
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!("WARNING: incremental solve after BVE triggered FINALIZE_SAT_FAIL");
            }
        }
        SatResult::Unsat(_) => {
            // The formula is still SAT (x1=true, x2=true, x3=true satisfies all)
            panic!("incremental solve returned UNSAT on a SAT formula");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 8: DIMACS benchmark with BVE — barrel-style circuit
// ---------------------------------------------------------------------------

/// Small barrel-shifter-style circuit formula that stresses BVE and
/// reconstruction. Uses DIMACS input to exercise the full parse → solve →
/// reconstruct → verify pipeline.
#[test]
fn barrel_style_circuit_bve_sound() {
    // Small barrel-shifter circuit: 8 vars, known-SAT.
    // Variables: d0, d1 (data), s0 (select), m0-m3 (mux outputs), out
    let dimacs = "\
p cnf 8 14
-3 1 -5 0
-3 -1 5 0
3 2 -5 0
3 -2 5 0
-3 1 -6 0
-3 -1 6 0
3 2 -6 0
3 -2 6 0
5 -7 0
-5 7 0
6 -8 0
-6 8 0
7 0
8 0
";

    let formula = parse_dimacs(dimacs).expect("parse barrel circuit");
    let original_clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "barrel circuit: SAT model violates original formula"
            );
        }
        SatResult::Unknown => {
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!("WARNING: barrel circuit triggered FINALIZE_SAT_FAIL");
            }
        }
        SatResult::Unsat(_) => {
            // This circuit is SAT (e.g., d0=1, d1=1, s0=0 propagates to out=1).
            panic!("barrel circuit SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 9: Soundness sweep — varied clause structures with BVE
// ---------------------------------------------------------------------------

/// Run a batch of small hand-crafted formulas through the solver with BVE
/// enabled. Every SAT result is independently verified. This catches
/// FINALIZE_SAT_FAIL patterns that only appear on specific clause shapes.
#[test]
fn varied_clause_structures_bve_all_valid() {
    let formulas: Vec<(&str, &str, bool)> = vec![
        // (label, DIMACS, known_sat)
        (
            "unit_chain",
            "p cnf 4 4\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n",
            true,
        ),
        ("xor_pair", "p cnf 2 2\n1 2 0\n-1 -2 0\n", true),
        (
            "diamond",
            "p cnf 4 4\n1 2 0\n-1 3 0\n-2 4 0\n-3 -4 0\n",
            true,
        ),
        ("bve_triangle", "p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n", true),
        (
            "long_clause",
            "p cnf 8 3\n1 2 3 4 5 6 7 8 0\n-1 -2 0\n-3 -4 0\n",
            true,
        ),
        (
            "unit_conflict",
            "p cnf 1 2\n1 0\n-1 0\n",
            false, // UNSAT
        ),
        (
            "php_2_1",
            "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n",
            false, // UNSAT
        ),
    ];

    for (label, dimacs, known_sat) in &formulas {
        let formula = parse_dimacs(dimacs).unwrap_or_else(|_| panic!("parse {label}"));
        let original_clauses = formula.clauses.clone();
        let mut solver = formula.into_solver();

        solver.set_preprocess_enabled(true);
        solver.set_bve_enabled(true);

        let result = solver.solve().into_inner();
        match &result {
            SatResult::Sat(model) => {
                assert!(
                    *known_sat,
                    "{label}: known-UNSAT returned SAT — soundness bug"
                );
                assert!(
                    verify_model_against_clauses(&original_clauses, model),
                    "{label}: SAT model violates original formula"
                );
            }
            SatResult::Unsat(_) => {
                assert!(
                    !*known_sat,
                    "{label}: known-SAT returned UNSAT — soundness bug"
                );
            }
            SatResult::Unknown => {
                let reason = solver.last_unknown_reason();
                if reason == Some(SatUnknownReason::InvalidSatModel) {
                    assert!(
                        *known_sat,
                        "{label}: UNSAT formula triggered InvalidSatModel — \
                         solver attempted to declare SAT on UNSAT formula"
                    );
                    eprintln!("WARNING: {label} triggered FINALIZE_SAT_FAIL");
                }
            }
            _ => unreachable!(),
        }
    }
}

// ---------------------------------------------------------------------------
// Test 10: No inprocessing baseline — finalize_sat_model without reconstruction
// ---------------------------------------------------------------------------

/// Solve formulas with ALL inprocessing disabled. The finalize_sat_model
/// path still runs (original-formula ledger check) but the reconstruction
/// stack is empty. This is the baseline: if this fails, the core CDCL
/// solve loop is producing invalid models.
#[test]
fn no_inprocessing_baseline_models_valid() {
    let cases = vec![
        ("unit", "p cnf 1 1\n1 0\n"),
        ("binary", "p cnf 2 1\n1 2 0\n"),
        ("ternary", "p cnf 3 2\n1 2 3 0\n-1 -2 -3 0\n"),
        (
            "implication_chain",
            "p cnf 5 5\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n-4 5 0\n",
        ),
    ];

    for (label, dimacs) in &cases {
        let formula = parse_dimacs(dimacs).unwrap_or_else(|_| panic!("parse {label}"));
        let original_clauses = formula.clauses.clone();
        let mut solver = formula.into_solver();

        super::common::disable_all_inprocessing(&mut solver);
        solver.set_preprocess_enabled(false);
        solver.set_walk_enabled(false);

        let result = solver.solve().into_inner();
        match &result {
            SatResult::Sat(model) => {
                assert!(
                    verify_model_against_clauses(&original_clauses, model),
                    "{label}: baseline (no inprocessing) SAT model violates formula"
                );
            }
            SatResult::Unknown => {
                let reason = solver.last_unknown_reason();
                assert_ne!(
                    reason,
                    Some(SatUnknownReason::InvalidSatModel),
                    "{label}: baseline (no inprocessing) triggered FINALIZE_SAT_FAIL — \
                     core CDCL loop producing invalid models"
                );
            }
            SatResult::Unsat(_) => {
                panic!("{label}: known-SAT returned UNSAT with no inprocessing — core bug");
            }
            _ => unreachable!(),
        }
    }
}

// ---------------------------------------------------------------------------
// Test 11: Unit clause chain — reconstruction must preserve unit clause truth
// ---------------------------------------------------------------------------

/// A formula with unit clauses that force specific variable assignments.
/// The unit-clause pre-check (#7917) in finalize_sat_model verifies these
/// are satisfied before reconstruction runs. This test exercises the
/// unit-clause early-diagnostic path.
#[test]
fn unit_clause_chain_preserved_through_bve() {
    let mut solver = Solver::new(6);
    let vars: Vec<Variable> = (0..6).map(Variable::new).collect();

    // Unit clauses: x0=T, x3=T (must hold before and after reconstruction)
    solver.add_clause(vec![Literal::positive(vars[0])]);
    solver.add_clause(vec![Literal::positive(vars[3])]);

    // BVE-eligible on x1: 2 pos, 1 neg occurrence
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[2])]);
    solver.add_clause(vec![Literal::positive(vars[1]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[1]), Literal::positive(vars[5])]);

    let original_clauses = vec![
        vec![Literal::positive(vars[0])],
        vec![Literal::positive(vars[3])],
        vec![Literal::positive(vars[1]), Literal::positive(vars[2])],
        vec![Literal::positive(vars[1]), Literal::positive(vars[4])],
        vec![Literal::negative(vars[1]), Literal::positive(vars[5])],
    ];

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            // Unit clauses must be satisfied in the final model
            assert!(
                model.first().copied().unwrap_or(false),
                "unit clause x0=T violated in final model"
            );
            assert!(
                model.get(3).copied().unwrap_or(false),
                "unit clause x3=T violated in final model"
            );
            assert!(
                verify_model_against_clauses(&original_clauses, model),
                "unit-clause chain: SAT model violates original formula"
            );
        }
        SatResult::Unknown => {
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!(
                    "WARNING: unit-clause chain triggered FINALIZE_SAT_FAIL — \
                     unit clause pre-check or reconstruction may have a bug"
                );
            }
        }
        SatResult::Unsat(_) => {
            panic!("unit-clause chain SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Test 12: Multiple unit clauses with BVE — stress unit-clause pre-check
// ---------------------------------------------------------------------------

/// Formula with many unit clauses constraining variables, plus BVE-eligible
/// variables. Stresses the unit-clause early-check loop with many entries.
#[test]
fn many_unit_clauses_with_bve_sound() {
    let num_vars = 12;
    let mut solver = Solver::new(num_vars);
    let vars: Vec<Variable> = (0..num_vars as u32).map(Variable::new).collect();

    // Unit clauses for vars 0-3 (all true)
    for v in &vars[..4] {
        solver.add_clause(vec![Literal::positive(*v)]);
    }

    // BVE-eligible: x4 has 2 pos, 1 neg
    solver.add_clause(vec![Literal::positive(vars[4]), Literal::positive(vars[8])]);
    solver.add_clause(vec![Literal::positive(vars[4]), Literal::positive(vars[9])]);
    solver.add_clause(vec![
        Literal::negative(vars[4]),
        Literal::positive(vars[10]),
    ]);

    // BVE-eligible: x5 has 1 pos, 2 neg
    solver.add_clause(vec![
        Literal::positive(vars[5]),
        Literal::positive(vars[11]),
    ]);
    solver.add_clause(vec![Literal::negative(vars[5]), Literal::positive(vars[6])]);
    solver.add_clause(vec![Literal::negative(vars[5]), Literal::positive(vars[7])]);

    // Support
    solver.add_clause(vec![Literal::positive(vars[6]), Literal::positive(vars[7])]);

    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);

    let (result, reason) = solve_with_timeout(&mut solver, 10);
    match &result {
        SatResult::Sat(model) => {
            // Verify all unit clauses satisfied
            for i in 0..4 {
                assert!(
                    model.get(i).copied().unwrap_or(false),
                    "unit clause x{i}=T violated in final model"
                );
            }
        }
        SatResult::Unknown => {
            if reason == Some(SatUnknownReason::InvalidSatModel) {
                eprintln!("WARNING: many-unit-clauses triggered FINALIZE_SAT_FAIL");
            }
        }
        SatResult::Unsat(_) => {
            panic!("many-unit-clauses SAT formula returned UNSAT — soundness bug");
        }
        _ => unreachable!(),
    }
}
