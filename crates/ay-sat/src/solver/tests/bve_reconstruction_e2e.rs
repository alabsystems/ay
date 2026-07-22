// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end BVE reconstruction validation tests (#8494).
//!
//! These tests verify that after BVE eliminates variables, the reconstruction
//! algorithm correctly restores eliminated variables in the model, and that
//! the resulting model satisfies the ORIGINAL formula (before BVE).
//!
//! Unlike the unit tests in reconstruct/tests.rs which test the ReconstructionStack
//! directly, these tests exercise the full solver pipeline: add_clause -> solve ->
//! finalize_sat_model (including reconstruction + original formula verification).
//!
//! The solver's `finalize_sat_model` already verifies the model against original
//! clauses (always-on, #4999). These tests add explicit verification in the test
//! layer for defense-in-depth and to exercise specific BVE-triggering patterns.

use super::*;

/// A clause represented as a list of (variable_index, positive?) pairs.
/// Used for independent verification outside the solver.
type ClauseSpec = Vec<(u32, bool)>;

/// Verify that a model satisfies all original clauses.
///
/// This is an independent check outside the solver's own verification
/// pipeline, providing defense-in-depth.
fn verify_model_against_clauses(model: &[bool], clauses: &[ClauseSpec]) {
    for (ci, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|&(var, positive)| {
            let var = var as usize;
            if var >= model.len() {
                return false;
            }
            if positive {
                model[var]
            } else {
                !model[var]
            }
        });
        assert!(
            satisfied,
            "Original clause {} unsatisfied by model: clause={:?}, model_vals={:?}",
            ci,
            clause
                .iter()
                .map(|&(v, p)| { (v as i32 + 1) * if p { 1 } else { -1 } })
                .collect::<Vec<_>>(),
            clause
                .iter()
                .map(|&(v, _)| (v, model.get(v as usize).copied()))
                .collect::<Vec<_>>(),
        );
    }
}

/// Add a clause to the solver and record it in the spec list.
fn add_and_record(solver: &mut Solver, clauses: &mut Vec<ClauseSpec>, lits: &[(u32, bool)]) {
    let clause_lits: Vec<Literal> = lits
        .iter()
        .map(|&(var, pos)| {
            if pos {
                Literal::positive(Variable(var))
            } else {
                Literal::negative(Variable(var))
            }
        })
        .collect();
    let spec: ClauseSpec = lits.to_vec();
    solver.add_clause(clause_lits);
    clauses.push(spec);
}

// =========================================================================
// Test: Simple BVE — one variable with one positive and one negative clause
// =========================================================================

#[test]
fn test_bve_e2e_simple_one_var_elimination() {
    // Formula:
    //   (x0 | x1)      — positive occurrence of x0
    //   (!x0 | x2)     — negative occurrence of x0
    //   (x1)           — anchor: force x1 = true
    //   (x2)           — anchor: force x2 = true
    //
    // BVE can eliminate x0: resolvent is (x1 | x2), which is subsumed by
    // the unit clauses. After elimination, reconstruction must set x0 to
    // a value satisfying both original clauses.
    let mut solver = Solver::new(3);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(
                model.len() >= 3,
                "model should have at least 3 variables, got {}",
                model.len()
            );
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Multi-variable BVE — three variables all eliminable
// =========================================================================

#[test]
fn test_bve_e2e_multi_variable_elimination() {
    // Variables 0, 1, 2 are BVE targets.
    // Variables 3, 4, 5, 6, 7, 8 are "anchor" variables that survive.
    //
    // x0: (x0 | x3), (!x0 | x4)
    // x1: (x1 | x5), (!x1 | x6)
    // x2: (x2 | x7), (!x2 | x8)
    //
    // All anchor variables forced true via unit clauses.
    let num_vars = 9;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // BVE targets
    add_and_record(&mut solver, &mut clauses, &[(0, true), (3, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (4, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true), (5, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (6, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, true), (7, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, false), (8, true)]);

    // Anchor unit clauses
    for v in 3..=8 {
        add_and_record(&mut solver, &mut clauses, &[(v, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(
                model.len() >= num_vars,
                "model should have at least {num_vars} variables"
            );
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Multi-round BVE — chain dependency
// =========================================================================

#[test]
fn test_bve_e2e_multi_round_chain_dependency() {
    // Round 1: eliminate x0 using (x0 | x1) and (!x0 | x2).
    // This produces resolvent (x1 | x2). With x1 a new eliminable variable
    // from round 2:
    // Round 2 candidate: x1 in (x1 | x2) [resolvent from round 1] and
    //   (!x1 | x3). Resolvent: (x2 | x3).
    //
    // We force x2 and x3 true so everything is satisfiable.
    let num_vars = 4;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // Round 1 elimination of x0
    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);

    // Round 2 elimination of x1
    add_and_record(&mut solver, &mut clauses, &[(1, true), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (3, true)]);

    // Anchor variables
    add_and_record(&mut solver, &mut clauses, &[(2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(3, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: All binary clauses
// =========================================================================

#[test]
fn test_bve_e2e_binary_clauses_only() {
    // A formula with only binary clauses. BVE on binary clauses produces
    // binary or unit resolvents, exercising the binary-clause reconstruction path.
    //
    // x0: (x0 | x1), (!x0 | x2)
    // x3: (x3 | x4), (!x3 | x5)
    // Additional: (x1 | x2), (x4 | x5) to ensure SAT.
    let num_vars = 6;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(3, true), (4, true)]);
    add_and_record(&mut solver, &mut clauses, &[(3, false), (5, true)]);

    // Force non-eliminated variables true for satisfiability
    add_and_record(&mut solver, &mut clauses, &[(1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(4, true)]);
    add_and_record(&mut solver, &mut clauses, &[(5, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Large clauses (ternary and beyond)
// =========================================================================

#[test]
fn test_bve_e2e_large_clauses() {
    // x0 in ternary clauses:
    //   (x0 | x1 | x2)
    //   (!x0 | x3 | x4)
    // BVE resolvent: (x1 | x2 | x3 | x4) — 4-literal clause.
    //
    // Also:
    //   (x0 | x5 | x6 | x7)   — 4-literal positive
    //   (!x0 | x8)             — binary negative
    // BVE resolvent: (x5 | x6 | x7 | x8) — 4-literal.
    let num_vars = 9;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(
        &mut solver,
        &mut clauses,
        &[(0, true), (1, true), (2, true)],
    );
    add_and_record(
        &mut solver,
        &mut clauses,
        &[(0, false), (3, true), (4, true)],
    );
    add_and_record(
        &mut solver,
        &mut clauses,
        &[(0, true), (5, true), (6, true), (7, true)],
    );
    add_and_record(&mut solver, &mut clauses, &[(0, false), (8, true)]);

    // Force all non-eliminated variables true
    for v in 1..=8 {
        add_and_record(&mut solver, &mut clauses, &[(v, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Mixed — some variables eliminated, some not
// =========================================================================

#[test]
fn test_bve_e2e_mixed_eliminated_and_surviving() {
    // x0 is BVE-eliminable: (x0 | x2), (!x0 | x3)
    // x1 is NOT eliminable (appears in 3+ clauses with various polarities):
    //   (x1 | x4), (x1 | x5), (!x1 | x6), (!x1 | x7)
    //
    // The model must include correct values for both x0 (reconstructed)
    // and x1 (directly assigned by CDCL search).
    let num_vars = 8;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // BVE-eliminable x0
    add_and_record(&mut solver, &mut clauses, &[(0, true), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (3, true)]);

    // Non-eliminable x1 (many occurrences)
    add_and_record(&mut solver, &mut clauses, &[(1, true), (4, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true), (5, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (6, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (7, true)]);

    // Force anchor variables
    for v in 2..=7 {
        add_and_record(&mut solver, &mut clauses, &[(v, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Forced polarity — eliminated variable MUST be true
// =========================================================================

#[test]
fn test_bve_e2e_forced_polarity_true() {
    // After BVE eliminates x0, reconstruction MUST set x0 = true because:
    //   (x0 | x1)      — if x1 = false, x0 must be true
    //   (!x0 | x2)     — x2 = true satisfies this regardless
    //
    // By forcing x1 = false and x2 = true, reconstruction must produce x0 = true.
    let num_vars = 3;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false)]); // force x1 = false
    add_and_record(&mut solver, &mut clauses, &[(2, true)]); // force x2 = true

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // x0 must be true because x1=false forces (x0|x1) to need x0=true
            assert!(model[0], "x0 must be true when x1=false to satisfy (x0|x1)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_bve_e2e_forced_polarity_false() {
    // After BVE eliminates x0, reconstruction MUST set x0 = false because:
    //   (x0 | x2)      — x2 = true satisfies this regardless
    //   (!x0 | x1)     — if x1 = false, x0 must be false
    //
    // By forcing x1 = false and x2 = true, reconstruction must produce x0 = false.
    let num_vars = 3;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false)]); // force x1 = false
    add_and_record(&mut solver, &mut clauses, &[(2, true)]); // force x2 = true

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // x0 must be false because x1=false forces (!x0|x1) to need x0=false
            assert!(
                !model[0],
                "x0 must be false when x1=false to satisfy (!x0|x1)"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: BVE with unit propagation interaction
// =========================================================================

#[test]
fn test_bve_e2e_unit_propagation_interaction() {
    // Unit clauses create level-0 assignments that interact with BVE.
    // BVE should correctly handle clauses that are root-satisfied (by
    // unit propagation) and clauses with root-false literals.
    //
    // (x0)            — unit: x0 = true at level 0
    // (x1 | x2)       — BVE target for x1
    // (!x1 | x3)      — BVE target for x1
    // (!x0 | x2)      — becomes (x2) after root propagation
    // (!x0 | x3)      — becomes (x3) after root propagation
    //
    // After unit propagation of x0=true, (!x0|x2) implies x2=true, etc.
    // BVE on x1 should work correctly in this propagated environment.
    let num_vars = 4;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (3, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (3, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // x0 must be true (unit clause)
            assert!(model[0], "x0 must be true (unit clause)");
            // x2 and x3 must be true (implied by !x0 clauses with x0=true)
            assert!(model[2], "x2 must be true (implied)");
            assert!(model[3], "x3 must be true (implied)");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Larger formula with multiple BVE rounds and non-trivial structure
// =========================================================================

#[test]
fn test_bve_e2e_larger_formula_multiple_rounds() {
    // A larger formula with 20 variables. Variables 0-4 are BVE targets,
    // variables 5-19 are anchors.
    //
    // Each BVE target xi has exactly 2 positive and 2 negative clauses:
    //   (xi | a1 | a2)
    //   (xi | a3)
    //   (!xi | a4 | a5)
    //   (!xi | a6)
    //
    // This creates resolvents of bounded size, making BVE profitable.
    let num_vars = 20;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // BVE targets 0-4, each with distinct anchor variables
    for target in 0..5u32 {
        let base = 5 + target * 3; // 3 anchor vars per target (5..19)
        let a1 = base;
        let a2 = base + 1;
        let a3 = base + 2;

        // Positive occurrences
        add_and_record(&mut solver, &mut clauses, &[(target, true), (a1, true)]);
        add_and_record(&mut solver, &mut clauses, &[(target, true), (a2, true)]);

        // Negative occurrences
        add_and_record(&mut solver, &mut clauses, &[(target, false), (a3, true)]);
        // Additional negative clause using a different anchor
        add_and_record(&mut solver, &mut clauses, &[(target, false), (a1, true)]);
    }

    // Force all anchor variables true
    for v in 5..num_vars as u32 {
        add_and_record(&mut solver, &mut clauses, &[(v, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: BVE on an implication chain
// =========================================================================

#[test]
fn test_bve_e2e_implication_chain() {
    // Implication chain: x0 -> x1 -> x2 -> x3 -> x4
    // Encoded as binary clauses:
    //   (!x0 | x1), (!x1 | x2), (!x2 | x3), (!x3 | x4)
    //
    // Plus (x0) to force x0 = true, which implies all must be true.
    // Variables in the middle of the chain (x1, x2, x3) have exactly
    // 1 positive and 1 negative occurrence and are BVE-eliminable.
    let num_vars = 5;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, false), (3, true)]);
    add_and_record(&mut solver, &mut clauses, &[(3, false), (4, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // All variables must be true due to the implication chain
            for (v, &value) in model.iter().enumerate().take(num_vars) {
                assert!(value, "x{v} must be true in implication chain");
            }
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: BVE with both polarities having multiple clauses
// =========================================================================

#[test]
fn test_bve_e2e_multiple_pos_and_neg_clauses() {
    // x0 has 3 positive and 2 negative occurrences.
    // BVE produces up to 6 resolvents, but may be profitable if some are
    // tautological.
    //
    //   (x0 | x1)
    //   (x0 | x2)
    //   (x0 | x3)
    //   (!x0 | x4)
    //   (!x0 | x5)
    //
    // Resolvents: (x1|x4), (x1|x5), (x2|x4), (x2|x5), (x3|x4), (x3|x5)
    // 6 resolvents for 5 removed = net +1, so BVE may or may not fire
    // depending on bounds. Force a smaller example:
    //
    //   (x0 | x1)
    //   (x0 | x2)
    //   (!x0 | x3)
    // Resolvents: (x1|x3), (x2|x3) — 2 resolvents for 3 removed = net -1
    let num_vars = 4;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, true), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (3, true)]);

    // Force anchor vars true
    add_and_record(&mut solver, &mut clauses, &[(1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(3, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Gate-pattern BVE (AND gate encoding)
// =========================================================================

#[test]
fn test_bve_e2e_and_gate_pattern() {
    // AND gate: y = (a AND b)
    // Encoding:
    //   (!a | !b | y)    — forward: if a and b, then y
    //   (a | !y)         — backward: if y, then a
    //   (b | !y)         — backward: if y, then b
    //
    // CaDiCaL detects this as a gate and eliminates y with gate-based BVE.
    // The resolvent is (!a | !b | a) ∧ (!a | !b | b) — both tautological.
    // Net result: 3 clauses removed, 0 added.
    //
    // After reconstruction, y must be correctly set to (a AND b).
    let num_vars = 3; // a=0, b=1, y=2
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // AND gate encoding
    add_and_record(
        &mut solver,
        &mut clauses,
        &[(0, false), (1, false), (2, true)],
    );
    add_and_record(&mut solver, &mut clauses, &[(0, true), (2, false)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true), (2, false)]);

    // Force a=true, b=true, so y must be true
    add_and_record(&mut solver, &mut clauses, &[(0, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // a=true, b=true => y must be true (AND gate)
            assert!(model[0], "a must be true");
            assert!(model[1], "b must be true");
            assert!(model[2], "y = (a AND b) must be true");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_bve_e2e_and_gate_false_output() {
    // Same AND gate but with a=true, b=false, so y must be false.
    let num_vars = 3;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(
        &mut solver,
        &mut clauses,
        &[(0, false), (1, false), (2, true)],
    );
    add_and_record(&mut solver, &mut clauses, &[(0, true), (2, false)]);
    add_and_record(&mut solver, &mut clauses, &[(1, true), (2, false)]);

    add_and_record(&mut solver, &mut clauses, &[(0, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // a=true, b=false => y must be false (AND gate)
            assert!(model[0], "a must be true");
            assert!(!model[1], "b must be false");
            assert!(!model[2], "y = (a AND b) must be false when b=false");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: BVE reconstruction with UNSAT formula (sanity check)
// =========================================================================

#[test]
fn test_bve_e2e_unsat_formula_not_confused_by_reconstruction() {
    // An UNSAT formula that also has BVE-eliminable variables.
    // BVE should not produce a false SAT.
    //
    // (x0 | x1), (!x0 | x1), (x0 | !x1), (!x0 | !x1)
    // This is unsatisfiable. x0 and x1 are both eliminable.
    let mut solver = Solver::new(2);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, false)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (1, false)]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "formula must be UNSAT, got {result:?}"
    );
}

// =========================================================================
// Test: Constraint-heavy formula with BVE (AIGER-style)
// =========================================================================

#[test]
fn test_bve_e2e_constraint_heavy_aiger_style() {
    // Simulates IC3 consecution checks with many unit clauses
    // (environment constraints) and BVE-eligible core variables.
    // This pattern caused false UNSAT in #8579.
    let num_env = 50;
    let num_core = 8;
    let num_vars = num_env + num_core;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // Environment unit clauses
    for i in 0..num_env {
        add_and_record(&mut solver, &mut clauses, &[(i as u32, true)]);
    }

    // Core BVE-eligible clauses: for each pair of adjacent core vars,
    //   (c_i | c_{i+1}) and (!c_i | c_{i+1})
    // Resolvent: (c_{i+1}) — unit, bounded elimination.
    for i in 0..(num_core - 1) {
        let ci = (num_env + i) as u32;
        let ci1 = (num_env + i + 1) as u32;
        add_and_record(&mut solver, &mut clauses, &[(ci, true), (ci1, true)]);
        add_and_record(&mut solver, &mut clauses, &[(ci, false), (ci1, true)]);
    }

    // Link some env vars to core vars
    for i in 0..num_env.min(num_core) {
        let ei = i as u32;
        let ci = (num_env + (i % num_core)) as u32;
        add_and_record(&mut solver, &mut clauses, &[(ei, false), (ci, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: BVE with negative-polarity-only elimination (pure literal)
// =========================================================================

#[test]
fn test_bve_e2e_pure_literal_positive() {
    // x0 appears only positively: (x0 | x1), (x0 | x2).
    // This is a pure literal — BVE sets x0 = true and removes both clauses.
    // Reconstruction must produce x0 = true.
    let num_vars = 3;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, true), (2, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_bve_e2e_pure_literal_negative() {
    // x0 appears only negatively: (!x0 | x1), (!x0 | x2).
    // Pure literal: x0 = false, both clauses satisfied.
    let num_vars = 3;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, false), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Cascading eliminations (5 variables in sequence)
// =========================================================================

#[test]
fn test_bve_e2e_cascading_five_variable_chain() {
    // x0 -> x1 -> x2 -> x3 -> x4 -> x5 (anchor)
    // Each variable has exactly one positive and one negative clause:
    //   (!xi | x_{i+1})
    // Plus (x0) to start the chain and (x5) as anchor.
    //
    // BVE can eliminate x1, x2, x3, x4 in sequence. Each elimination
    // produces a unit resolvent that enables the next.
    let num_vars = 6;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true)]);
    for i in 0..5u32 {
        add_and_record(&mut solver, &mut clauses, &[(i, false), (i + 1, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // All variables must be true
            for (v, &value) in model.iter().enumerate().take(num_vars) {
                assert!(value, "x{v} must be true in chain");
            }
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Diamond dependency pattern
// =========================================================================

#[test]
fn test_bve_e2e_diamond_dependency() {
    // Diamond: x0 -> x1, x0 -> x2, x1 -> x3, x2 -> x3
    //   (!x0 | x1), (!x0 | x2), (!x1 | x3), (!x2 | x3)
    // Plus (x0) and (!x3 | x4) with (x4) as anchor.
    //
    // x1 and x2 are BVE-eliminable (each has 1 pos + 1 neg occurrence).
    let num_vars = 5;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(&mut solver, &mut clauses, &[(0, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (1, true)]);
    add_and_record(&mut solver, &mut clauses, &[(0, false), (2, true)]);
    add_and_record(&mut solver, &mut clauses, &[(1, false), (3, true)]);
    add_and_record(&mut solver, &mut clauses, &[(2, false), (3, true)]);
    add_and_record(&mut solver, &mut clauses, &[(3, false), (4, true)]);
    add_and_record(&mut solver, &mut clauses, &[(4, true)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
            // All should be true due to the implication structure
            for (v, &value) in model.iter().enumerate().take(num_vars) {
                assert!(value, "x{v} must be true in diamond");
            }
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// =========================================================================
// Test: Variable numbering gap — eliminated variable is not contiguous
// =========================================================================

#[test]
fn test_bve_e2e_noncontiguous_eliminated_variable() {
    // x5 is the BVE target (high-numbered variable in a small formula).
    // x0..x4 are anchor variables.
    //
    //   (x5 | x0 | x1)
    //   (!x5 | x2 | x3)
    //   (x0), (x1), (x2), (x3), (x4)
    //
    // x5 is eliminated, but its index is higher than the surviving variables.
    // Tests that reconstruction handles non-contiguous variable indices.
    let num_vars = 6;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    add_and_record(
        &mut solver,
        &mut clauses,
        &[(5, true), (0, true), (1, true)],
    );
    add_and_record(
        &mut solver,
        &mut clauses,
        &[(5, false), (2, true), (3, true)],
    );

    for v in 0..=4 {
        add_and_record(&mut solver, &mut clauses, &[(v, true)]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model.len() >= num_vars, "model too small");
            verify_model_against_clauses(&model, &clauses);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}
