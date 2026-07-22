// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Proof-coverage tests for propagation, backtracking, and model verification.
//!
//! Part of Epic #4172 (sat-debuggability). These tests exercise the BCP hot
//! loop, backtracking, and model verification through the public Solver API.
//!
//! Prior to this file, propagation.rs (525 LOC) and backtrack.rs (449 LOC)
//! had ZERO dedicated test coverage. All testing was indirect through
//! solver-level integration tests that couldn't isolate a BCP bug from a
//! backtracking bug.
//!
//! These formulas are designed to force specific solver behaviors:
//! - Binary and ternary unit propagation
//! - Implication chain propagation
//! - Watch replacement without propagation
//! - Conflict detection in non-binary clauses
//! - Backtracking with phase saving (via CDCL conflict-driven backjumps)
//! - Model verification of SAT results

use ay_sat::{Literal, SatResult, Solver, Variable};

// ========================================================================
// Propagation coverage: formulas that exercise specific BCP paths
// ========================================================================

/// Exercise binary unit propagation: (x0) ∧ (¬x0 ∨ x1)
///
/// BCP at level 0: x0 is a unit clause, propagated true. Then (¬x0 ∨ x1)
/// becomes unit with x0=true, so x1 must be propagated true. This exercises
/// the binary clause propagation path in propagate().
#[test]
fn test_bcp_binary_unit_propagation() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    // Unit clause: x0 = true
    solver.add_clause(vec![Literal::positive(x0)]);
    // Binary implication: x0 → x1
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "x0 must be true (unit clause)");
            assert!(model[1], "x1 must be true (propagated from x0)");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Exercise ternary unit propagation: (x0) ∧ (¬x1) ∧ (¬x0 ∨ x1 ∨ x2)
///
/// With x0=true and x1=false, the ternary clause (¬x0 ∨ x1 ∨ x2) has two
/// false literals and one unassigned → BCP must propagate x2=true.
/// This exercises the non-binary unit propagation path.
#[test]
fn test_bcp_ternary_unit_propagation() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    solver.add_clause(vec![Literal::positive(x0)]);
    solver.add_clause(vec![Literal::negative(x1)]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "x0 = true (unit)");
            assert!(!model[1], "x1 = false (unit)");
            assert!(model[2], "x2 = true (ternary BCP)");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Exercise implication chain: x0 → x1 → x2 → x3 → x4
///
/// A chain of 4 binary implications starting from unit clause (x0).
/// BCP must propagate all 5 variables in one pass through the trail.
/// This tests multi-step propagation with qhead advancing through the chain.
#[test]
fn test_bcp_implication_chain() {
    let mut solver = Solver::new(5);
    let vars: Vec<Variable> = (0..5).map(Variable::new).collect();

    // Force x0 = true
    solver.add_clause(vec![Literal::positive(vars[0])]);

    // Chain: x0 → x1 → x2 → x3 → x4
    for i in 0..4 {
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            for (i, val) in model.iter().enumerate() {
                assert!(val, "x{i} must be true (chain propagation)");
            }
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Exercise watch replacement: 4-literal clause with only one falsified watch.
///
/// Clause (x0 ∨ x1 ∨ x2 ∨ x3) is watched on x0 and x1 initially.
/// When x0 is forced false but x1,x2,x3 are free, BCP should move the watch
/// to an unassigned literal without propagating. The formula is SAT with
/// x0=false (forced by unit clause) and x1 or x2 or x3 = true.
#[test]
fn test_bcp_watch_replacement() {
    let mut solver = Solver::new(4);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);

    // Force x0 = false
    solver.add_clause(vec![Literal::negative(x0)]);
    // 4-literal clause: when x0 becomes false, BCP moves watch
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
        Literal::positive(x3),
    ]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(!model[0], "x0 must be false (unit clause)");
            // At least one of x1, x2, x3 must be true
            assert!(
                model[1] || model[2] || model[3],
                "At least one of x1,x2,x3 must be true to satisfy the clause"
            );
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Exercise conflict detection: UNSAT formula requiring BCP conflict.
///
/// (x0) ∧ (¬x0 ∨ x1) ∧ (¬x0 ∨ ¬x1) forces x0=true, x1=true, x1=false.
/// BCP at level 0 propagates x0=true → x1=true (binary), then ¬x0 ∨ ¬x1
/// becomes empty. BCP must detect this conflict.
#[test]
fn test_bcp_conflict_detection() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    solver.add_clause(vec![Literal::positive(x0)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x1)]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Formula is UNSAT: x0→x1 and x0→¬x1"
    );
}

/// Exercise non-binary conflict: ternary clause falsified.
///
/// (x0 ∨ x1 ∨ x2) ∧ (¬x0) ∧ (¬x1) ∧ (¬x2) forces all three false,
/// then the ternary clause has no replacement literal → conflict.
/// This exercises the non-binary conflict path in propagate().
#[test]
fn test_bcp_ternary_conflict() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);
    solver.add_clause(vec![Literal::negative(x0)]);
    solver.add_clause(vec![Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x2)]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Formula is UNSAT: ternary clause falsified"
    );
}

// ========================================================================
// Backtracking coverage: formulas that require CDCL backjumps
// ========================================================================

/// Exercise CDCL backtracking: formula requires conflict analysis + backjump.
///
/// This formula encodes a pigeonhole-like constraint that forces the solver
/// to learn clauses and backtrack. x0 and x1 interact through multiple
/// clauses requiring exploration of both polarities.
///
/// (x0 ∨ x1) ∧ (x0 ∨ ¬x1) ∧ (¬x0 ∨ x2) ∧ (¬x0 ∨ ¬x2)
///
/// The only satisfying assignment is x0=true: clauses 1,2 force x0=true
/// (since x0=false would require x1=true AND x1=false). Clauses 3,4 then
/// force x2=true AND x2=false → UNSAT.
#[test]
fn test_cdcl_backjump_required() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x2)]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Formula is UNSAT: requires conflict analysis and backjump"
    );
}

/// Exercise multiple backtracks: formula requires several conflict-driven
/// backtracks before determining satisfiability.
///
/// 8-variable formula with conflicting constraints. The solver must explore
/// and backtrack through multiple decision levels to find the solution.
#[test]
fn test_cdcl_multiple_backtracks() {
    let mut solver = Solver::new(8);
    let vars: Vec<Variable> = (0..8).map(Variable::new).collect();

    // Implication chain: x0 → x1 → x2 → x3
    for i in 0..3 {
        solver.add_clause(vec![
            Literal::negative(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }
    // Backward implications: x3 → ¬x4, x4 → x5, x5 → ¬x6
    solver.add_clause(vec![Literal::negative(vars[3]), Literal::negative(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[4]), Literal::positive(vars[5])]);
    solver.add_clause(vec![Literal::negative(vars[5]), Literal::negative(vars[6])]);
    // Clauses requiring positive vars: (x4 ∨ x6 ∨ x7) ∧ (x0 ∨ x7)
    solver.add_clause(vec![
        Literal::positive(vars[4]),
        Literal::positive(vars[6]),
        Literal::positive(vars[7]),
    ]);
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[7])]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify the model satisfies all clauses manually
            // Chain: x0 → x1 → x2 → x3
            for i in 0..3 {
                assert!(
                    !model[i] || model[i + 1],
                    "Implication x{i} → x{} violated",
                    i + 1
                );
            }
            // x3 → ¬x4
            assert!(!model[3] || !model[4], "x3 → ¬x4 violated");
            // x4 → x5
            assert!(!model[4] || model[5], "x4 → x5 violated");
            // x5 → ¬x6
            assert!(!model[5] || !model[6], "x5 → ¬x6 violated");
            // (x4 ∨ x6 ∨ x7)
            assert!(model[4] || model[6] || model[7], "(x4 ∨ x6 ∨ x7) violated");
            // (x0 ∨ x7)
            assert!(model[0] || model[7], "(x0 ∨ x7) violated");
        }
        SatResult::Unsat(_) => panic!("Expected SAT (formula is satisfiable)"),
        SatResult::Unknown => panic!("Expected SAT, got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Exercise backtracking to level 0: formula UNSAT at root level after
/// learning a unit clause from conflict analysis.
///
/// When conflict analysis at a higher level learns a unit clause, the
/// solver backtracks to level 0 and propagates. If this creates another
/// conflict, the formula is UNSAT. This tests backtrack(0) path.
#[test]
fn test_cdcl_backtrack_to_zero_unsat() {
    let mut solver = Solver::new(4);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);

    // Clauses that force x0 → contradiction:
    // (x0 ∨ x1) ∧ (x0 ∨ ¬x1) means x0 must be true
    // (¬x0 ∨ x2) ∧ (¬x0 ∨ ¬x2) means if x0=true then contradiction
    // Adding x3 involvement for multi-level exploration:
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x2),
        Literal::positive(x3),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x2),
        Literal::negative(x3),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::negative(x2),
        Literal::positive(x3),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::negative(x2),
        Literal::negative(x3),
    ]);

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Formula is UNSAT: exhaustive contradiction after x0 is forced true"
    );
}

// ========================================================================
// Model verification coverage: verify SAT models satisfy original clauses
// ========================================================================

/// Verify that a SAT model satisfies all original clauses.
///
/// This exercises the verify_model path that runs before every SatResult::Sat.
/// The formula has a unique model, so we can check exact values.
#[test]
fn test_model_satisfies_all_clauses() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    // Force unique model: x0=true, x1=false, x2=true
    solver.add_clause(vec![Literal::positive(x0)]);
    solver.add_clause(vec![Literal::negative(x1)]);
    solver.add_clause(vec![Literal::positive(x2)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_eq!(model.len(), 3, "Model must have 3 variables");
            assert!(model[0], "x0 = true");
            assert!(!model[1], "x1 = false");
            assert!(model[2], "x2 = true");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify model with mixed polarity clauses.
///
/// Formula with negative literals requiring careful polarity checking
/// in verify_model's clause_satisfied helper.
#[test]
fn test_model_mixed_polarity() {
    let mut solver = Solver::new(4);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);

    // (¬x0 ∨ ¬x1) — at least one must be false
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x1)]);
    // (x0 ∨ x2) — x0 or x2 must be true
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);
    // (x1 ∨ x3) — x1 or x3 must be true
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x3)]);
    // (¬x2 ∨ ¬x3) — at least one of x2,x3 must be false
    solver.add_clause(vec![Literal::negative(x2), Literal::negative(x3)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify manually
            assert!(
                !model[0] || !model[1],
                "(¬x0 ∨ ¬x1) violated: x0={}, x1={}",
                model[0],
                model[1]
            );
            assert!(
                model[0] || model[2],
                "(x0 ∨ x2) violated: x0={}, x2={}",
                model[0],
                model[2]
            );
            assert!(
                model[1] || model[3],
                "(x1 ∨ x3) violated: x1={}, x3={}",
                model[1],
                model[3]
            );
            assert!(
                !model[2] || !model[3],
                "(¬x2 ∨ ¬x3) violated: x2={}, x3={}",
                model[2],
                model[3]
            );
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Verify model correctness for a formula with many clauses.
///
/// A structured formula (5 variables, 10 clauses) that exercises the
/// full verify_model path including the loop over all clause_db entries.
#[test]
fn test_model_many_clauses() {
    let mut solver = Solver::new(5);
    let vars: Vec<Variable> = (0..5).map(Variable::new).collect();

    // Create a satisfiable formula with 10 clauses
    let clauses: Vec<Vec<Literal>> = vec![
        vec![Literal::positive(vars[0]), Literal::positive(vars[1])],
        vec![Literal::positive(vars[1]), Literal::positive(vars[2])],
        vec![Literal::positive(vars[2]), Literal::positive(vars[3])],
        vec![Literal::positive(vars[3]), Literal::positive(vars[4])],
        vec![Literal::negative(vars[0]), Literal::positive(vars[2])],
        vec![Literal::negative(vars[1]), Literal::positive(vars[3])],
        vec![Literal::negative(vars[2]), Literal::positive(vars[4])],
        vec![
            Literal::positive(vars[0]),
            Literal::negative(vars[3]),
            Literal::positive(vars[4]),
        ],
        vec![
            Literal::negative(vars[0]),
            Literal::positive(vars[1]),
            Literal::negative(vars[4]),
        ],
        vec![
            Literal::positive(vars[2]),
            Literal::negative(vars[3]),
            Literal::positive(vars[4]),
        ],
    ];

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify every clause is satisfied
            for (i, clause) in clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|lit| {
                    let var = lit.variable().index();
                    model[var] == lit.is_positive()
                });
                assert!(satisfied, "Clause {i} not satisfied by model: {clause:?}");
            }
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}
