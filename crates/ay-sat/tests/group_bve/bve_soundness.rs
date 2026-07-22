// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BVE soundness integration tests (Part of #3292).
//!
//! These tests verify that BVE (bounded variable elimination) produces correct
//! results at the solver API level. BVE is currently disabled due to #3292
//! (reconstruction soundness bug). When re-enabled, these tests serve as the
//! soundness regression gate.
//!
//! A companion unit test `test_bve_resolvents_are_irredundant` in
//! `solver/tests.rs` verifies the internal invariant that BVE resolvents
//! are marked irredundant (the #3292 root cause).

use ay_sat::{Literal, SatResult, Solver, Variable};

/// Verify that solving a SAT formula with BVE enabled produces a correct model.
///
/// When BVE is re-enabled, this test exercises the full elimination →
/// reconstruction → model-check pipeline. Currently BVE is disabled
/// (should_bve() returns false), so this serves as a regression gate.
#[test]
fn test_bve_enabled_sat_formula_produces_valid_model() {
    let mut solver = Solver::new(5);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);
    let x4 = Variable::new(4);

    // Formula with a variable (x0) that has bounded resolution.
    // Positive occurrences of x0:
    //   C0: (x0 ∨ x1 ∨ x2)
    //   C1: (x0 ∨ x3)
    // Negative occurrences of x0:
    //   C2: (¬x0 ∨ x2 ∨ x4)
    //   C3: (¬x0 ∨ x1)
    // BVE on x0 would produce resolvents:
    //   R(C0,C2): (x1 ∨ x2 ∨ x4)
    //   R(C0,C3): (x1 ∨ x2)
    //   R(C1,C2): (x3 ∨ x2 ∨ x4)
    //   R(C1,C3): (x3 ∨ x1)
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x3)]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x2),
        Literal::positive(x4),
    ]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);

    // Additional clause to constrain the solution space
    solver.add_clause(vec![Literal::positive(x4)]);

    solver.set_bve_enabled(true);

    let original_clauses: [&[Literal]; 5] = [
        &[
            Literal::positive(x0),
            Literal::positive(x1),
            Literal::positive(x2),
        ],
        &[Literal::positive(x0), Literal::positive(x3)],
        &[
            Literal::negative(x0),
            Literal::positive(x2),
            Literal::positive(x4),
        ],
        &[Literal::negative(x0), Literal::positive(x1)],
        &[Literal::positive(x4)],
    ];

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            // Verify model satisfies all original clauses
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|lit| {
                    let var_idx = lit.variable().index();
                    if var_idx >= model.len() {
                        return false;
                    }
                    if lit.is_positive() {
                        model[var_idx]
                    } else {
                        !model[var_idx]
                    }
                });
                assert!(
                    satisfied,
                    "BVE soundness: model violates original clause #{ci}: {clause:?}"
                );
            }
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

/// Regression test for #8223: BVE elimination with backward subsumption.
///
/// Exercises the exact bug pattern from #8223:
/// 1. Variable x0 is eliminable (2 pos, 2 neg occurrences → 4 resolvents)
/// 2. A resolvent subsumes an existing clause containing variable x3
/// 3. If x3 is later eliminated, the subsumed clause must still be in x3's
///    extension stack for correct reconstruction
/// 4. The reconstructed model must satisfy ALL original clauses
///
/// The formula is SAT (x0=T, x1=T, x2=T, x3=T, x4=T, x5=F satisfies all).
/// Before the #8223 fix, backward subsumption would delete the subsumed clause,
/// removing it from x3's extension stack, causing reconstruction to produce
/// a model violating the original formula.
#[test]
fn test_bve_backward_subsumption_reconstruction_soundness_8223() {
    let mut solver = Solver::new(6);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);
    let x3 = Variable::new(3);
    let x4 = Variable::new(4);
    let x5 = Variable::new(5);

    // Positive occurrences of x0 (eliminable variable):
    //   C0: (x0 v x1)
    //   C1: (x0 v x2)
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);

    // Negative occurrences of x0:
    //   C2: (!x0 v x3 v x4)
    //   C3: (!x0 v x1 v x5)
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x3),
        Literal::positive(x4),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::positive(x1),
        Literal::positive(x5),
    ]);

    // BVE on x0 produces resolvents:
    //   R(C0,C2): (x1 v x3 v x4)
    //   R(C0,C3): (x1 v x5)        -- this subsumes C4 below
    //   R(C1,C2): (x2 v x3 v x4)
    //   R(C1,C3): (x2 v x1 v x5)

    // C4: (x1 v x3 v x5) -- subsumable by R(C0,C3) = (x1 v x5)
    // Contains x3: if x3 is eliminated later, C4 must be on x3's
    // extension stack for correct reconstruction.
    solver.add_clause(vec![
        Literal::positive(x1),
        Literal::positive(x3),
        Literal::positive(x5),
    ]);

    // Additional clauses involving x3 to make it eliminable:
    //   C5: (x3 v x4)
    //   C6: (!x3 v x2)
    //   C7: (!x3 v x4)
    solver.add_clause(vec![Literal::positive(x3), Literal::positive(x4)]);
    solver.add_clause(vec![Literal::negative(x3), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::negative(x3), Literal::positive(x4)]);

    // Constraint to force non-trivial model:
    //   C8: (x4)
    solver.add_clause(vec![Literal::positive(x4)]);

    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);

    let original_clauses: Vec<Vec<Literal>> = vec![
        vec![Literal::positive(x0), Literal::positive(x1)],
        vec![Literal::positive(x0), Literal::positive(x2)],
        vec![
            Literal::negative(x0),
            Literal::positive(x3),
            Literal::positive(x4),
        ],
        vec![
            Literal::negative(x0),
            Literal::positive(x1),
            Literal::positive(x5),
        ],
        vec![
            Literal::positive(x1),
            Literal::positive(x3),
            Literal::positive(x5),
        ],
        vec![Literal::positive(x3), Literal::positive(x4)],
        vec![Literal::negative(x3), Literal::positive(x2)],
        vec![Literal::negative(x3), Literal::positive(x4)],
        vec![Literal::positive(x4)],
    ];

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|lit| {
                    let var_idx = lit.variable().index();
                    if var_idx >= model.len() {
                        return false;
                    }
                    if lit.is_positive() {
                        model[var_idx]
                    } else {
                        !model[var_idx]
                    }
                });
                assert!(
                    satisfied,
                    "#8223: BVE backward subsumption reconstruction: model violates clause #{ci}: {:?}",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        SatResult::Unknown => panic!(
            "#8223: BVE backward subsumption reconstruction returned Unknown — \
             likely InvalidSatModel from reconstruction failure"
        ),
        SatResult::Unsat(_) => {
            // Formula is SAT, UNSAT result indicates soundness bug
            panic!(
                "#8223: BVE backward subsumption reconstruction returned UNSAT \
                 on known-SAT formula — BVE derived unsound empty clause"
            );
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Regression test for #8223: multiple sequential BVE eliminations with
/// cascading backward subsumption.
///
/// Tests a formula where BVE eliminates variables sequentially (x0 then x3),
/// and resolvents from x0's elimination subsume clauses needed for x3's
/// reconstruction. This catches the exact cascade bug described in #8223.
#[test]
fn test_bve_cascade_elimination_reconstruction_8223() {
    let mut solver = Solver::new(8);
    let vars: Vec<Variable> = (0..8).map(Variable::new).collect();

    // Phase 1: x0 eliminable
    // Pos: (x0 v x1), (x0 v x2 v x3)
    // Neg: (!x0 v x4), (!x0 v x5)
    solver.add_clause(vec![Literal::positive(vars[0]), Literal::positive(vars[1])]);
    solver.add_clause(vec![
        Literal::positive(vars[0]),
        Literal::positive(vars[2]),
        Literal::positive(vars[3]),
    ]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[4])]);
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::positive(vars[5])]);

    // Phase 2: x3 eliminable after x0 is gone
    // Pos: (x3 v x6), (x3 v x7)
    // Neg: (!x3 v x1 v x4)
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[6])]);
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[7])]);
    solver.add_clause(vec![
        Literal::negative(vars[3]),
        Literal::positive(vars[1]),
        Literal::positive(vars[4]),
    ]);

    // Bridge clause: contains both x3 and x5
    // After x0 elimination, resolvent (x1 v x5) could subsume this
    // (x1 v x3 v x5), removing it from x3's extension stack.
    solver.add_clause(vec![
        Literal::positive(vars[1]),
        Literal::positive(vars[3]),
        Literal::positive(vars[5]),
    ]);

    // Constraints to keep formula satisfiable
    solver.add_clause(vec![Literal::positive(vars[6]), Literal::positive(vars[7])]);

    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify: all original clauses must be satisfied
            let original_clauses = vec![
                vec![Literal::positive(vars[0]), Literal::positive(vars[1])],
                vec![
                    Literal::positive(vars[0]),
                    Literal::positive(vars[2]),
                    Literal::positive(vars[3]),
                ],
                vec![Literal::negative(vars[0]), Literal::positive(vars[4])],
                vec![Literal::negative(vars[0]), Literal::positive(vars[5])],
                vec![Literal::positive(vars[3]), Literal::positive(vars[6])],
                vec![Literal::positive(vars[3]), Literal::positive(vars[7])],
                vec![
                    Literal::negative(vars[3]),
                    Literal::positive(vars[1]),
                    Literal::positive(vars[4]),
                ],
                vec![
                    Literal::positive(vars[1]),
                    Literal::positive(vars[3]),
                    Literal::positive(vars[5]),
                ],
                vec![Literal::positive(vars[6]), Literal::positive(vars[7])],
            ];
            for (ci, clause) in original_clauses.iter().enumerate() {
                let satisfied = clause.iter().any(|lit| {
                    let vi = lit.variable().index();
                    vi < model.len()
                        && ((lit.is_positive() && model[vi]) || (!lit.is_positive() && !model[vi]))
                });
                assert!(
                    satisfied,
                    "#8223: cascade BVE reconstruction: model violates clause #{ci}: {:?}",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        SatResult::Unknown => {
            panic!("#8223: cascade BVE reconstruction returned Unknown — reconstruction failure")
        }
        SatResult::Unsat(_) => {
            // The formula is satisfiable (e.g. all true). UNSAT means soundness bug.
            panic!("#8223: cascade BVE reconstruction returned UNSAT on SAT formula");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Verify that solving a known-UNSAT formula with BVE enabled returns UNSAT.
///
/// This tests the BVE → empty resolvent → UNSAT derivation path.
#[test]
fn test_bve_enabled_unsat_formula_returns_unsat() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    // Unit clauses force x1=T, x2=T
    solver.add_clause(vec![Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x2)]);

    // BVE on x0 produces resolvent (¬x1 ∨ ¬x2), which conflicts with x1=T, x2=T
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x2)]);

    solver.set_bve_enabled(true);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");
}
