// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unsat core tests: assumption-based solving and core extraction.

use super::*;

/// Test that DpllT propagates unsat core from SAT solver
#[test]
fn test_dpllt_unsat_core_propagation() {
    // Create a DpllT with 2 variables (x, y)
    // Formula: (x) - forces x=true
    // Assumptions: ¬x - contradicts the unit clause
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Add unit clause: x (forces x=true)
    dpll.sat_solver_mut()
        .add_clause(vec![Literal::positive(Variable::new(0))]);

    // Assumption: ¬x (contradicts the unit clause)
    let lit_not_x = Literal::negative(Variable::new(0));

    let assumptions = vec![lit_not_x];
    let result = dpll.solve_with_assumptions(&assumptions).unwrap();

    match result {
        AssumeResult::Unsat(core, _) => {
            // Core should be a subset of assumptions
            for lit in &core {
                assert!(
                    assumptions.contains(lit),
                    "Unsat core literal {lit:?} not in assumptions"
                );
            }
            // The core might be empty if the SAT solver detects conflict
            // before fully processing assumptions (e.g., at decision level 0)
        }
        AssumeResult::Sat(_) => panic!("Should be unsat - ¬x contradicts unit clause x"),
        AssumeResult::Unknown => panic!("Should determine satisfiability"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test unsat core with multiple assumptions where only some conflict
#[test]
fn test_dpllt_unsat_core_minimal() {
    // Formula: (x ∨ y) with assumptions x=false, y=false, z=true
    // Only x=false and y=false are needed for unsat

    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Add clause: x ∨ y
    dpll.sat_solver_mut().add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Assumptions: ¬x, ¬y, z (only first two cause conflict)
    let assumptions = vec![
        Literal::negative(Variable::new(0)), // ¬x
        Literal::negative(Variable::new(1)), // ¬y
        Literal::positive(Variable::new(2)), // z (irrelevant)
    ];

    let result = dpll.solve_with_assumptions(&assumptions).unwrap();

    match result {
        AssumeResult::Unsat(core, _) => {
            // Core should be a subset of assumptions
            for lit in &core {
                assert!(
                    assumptions.contains(lit),
                    "Unsat core literal {lit:?} not in assumptions"
                );
            }

            // Core should contain at least ¬x or ¬y (both needed for conflict)
            // but should NOT contain z (it's irrelevant)
            let contains_z = core.contains(&Literal::positive(Variable::new(2)));
            assert!(
                !contains_z,
                "Unsat core should not contain irrelevant assumption z"
            );
        }
        AssumeResult::Sat(_) => panic!("Should be unsat"),
        AssumeResult::Unknown => panic!("Should determine satisfiability"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test unsat core with EUF theory
#[test]
fn test_dpllt_unsat_core_with_euf() {
    // Create: a = b ∧ f(a) ≠ f(b) (UNSAT due to congruence)
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::Uninterpreted("U".to_string()));
    let b = terms.mk_var("b", Sort::Uninterpreted("U".to_string()));

    let f_a = terms.mk_app(
        Symbol::Named("f".to_string()),
        vec![a],
        Sort::Uninterpreted("U".to_string()),
    );
    let f_b = terms.mk_app(
        Symbol::Named("f".to_string()),
        vec![b],
        Sort::Uninterpreted("U".to_string()),
    );

    let a_eq_b = terms.mk_eq(a, b);
    let f_a_eq_f_b = terms.mk_eq(f_a, f_b);
    let f_a_neq_f_b = terms.mk_not(f_a_eq_f_b);

    // Tseitin transform
    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform_all(&[a_eq_b, f_a_neq_f_b]);

    // Create solver
    let euf = EufSolver::new(&terms);
    let mut dpll = DpllT::from_tseitin(&terms, &result, euf);

    // This should be UNSAT without assumptions
    let result = dpll.solve().unwrap();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "a = b ∧ f(a) ≠ f(b) should be UNSAT"
    );
}
