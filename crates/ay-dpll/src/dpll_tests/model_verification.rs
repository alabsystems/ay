// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gap 12: SMT model verification tests.
//!
//! When the solver returns SAT, verify that the model actually satisfies
//! the original assertions, not just the CNF encoding.

use super::*;

#[test]
fn test_smt_model_verification_gap12() {
    // Test 1: Simple SAT formula with expected model
    let mut solver = SmtSolver::new();

    // Create (a ∨ b) - should be SAT
    let a = solver.terms.mk_var("a", Sort::Bool);
    let b = solver.terms.mk_var("b", Sort::Bool);
    let formula = solver.terms.mk_or(vec![a, b]);

    solver.assert(formula);

    let result = solver.solve_propositional();
    match result {
        SatResult::Sat(model) => {
            // Verify: at least one of a or b must be true in the model
            let a_true = model.first().copied().unwrap_or(false);
            let b_true = model.get(1).copied().unwrap_or(false);
            assert!(
                a_true || b_true,
                "SMT Model Soundness: (a ∨ b) returned SAT but neither a nor b is true"
            );
        }
        other => panic!("(a ∨ b) should be SAT, got {other:?}"),
    }
}

/// Gap 12 continued: Verify SMT model against conjunction
#[test]
fn test_smt_model_verification_conjunction() {
    let mut solver = SmtSolver::new();

    // Create (a ∧ b) - should be SAT with a=true, b=true
    let a = solver.terms.mk_var("a", Sort::Bool);
    let b = solver.terms.mk_var("b", Sort::Bool);
    let formula = solver.terms.mk_and(vec![a, b]);

    solver.assert(formula);

    let result = solver.solve_propositional();
    match result {
        SatResult::Sat(model) => {
            // Verify: both a and b must be true
            let a_true = model.first().copied().unwrap_or(false);
            let b_true = model.get(1).copied().unwrap_or(false);
            assert!(
                a_true && b_true,
                "SMT Model Soundness: (a ∧ b) returned SAT but a={a_true}, b={b_true}"
            );
        }
        other => panic!("(a ∧ b) should be SAT, got {other:?}"),
    }
}

/// Gap 12 continued: Verify model against implications
#[test]
fn test_smt_model_verification_implication() {
    let mut solver = SmtSolver::new();

    // Create (a ⟹ b) ∧ a - should be SAT with a=true, b=true
    // (a ⟹ b) is equivalent to (¬a ∨ b)
    let a = solver.terms.mk_var("a", Sort::Bool);
    let b = solver.terms.mk_var("b", Sort::Bool);
    let not_a = solver.terms.mk_not(a);
    let implies = solver.terms.mk_or(vec![not_a, b]);
    let formula = solver.terms.mk_and(vec![implies, a]);

    solver.assert(formula);

    let result = solver.solve_propositional();
    match result {
        SatResult::Sat(model) => {
            // Verify: a must be true (from second conjunct)
            // and b must be true (from implication with a=true)
            let a_true = model.first().copied().unwrap_or(false);
            let b_true = model.get(1).copied().unwrap_or(false);
            assert!(
                a_true,
                "SMT Model Soundness: (a ⟹ b) ∧ a returned SAT but a=false"
            );
            assert!(
                b_true,
                "SMT Model Soundness: (a ⟹ b) ∧ a returned SAT with a=true but b=false"
            );
        }
        other => panic!("(a ⟹ b) ∧ a should be SAT, got {other:?}"),
    }
}
