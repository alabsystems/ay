// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gap 11: Theory conflict explanation soundness — EUF and LRA.
//!
//! When a theory reports a conflict, the explanation literals should
//! logically imply the conflict.

use super::*;

#[test]
fn test_euf_conflict_explanation_soundness_gap11() {
    // Test that EUF produces sound explanations
    // Set up: a = b ∧ b = c ⟹ a = c (transitivity)
    // If we assert a = b, b = c, and a ≠ c, we should get UNSAT
    // and the explanation should be {a = b, b = c, a ≠ c}

    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());

    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s.clone());
    let c = terms.mk_var("c", sort_s);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let _neq_ac = terms.mk_not(eq_ac); // kept for documentation

    // Create EUF solver and assert literals
    let mut euf = EufSolver::new(&terms);

    // Assert: a = b, b = c, a ≠ c
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_ac, false);

    // Check should return Unsat (conflict)
    let result = euf.check();
    match result {
        TheoryResult::Unsat(explanation) => {
            assert!(
                !explanation.is_empty(),
                "EUF conflict explanation is empty - soundness violation"
            );
        }
        TheoryResult::Sat => {
            panic!("EUF should find conflict for a=b ∧ b=c ∧ a≠c (transitivity)");
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            assert!(
                !conflict.literals.is_empty(),
                "EUF conflict explanation is empty - soundness violation"
            );
        }
        other => {
            panic!("EUF should detect a=b ∧ b=c ∧ a≠c as Unsat, got {other:?}");
        }
    }
}

#[test]
fn test_lra_conflict_explanation_soundness_gap11() {
    use ay_lra::LraSolver;

    // Test that LRA produces sound explanations
    // Set up: x >= 5 ∧ x <= 3 is clearly UNSAT

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_int(5.into());
    let three = terms.mk_int(3.into());

    let ge_5 = terms.mk_app(Symbol::Named(">=".to_string()), vec![x, five], Sort::Bool);
    let le_3 = terms.mk_app(Symbol::Named("<=".to_string()), vec![x, three], Sort::Bool);

    let mut lra = LraSolver::new(&terms);

    lra.assert_literal(ge_5, true);
    lra.assert_literal(le_3, true);

    let result = lra.check();
    match result {
        TheoryResult::Unsat(explanation) => {
            assert!(
                !explanation.is_empty(),
                "LRA conflict explanation is empty - soundness violation"
            );

            // Soundness verification: re-solve with only explanation literals
            let mut lra2 = LraSolver::new(&terms);
            for lit in &explanation {
                lra2.assert_literal(lit.term, lit.value);
            }
            let result2 = lra2.check();
            assert!(
                matches!(result2, TheoryResult::Unsat(_)),
                "LRA explanation is not sound: re-asserting explanation literals did not cause conflict"
            );
        }
        TheoryResult::Sat => {
            panic!("LRA should find conflict for x >= 5 ∧ x <= 3");
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            let mut lra2 = LraSolver::new(&terms);
            for lit in &conflict.literals {
                lra2.assert_literal(lit.term, lit.value);
            }
            let result2 = lra2.check();
            assert!(
                matches!(result2, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
                "LRA explanation is not sound: re-asserting explanation literals did not cause conflict"
            );
        }
        other => {
            panic!("LRA should detect x >= 5 ∧ x <= 3 as Unsat, got {other:?}");
        }
    }
}

/// Gap 11: LRA Explanation Minimality Test
///
/// Test that LRA explanations are reasonably minimal (don't include
/// irrelevant literals).
#[test]
fn test_lra_explanation_minimality_gap11() {
    use ay_lra::LraSolver;

    // Set up a conflict with one irrelevant constraint:
    // x >= 5 ∧ x <= 3 ∧ y >= 0 should conflict
    // The explanation should NOT include y >= 0

    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_int(5.into());
    let three = terms.mk_int(3.into());
    let zero = terms.mk_int(0.into());

    let ge_5 = terms.mk_app(Symbol::Named(">=".to_string()), vec![x, five], Sort::Bool);
    let le_3 = terms.mk_app(Symbol::Named("<=".to_string()), vec![x, three], Sort::Bool);
    let y_ge_0 = terms.mk_app(Symbol::Named(">=".to_string()), vec![y, zero], Sort::Bool);

    let mut lra = LraSolver::new(&terms);

    lra.assert_literal(ge_5, true);
    lra.assert_literal(le_3, true);
    lra.assert_literal(y_ge_0, true);

    let result = lra.check();
    match result {
        TheoryResult::Unsat(explanation) => {
            let contains_y = explanation.iter().any(|lit| lit.term == y_ge_0);
            assert!(
                !contains_y,
                "LRA explanation includes irrelevant constraint (y >= 0) - minimality violation"
            );
            assert!(
                explanation.len() <= 2,
                "LRA explanation has {} literals, expected at most 2",
                explanation.len()
            );
        }
        TheoryResult::Sat => {
            panic!("LRA should find conflict for x >= 5 ∧ x <= 3");
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            let contains_y = conflict.literals.iter().any(|lit| lit.term == y_ge_0);
            assert!(
                !contains_y,
                "LRA explanation includes irrelevant constraint (y >= 0) - minimality violation"
            );
            assert!(
                conflict.literals.len() <= 2,
                "LRA explanation has {} literals, expected at most 2",
                conflict.literals.len()
            );
        }
        other => {
            panic!("LRA should detect x >= 5 ∧ x <= 3 (with irrelevant y >= 0) as Unsat, got {other:?}");
        }
    }
}
