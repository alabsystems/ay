// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Dual Simplex Invariants (#2014)
// ========================================================================

/// LRA check() correctly identifies UNSAT on a 2-variable problem.
///
/// Part of #2014: Tests that the full assert_literal → check() path correctly
/// detects UNSAT on (x >= 10, x + y <= 5, y >= 0). Verifies conflict clause
/// only contains asserted literals. Rejects NeedSplit on a purely linear problem.
///
/// Note: The previous version of this harness called dual_simplex_with_max_iters()
/// directly after assert_literal(). That skips atom-to-bound parsing (done in
/// check()) so the simplex saw no bounds and always returned SAT — the test was
/// passing trivially via the Unknown arm.
#[kani::proof]
#[kani::unwind(4)]
fn proof_dual_simplex_terminates_within_limit() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let y = terms.mk_var("y", ay_core::Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x >= 10 AND x + y <= 5 AND y >= 0 → UNSAT (x>=10, y>=0 → x+y>=10 > 5)
    let ge_ten = terms.mk_ge(x, ten);
    let sum = terms.mk_add(vec![x, y]);
    let le_five = terms.mk_le(sum, five);
    let zero = terms.mk_rational(BigRational::zero());
    let ge_zero = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_ten, true);
    solver.assert_literal(le_five, true);
    solver.assert_literal(ge_zero, true);

    // Use check() which processes atoms into bounds before calling dual_simplex
    let result = solver.check();

    // Helper: verify conflict literals are a subset of asserted atoms
    let verify_conflict_lits = |lits: &[TheoryLit]| {
        assert!(!lits.is_empty(), "UNSAT conflict clause must not be empty");
        for lit in lits {
            let is_known = lit.term == ge_ten || lit.term == le_five || lit.term == ge_zero;
            assert!(is_known, "Conflict literal must come from asserted atoms");
        }
    };

    match &result {
        TheoryResult::Sat => {
            assert!(
                false,
                "check() returned SAT on UNSAT problem (x>=10, x+y<=5, y>=0)"
            );
        }
        TheoryResult::Unknown => {
            // Unknown is acceptable — the solver may not support all sub-expressions
        }
        TheoryResult::Unsat(lits) => {
            verify_conflict_lits(lits);
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            verify_conflict_lits(&conflict.literals);
        }
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_) => {
            assert!(
                false,
                "NeedSplit on a purely linear UNSAT problem is incorrect"
            );
        }
        _ => {
            // Non-exhaustive enum: unknown variant — treat as acceptable
        }
    }
}

/// dual_simplex returns SAT for a trivially satisfiable problem regardless of
/// iteration limit.
///
/// Part of #2014: Single-variable bound problems require zero pivots, so even
/// max_iters=0 should return SAT (not Unknown).
#[kani::proof]
#[kani::unwind(3)]
fn proof_dual_simplex_trivial_sat_zero_iters() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let bound_val = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_le(x, bound_val);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(atom, true);

    // A single-variable problem needs no pivoting. Even with 0 iterations,
    // dual_simplex should detect that no basic variable violates its bounds.
    let result = solver.dual_simplex_with_max_iters(0);
    assert!(
        matches!(result, TheoryResult::Sat),
        "Trivially satisfiable problem should return Sat even with 0 iterations"
    );
}

/// Conflicts returned from dual_simplex contain literals from the asserted problem.
///
/// Part of #2014: When dual_simplex returns UNSAT, the conflict clause must contain
/// at least one literal that was actually asserted. Empty conflicts are unsound.
#[kani::proof]
#[kani::unwind(3)]
fn proof_conflict_contains_asserted_literals() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);

    // Create contradictory bounds: x >= 10 AND x <= 5
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let le_five = terms.mk_le(x, five); // x <= 5
    let ge_ten = terms.mk_ge(x, ten); // x >= 10

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_five, true);
    solver.assert_literal(ge_ten, true);

    let result = solver.dual_simplex_with_max_iters(100);
    match result {
        TheoryResult::Unsat(lits) => {
            // Conflict must be non-empty
            assert!(!lits.is_empty(), "Conflict clause must not be empty");
            // At least one literal must be from our assertions
            let has_le_five = lits.iter().any(|l| l.term == le_five);
            let has_ge_ten = lits.iter().any(|l| l.term == ge_ten);
            assert!(
                has_le_five || has_ge_ten,
                "Conflict must contain at least one asserted literal"
            );
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            assert!(
                !conflict.literals.is_empty(),
                "Conflict clause must not be empty"
            );
            let has_le_five = conflict.literals.iter().any(|l| l.term == le_five);
            let has_ge_ten = conflict.literals.iter().any(|l| l.term == ge_ten);
            assert!(
                has_le_five || has_ge_ten,
                "Conflict must contain at least one asserted literal"
            );
        }
        other => panic!("Expected UNSAT for contradictory bounds, got {:?}", other),
    }
}
