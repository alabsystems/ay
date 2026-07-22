// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// suggest_phase() tests — LP-model-consistent phase selection (#4919)
// ============================================================================

/// suggest_phase on a non-strict inequality (x <= 5) when model satisfies it.
/// With x in [0, 10] (default model x=0), x <= 5 is true.
#[test]
fn test_suggest_phase_nonstrict_le_satisfied() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_le(x, five); // x <= 5

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom);

    // Default model: x = 0. 0 <= 5 satisfied → suggest true.
    let phase = solver.suggest_phase(atom);
    assert_eq!(phase, Some(true), "x=0, x<=5 satisfied → true");
}

/// suggest_phase on a non-strict inequality (x <= 5) when model violates it.
/// After asserting x >= 10, model has x = 10, so x <= 5 is false.
#[test]
fn test_suggest_phase_nonstrict_le_violated() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let atom_le = terms.mk_le(x, five); // x <= 5
    let atom_ge = terms.mk_ge(x, ten); // x >= 10

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom_le);
    solver.assert_literal(atom_ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Model: x = 10. 10 <= 5 false → suggest false.
    let phase = solver.suggest_phase(atom_le);
    assert_eq!(phase, Some(false), "x=10, x<=5 violated → false");
}

/// suggest_phase on a non-strict inequality at the boundary (x <= 5, x = 5).
/// At x = 5, x <= 5 is satisfied → suggest true.
#[test]
fn test_suggest_phase_nonstrict_le_boundary() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five_1 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let five_2 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let five_3 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom_le = terms.mk_le(x, five_1); // x <= 5
    let atom_ge = terms.mk_ge(x, five_2); // x >= 5
    let atom_le2 = terms.mk_le(x, five_3); // x <= 5 (to force x = 5)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom_le);
    solver.assert_literal(atom_ge, true);
    solver.assert_literal(atom_le2, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Model: x = 5. 5 <= 5 satisfied → suggest true.
    let phase = solver.suggest_phase(atom_le);
    assert_eq!(phase, Some(true), "x=5, x<=5 at boundary → true");
}

/// suggest_phase on a strict inequality (x < 5) when model satisfies it.
#[test]
fn test_suggest_phase_strict_lt_satisfied() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_lt(x, five); // x < 5

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom);

    // Default model: x = 0. 0 < 5 satisfied → suggest true.
    let phase = solver.suggest_phase(atom);
    assert_eq!(phase, Some(true), "x=0, x<5 satisfied → true");
}

/// suggest_phase on a strict inequality (x < 5) when model violates it.
#[test]
fn test_suggest_phase_strict_lt_violated() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let atom_lt = terms.mk_lt(x, five); // x < 5
    let atom_ge = terms.mk_ge(x, ten); // x >= 10

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom_lt);
    solver.assert_literal(atom_ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Model: x = 10. 10 < 5 false → suggest false.
    let phase = solver.suggest_phase(atom_lt);
    assert_eq!(phase, Some(false), "x=10, x<5 violated → false");
}

/// suggest_phase on a strict inequality at the boundary (x < 5, x = 5).
/// At x = 5, strict x < 5 is NOT satisfied (5 < 5 is false) → suggest false.
///
/// #8008: Previously returned None, now returns Some(false) to match Z3's
/// compare_values() behavior. Z3 returns l_false for strict inequalities at
/// the boundary. Returning None caused the SAT solver to use its default
/// phase (positive), which is theory-inconsistent at the boundary.
#[test]
fn test_suggest_phase_strict_lt_boundary_returns_false() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five_1 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let five_2 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let five_3 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom_lt = terms.mk_lt(x, five_1); // x < 5
    let atom_ge = terms.mk_ge(x, five_2); // x >= 5
    let atom_le = terms.mk_le(x, five_3); // x <= 5

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom_lt);
    solver.assert_literal(atom_ge, true);
    solver.assert_literal(atom_le, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Model: x = 5. Strict x < 5 at boundary: 5 < 5 is false → suggest false.
    let phase = solver.suggest_phase(atom_lt);
    assert_eq!(phase, Some(false), "x=5, x<5 strict at boundary → false");
}

/// suggest_phase on an equality atom (x = 5) when model satisfies it.
#[test]
fn test_suggest_phase_equality_satisfied() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five_1 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let five_2 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let five_3 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let eq_atom = terms.mk_eq(x, five_1); // x = 5
    let atom_ge = terms.mk_ge(x, five_2); // x >= 5
    let atom_le = terms.mk_le(x, five_3); // x <= 5

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.assert_literal(atom_ge, true);
    solver.assert_literal(atom_le, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Model: x = 5. (= x 5) evaluates to 0 → is_zero → true.
    let phase = solver.suggest_phase(eq_atom);
    assert_eq!(phase, Some(true), "x=5, (= x 5) satisfied → true");
}

/// suggest_phase on an equality atom (x = 5) when model violates it.
#[test]
fn test_suggest_phase_equality_violated() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let eq_atom = terms.mk_eq(x, five); // x = 5
    let atom_ge = terms.mk_ge(x, ten); // x >= 10

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.assert_literal(atom_ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Model: x = 10. (= x 5) evaluates to 5 → not zero → false.
    let phase = solver.suggest_phase(eq_atom);
    assert_eq!(phase, Some(false), "x=10, (= x 5) violated → false");
}

/// suggest_phase on an unregistered atom returns None.
#[test]
fn test_suggest_phase_unknown_atom_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_le(x, five); // x <= 5

    let solver = LraSolver::new(&terms);
    // Do NOT register the atom
    let phase = solver.suggest_phase(atom);
    assert_eq!(phase, None, "unregistered atom → None");
}

/// Phase hint cache is populated after check() returns Sat and
/// save_feasible_snapshot() fires. Subsequent suggest_phase() calls
/// should return the same values as a fresh evaluation.
#[test]
fn test_phase_hint_cache_populated_after_check() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));
    let atom_le = terms.mk_le(x, seven); // x <= 7
    let atom_ge = terms.mk_ge(x, three); // x >= 3

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom_le);
    solver.register_atom(atom_ge);
    solver.assert_literal(atom_ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // After check() returns Sat, the phase hint cache should be populated.
    // x >= 3, model has x = 3. x <= 7 is satisfied (3 <= 7 → true).
    let phase_le = solver.suggest_phase(atom_le);
    assert_eq!(phase_le, Some(true), "x=3, x<=7 → true (from cache)");

    // x >= 3 is satisfied (3 >= 3 → true).
    let phase_ge = solver.suggest_phase(atom_ge);
    assert_eq!(phase_ge, Some(true), "x=3, x>=3 → true (from cache)");

    // The cache should have entries for both atoms.
    assert!(
        !solver.phase_hint_cache.is_empty(),
        "phase hint cache should be populated after feasible check"
    );
}
