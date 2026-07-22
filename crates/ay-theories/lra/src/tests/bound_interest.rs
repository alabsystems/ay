// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::ColEntry;
// -- bound_is_interesting unit tests (#6615 Packet 2) --

/// Helper: create an AtomRef for testing bound_is_interesting.
fn make_atom_ref(term_id: u32, bound: i64, is_upper: bool, strict: bool) -> AtomRef {
    AtomRef {
        term: TermId(term_id),
        bound_value: Rational::from(bound),
        is_upper,
        strict,
    }
}

/// No atoms registered for a variable → bound_is_interesting returns true
/// (conservative: variable may be slack/auxiliary needed for cascading).
#[test]
fn test_bound_is_interesting_no_atoms_returns_true() {
    let terms = TermStore::new();
    let solver = LraSolver::new(&terms);
    // var 99 has no entry in atom_index
    let val = Rational::new(5, 1);
    assert!(solver.bound_is_interesting(99, true, &val));
    assert!(solver.bound_is_interesting(99, false, &val));
}

/// Empty atom list for a variable → bound_is_interesting returns true.
#[test]
fn test_bound_is_interesting_empty_atoms_returns_true() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver.atom_index.insert(0, Vec::new());
    let val = Rational::new(5, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
    assert!(solver.bound_is_interesting(0, false, &val));
}

/// Upper bound value <= atom bound (non-strict) → interesting.
/// Upper bound 3 can imply atom `var <= 5` (non-strict: 3 <= 5).
#[test]
fn test_bound_is_interesting_upper_nonstrict_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    // Atom: var <= 5 (non-strict upper)
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, true, false)]);
    // New upper bound = 3: 3 <= 5 → interesting
    let val = Rational::new(3, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
}

/// Upper bound value > atom bound (non-strict) → not interesting.
/// Upper bound 7 cannot imply atom `var <= 5` (7 > 5).
#[test]
fn test_bound_is_interesting_upper_nonstrict_not_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, true, false)]);
    // New upper bound = 7: 7 > 5 → not interesting
    let val = Rational::new(7, 1);
    assert!(!solver.bound_is_interesting(0, true, &val));
}

/// Upper bound value == atom bound (non-strict) → interesting.
/// Exact match: new upper 5 implies atom `var <= 5`.
#[test]
fn test_bound_is_interesting_upper_nonstrict_exact() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, true, false)]);
    let val = Rational::new(5, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
}

/// Upper bound value == atom bound (strict atom: var < 5) → not interesting.
/// For strict atom, need value < bound, not value <= bound.
#[test]
fn test_bound_is_interesting_upper_strict_exact_not_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    // Atom: var < 5 (strict upper)
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, true, true)]);
    // New upper bound = 5: 5 is not < 5 → not interesting
    let val = Rational::new(5, 1);
    assert!(!solver.bound_is_interesting(0, true, &val));
}

/// Upper bound value < strict atom bound → interesting.
#[test]
fn test_bound_is_interesting_upper_strict_below_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, true, true)]);
    // New upper bound = 4: 4 < 5 → interesting
    let val = Rational::new(4, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
}

/// Lower bound value >= atom bound (non-strict) → interesting.
/// Lower bound 7 can imply atom `var >= 5` (7 >= 5).
#[test]
fn test_bound_is_interesting_lower_nonstrict_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    // Atom: var >= 5 (non-strict lower)
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, false, false)]);
    let val = Rational::new(7, 1);
    assert!(solver.bound_is_interesting(0, false, &val));
}

/// Lower bound value < atom bound → not interesting.
#[test]
fn test_bound_is_interesting_lower_nonstrict_not_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, false, false)]);
    // New lower bound = 3: 3 < 5 → not interesting
    let val = Rational::new(3, 1);
    assert!(!solver.bound_is_interesting(0, false, &val));
}

/// Lower bound value == atom bound (strict atom: var > 5) → not interesting.
#[test]
fn test_bound_is_interesting_lower_strict_exact_not_implies() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    // Atom: var > 5 (strict lower)
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, false, true)]);
    let val = Rational::new(5, 1);
    assert!(!solver.bound_is_interesting(0, false, &val));
}

/// Direction mismatch: upper bound + lower atom only → still interesting.
/// #6697: When no same-direction unassigned atom exists, retain the bound
/// for cross-row cascading and cross-solver queries (has_implied_bounds).
#[test]
fn test_bound_is_interesting_direction_mismatch_retained() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    // Only lower atom (var >= 5), but new bound is upper direction
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, false, false)]);
    // Upper bound = 3: no same-direction unassigned atom → retained for downstream consumers
    let val = Rational::new(3, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
}

/// Already-asserted atoms are skipped; if all same-direction atoms asserted → still interesting.
/// #6697: Retained for cross-solver queries (has_implied_bounds) and cascading.
#[test]
fn test_bound_is_interesting_all_asserted_retained() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    let atom_term = TermId(100);
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(100, 5, true, false)]);
    // Mark the atom as already asserted
    solver.asserted.insert(atom_term, true);
    // Upper bound = 3: atom already asserted → no unassigned same-direction → retained
    let val = Rational::new(3, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
}

/// Mixed: one asserted atom (skipped) + one unassigned atom that matches.
#[test]
fn test_bound_is_interesting_mixed_asserted_and_unassigned() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver.atom_index.insert(
        0,
        vec![
            make_atom_ref(100, 5, true, false), // var <= 5, will be asserted
            make_atom_ref(101, 8, true, false), // var <= 8, unassigned
        ],
    );
    solver.asserted.insert(TermId(100), true);
    // Upper bound = 3: first atom asserted (skip), second atom: 3 <= 8 → interesting
    let val = Rational::new(3, 1);
    assert!(solver.bound_is_interesting(0, true, &val));
}

/// Regression for #6697: compute_implied_bounds retains a derived lower bound
/// on a variable that has only upper-direction atoms. has_implied_bounds()
/// must return true so AUFLIRA cross-sort propagation can request a split.
///
/// Setup: row 0 has y (basic) = x (nonbasic). y has lower bound >= 0.
/// The single-unbounded derivation produces x >= 0 (lower). x has only an
/// upper atom (x <= 10). The old gate discarded the lower bound because no
/// same-direction (lower) unassigned atom existed; #6697 fix retains it.
#[test]
fn test_has_implied_bounds_survives_direction_mismatch_6697() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let bound = |value: i64, reason: u32| {
        Bound::new(
            BigRational::from(BigInt::from(value)).into(),
            vec![TermId::new(reason)],
            vec![true],
            vec![Rational::one()],
            false,
        )
    };

    // var 0 = x (nonbasic, no direct bounds)
    // var 1 = y (basic, row 0, lower >= 0)
    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, 900)),
            upper: None,
            status: Some(VarStatus::Basic(0)),
        },
    ];

    // Row 0: basic_var=1 (y), coeffs=[(0, +1)] → raw: y = 0 + 1*x = x.
    // Analysis equation: y + (-1)*x = 0 → y - x = 0.
    // Lower direction: y has lb=0, x is unbounded (eq_c=-1, negative → needs upper).
    // Single-unbounded derivation: bound_val = (0-0)/(-1) = 0, is_upper = false → x >= 0.
    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(1)))],
        BigRational::zero(),
    )];
    solver.col_index = vec![Vec::new(); 2];
    solver.col_index[0].push(ColEntry::new(0, 0));
    solver.basic_var_to_row.insert(1, 0);
    solver.touched_rows.insert(0);

    // Register an upper-only atom on var 0 (x). The derived bound is lower,
    // so there is no same-direction unassigned atom → #6697 retention gate.
    solver
        .atom_index
        .insert(0, vec![make_atom_ref(200, 10, true, false)]); // x <= 10

    // Map term 50 → var 0 so has_implied_bounds can look it up.
    let term_x = TermId(50);
    solver.term_to_var.insert(term_x, 0);

    solver.compute_implied_bounds();

    assert!(
        solver.has_implied_bounds(term_x),
        "#6697: lower bound derived from row must survive when only upper atoms exist"
    );

    // Verify the actual bound value: x >= 0.
    let x_lower = solver.implied_bounds[0]
        .0
        .as_ref()
        .expect("x should have an implied lower bound");
    assert_eq!(x_lower.value, Rational::new(0, 1));
}
