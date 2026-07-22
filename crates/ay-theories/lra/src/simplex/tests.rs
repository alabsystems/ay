// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::{TermId, TermStore};
use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};

fn int(value: i64) -> BigRational {
    BigRational::from(BigInt::from(value))
}

fn frac(num: i64, den: i64) -> BigRational {
    BigRational::new(BigInt::from(num), BigInt::from(den))
}

fn bound_with_reason(
    value: i64,
    reason: u32,
    reason_value: bool,
    scale_num: i64,
    scale_den: i64,
) -> crate::Bound {
    crate::Bound::new(
        int(value).into(),
        vec![TermId::new(reason)],
        vec![reason_value],
        vec![frac(scale_num, scale_den).into()],
        false,
    )
}

fn basic_var(value: i64, lower: Option<crate::Bound>, upper: Option<crate::Bound>) -> VarInfo {
    VarInfo {
        value: InfRational::from_rational(int(value)),
        lower,
        upper,
        status: Some(VarStatus::Basic(0)),
    }
}

fn nonbasic_var(lower: Option<crate::Bound>, upper: Option<crate::Bound>) -> VarInfo {
    VarInfo {
        value: InfRational::from_rational(int(0)),
        lower,
        upper,
        status: Some(VarStatus::NonBasic),
    }
}

/// #8764: Populate `solver.asserted` from every bound reason on every var.
///
/// The stale-reason guard added to `build_conflict_with_farkas` rejects any
/// conflict whose literals are not currently asserted. Isolated unit tests
/// that construct vars directly must therefore pre-populate `asserted`
/// with the reasons they intend to cite.
fn populate_asserted_from_vars(solver: &mut LraSolver) {
    for var in &solver.vars {
        for bound in [var.lower.as_ref(), var.upper.as_ref()]
            .into_iter()
            .flatten()
        {
            for (term, val) in bound.reason_pairs() {
                if !term.is_sentinel() {
                    solver.asserted.insert(term, val);
                }
            }
        }
    }
}

#[test]
fn test_build_conflict_with_farkas_lower_violation_scales_basic_and_active_bounds() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let basic_reason = TermId::new(10);
    let upper_reason = TermId::new(11);
    let lower_reason = TermId::new(12);

    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(1, 10, true, 1, 2)), None),
        nonbasic_var(None, Some(bound_with_reason(4, 11, false, 1, 4))),
        nonbasic_var(Some(bound_with_reason(-2, 12, true, 2, 3)), None),
    ];
    solver.rows = vec![TableauRow::new(0, vec![(1, int(3)), (2, int(-5))], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);
    let farkas = conflict
        .farkas
        .expect("expected complete Farkas annotation");

    assert_eq!(
        conflict.literals,
        vec![
            TheoryLit::new(basic_reason, true),
            TheoryLit::new(upper_reason, false),
            TheoryLit::new(lower_reason, true),
        ]
    );
    assert_eq!(
        farkas.coefficients,
        vec![
            Rational64::new(1, 2),
            Rational64::new(3, 4),
            Rational64::new(10, 3),
        ]
    );
}

#[test]
fn test_dual_simplex_iteration_budget_is_bland_gated() {
    assert_eq!(LraSolver::dual_simplex_iteration_budget(42, false), 42);
    assert_eq!(LraSolver::dual_simplex_iteration_budget(42, true), 420);
    assert_eq!(
        LraSolver::dual_simplex_iteration_budget(2_000_000, true),
        10_000_000
    );
}

#[test]
fn test_build_conflict_with_farkas_upper_violation_uses_upper_and_lower_active_sides() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let basic_reason = TermId::new(20);
    let lower_reason = TermId::new(21);
    let upper_reason = TermId::new(22);
    let wrong_upper_reason = TermId::new(23);
    let wrong_lower_reason = TermId::new(24);

    solver.vars = vec![
        basic_var(10, None, Some(bound_with_reason(4, 20, false, 3, 2))),
        nonbasic_var(
            Some(bound_with_reason(-1, 21, true, 5, 4)),
            Some(bound_with_reason(6, 23, false, 1, 1)),
        ),
        nonbasic_var(
            Some(bound_with_reason(-3, 24, true, 1, 1)),
            Some(bound_with_reason(2, 22, false, 1, 3)),
        ),
    ];
    solver.rows = vec![TableauRow::new(0, vec![(1, int(2)), (2, int(-7))], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);
    let farkas = conflict
        .farkas
        .expect("expected complete Farkas annotation");

    assert_eq!(
        conflict.literals,
        vec![
            TheoryLit::new(basic_reason, false),
            TheoryLit::new(lower_reason, true),
            TheoryLit::new(upper_reason, false),
        ]
    );
    assert!(
        conflict
            .literals
            .iter()
            .all(|lit| lit.term != wrong_upper_reason && lit.term != wrong_lower_reason),
        "conflict must use the active-side bounds only"
    );
    assert_eq!(
        farkas.coefficients,
        vec![
            Rational64::new(3, 2),
            Rational64::new(5, 2),
            Rational64::new(7, 3),
        ]
    );
}

#[test]
fn test_build_conflict_with_farkas_reasonless_active_bound_returns_empty_conflict() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    solver.vars = vec![
        basic_var(10, None, Some(bound_with_reason(4, 30, true, 1, 1))),
        nonbasic_var(
            Some(crate::Bound::without_reasons(int(-1).into(), false)),
            Some(bound_with_reason(5, 31, false, 1, 1)),
        ),
    ];
    solver.rows = vec![TableauRow::new(0, vec![(1, int(2))], int(0))];

    let conflict = solver.build_conflict_with_farkas(0);

    assert!(
        conflict.literals.is_empty(),
        "reasonless active bounds must degrade to an empty conflict"
    );
    assert!(
        conflict.farkas.is_none(),
        "reasonless active bounds must not keep a partial Farkas certificate"
    );
}

/// Single-variable conflict: the basic var violates its lower bound and the
/// row has no non-basic variable coefficients. The conflict should contain
/// only the basic variable's bound reason.
#[test]
fn test_build_conflict_with_farkas_single_variable_lower_violation() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let basic_reason = TermId::new(40);

    // Basic var at value 0, lower bound 5 → violates lower.
    // Row: x0 = 0 (no non-basic terms).
    solver.vars = vec![basic_var(
        0,
        Some(bound_with_reason(5, 40, true, 1, 1)),
        None,
    )];
    solver.rows = vec![TableauRow::new(0, vec![], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);
    let farkas = conflict
        .farkas
        .expect("single-variable conflict should have Farkas annotation");

    assert_eq!(conflict.literals, vec![TheoryLit::new(basic_reason, true)]);
    assert_eq!(farkas.coefficients, vec![Rational64::new(1, 1)]);
}

/// Sentinel-only basic bound with real non-basic bound reasons: the conflict
/// is partial (sentinel-only flag set) but still yields literals from the
/// non-basic bounds. Farkas metadata is dropped.
#[test]
fn test_build_conflict_with_farkas_sentinel_basic_real_nonbasic_partial() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let nb_reason = TermId::new(50);

    // Basic var lower bound has only sentinel reasons.
    let sentinel_bound = crate::Bound::new(
        int(5).into(),
        vec![TermId::SENTINEL],
        vec![true],
        vec![int(1).into()],
        false,
    );
    // Non-basic var has a real upper bound reason.
    solver.vars = vec![
        basic_var(0, Some(sentinel_bound), None),
        nonbasic_var(None, Some(bound_with_reason(3, 50, false, 1, 1))),
    ];
    // Row: x0 = 2*x1. Basic var at 0, lower bound 5 → lower violation.
    // Non-basic x1 has coeff +2 → active bound is upper for lower violation.
    solver.rows = vec![TableauRow::new(0, vec![(1, int(2))], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);

    // Partial conflict: should have the non-basic literal but no Farkas.
    assert_eq!(conflict.literals, vec![TheoryLit::new(nb_reason, false)]);
    assert!(
        conflict.farkas.is_none(),
        "sentinel-only basic bound should drop Farkas metadata"
    );
}

/// All-sentinel conflict: basic var has sentinel-only reasons and there are
/// no non-basic variables. Should return empty conflict.
#[test]
fn test_build_conflict_with_farkas_all_sentinel_returns_empty() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let sentinel_bound = crate::Bound::new(
        int(5).into(),
        vec![TermId::SENTINEL],
        vec![true],
        vec![int(1).into()],
        false,
    );
    solver.vars = vec![basic_var(0, Some(sentinel_bound), None)];
    solver.rows = vec![TableauRow::new(0, vec![], int(0))];

    let conflict = solver.build_conflict_with_farkas(0);

    assert!(
        conflict.literals.is_empty(),
        "all-sentinel conflict should degrade to empty"
    );
}

/// Multiple reasons per bound: a single bound can carry multiple reason atoms
/// (e.g., equality x=4 implies both x>=4 and x<=4, or a derived bound from
/// multiple constraints). Each reason gets its own Farkas coefficient.
#[test]
fn test_build_conflict_with_farkas_multi_reason_bound() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let reason_a = TermId::new(60);
    let reason_b = TermId::new(61);
    let nb_reason = TermId::new(62);

    // Basic var lower bound has two reason atoms with distinct scales.
    let multi_bound = crate::Bound::new(
        int(3).into(),
        vec![reason_a, reason_b],
        vec![true, false],
        vec![frac(1, 3).into(), frac(2, 3).into()],
        false,
    );
    solver.vars = vec![
        basic_var(0, Some(multi_bound), None),
        nonbasic_var(None, Some(bound_with_reason(1, 62, true, 1, 1))),
    ];
    // Row: x0 = x1. Lower violation (value 0 < bound 3).
    // Non-basic x1 has coeff +1 → active bound is upper.
    solver.rows = vec![TableauRow::new(0, vec![(1, int(1))], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);
    let farkas = conflict
        .farkas
        .expect("multi-reason bound should produce Farkas annotation");

    assert_eq!(
        conflict.literals,
        vec![
            TheoryLit::new(reason_a, true),
            TheoryLit::new(reason_b, false),
            TheoryLit::new(nb_reason, true),
        ]
    );
    // Basic bound scales: 1/3 and 2/3.
    // Non-basic: |coeff|=1 * bound_scale=1/1 = 1.
    assert_eq!(
        farkas.coefficients,
        vec![
            Rational64::new(1, 3),
            Rational64::new(2, 3),
            Rational64::new(1, 1),
        ]
    );
}

/// Duplicate literal deduplication: when the same constraint reason appears
/// in both the basic and non-basic bounds, the deduplicated conflict merges
/// them with combined Farkas coefficients.
#[test]
fn test_build_conflict_with_farkas_duplicate_literal_combines_coefficients() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let shared_reason = TermId::new(70);

    // Both basic lower bound and non-basic upper bound cite the same reason.
    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(5, 70, true, 1, 1)), None),
        nonbasic_var(None, Some(bound_with_reason(2, 70, true, 1, 1))),
    ];
    // Row: x0 = 3*x1. Lower violation. coeff +3 → active is upper bound.
    solver.rows = vec![TableauRow::new(0, vec![(1, int(3))], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);

    // After deduplication: one literal (shared_reason, true).
    // Combined coefficient: basic_scale(1) + |coeff(3)| * nb_scale(1) = 1 + 3 = 4.
    assert_eq!(conflict.literals, vec![TheoryLit::new(shared_reason, true)]);
    let farkas = conflict
        .farkas
        .expect("deduplicated conflict should keep merged Farkas");
    assert_eq!(farkas.coefficients, vec![Rational64::new(4, 1)]);
}

/// Non-basic variable that is actually Basic (e.g., after pivots the row.coeffs
/// still references a var that became basic for another row). This variable
/// should be skipped — only NonBasic vars contribute to the conflict.
#[test]
fn test_build_conflict_with_farkas_skips_basic_vars_in_row_coeffs() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let basic_reason = TermId::new(80);
    let nb_reason = TermId::new(81);
    let other_basic_reason = TermId::new(82);

    // var 0: basic (row 0), value 0, lower bound 5 → violates lower.
    // var 1: NonBasic with upper bound.
    // var 2: Basic (row 1) — should be SKIPPED even though row 0 references it.
    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(5, 80, true, 1, 1)), None),
        nonbasic_var(None, Some(bound_with_reason(3, 81, false, 1, 1))),
        VarInfo {
            value: InfRational::from_rational(int(0)),
            lower: Some(bound_with_reason(1, 82, true, 1, 1)),
            upper: None,
            status: Some(VarStatus::Basic(1)),
        },
    ];
    // Row 0: x0 = 2*x1 + 4*x2. Both x1 and x2 appear in coeffs.
    solver.rows = vec![
        TableauRow::new(0, vec![(1, int(2)), (2, int(4))], int(0)),
        TableauRow::new(2, vec![], int(0)),
    ];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);

    // var 2 (Basic) should be skipped. Only basic_reason and nb_reason appear.
    assert!(
        conflict
            .literals
            .iter()
            .all(|lit| lit.term != other_basic_reason),
        "basic var in row coefficients must be skipped"
    );
    assert_eq!(
        conflict.literals,
        vec![
            TheoryLit::new(basic_reason, true),
            TheoryLit::new(nb_reason, false),
        ]
    );
}

/// Fractional tableau coefficients: verify that non-integer coefficients in
/// the row correctly scale the Farkas annotation. Row: x0 = (3/2)*x1.
#[test]
fn test_build_conflict_with_farkas_fractional_tableau_coefficients() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let basic_reason = TermId::new(90);
    let nb_reason = TermId::new(91);

    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(5, 90, true, 1, 1)), None),
        nonbasic_var(None, Some(bound_with_reason(2, 91, false, 1, 1))),
    ];
    // Row: x0 = (3/2)*x1. Lower violation. Coeff 3/2 positive → active is upper.
    solver.rows = vec![TableauRow::new(0, vec![(1, frac(3, 2))], int(0))];
    populate_asserted_from_vars(&mut solver);

    let conflict = solver.build_conflict_with_farkas(0);
    let farkas = conflict
        .farkas
        .expect("fractional coefficients should produce Farkas annotation");

    assert_eq!(
        conflict.literals,
        vec![
            TheoryLit::new(basic_reason, true),
            TheoryLit::new(nb_reason, false),
        ]
    );
    // Basic scale: 1/1. Non-basic: |3/2| * 1/1 = 3/2.
    assert_eq!(
        farkas.coefficients,
        vec![Rational64::new(1, 1), Rational64::new(3, 2)]
    );
}
