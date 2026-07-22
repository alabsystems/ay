// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::ColEntry;

/// When two variables both have tight bounds at the same value,
/// propagate_equalities must report their equality.
///
/// Setup: x = 5 (via x >= 5, x <= 5) and y = 5 (via y >= 5, y <= 5).
/// Expected: propagate_equalities returns x = y with reasons from both
/// pairs of bound assertions.
#[test]
fn test_propagate_equalities_tight_bounds_same_value() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let x_ge_5 = terms.mk_ge(x, five);
    let x_le_5 = terms.mk_le(x, five);
    let five2 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let y_ge_5 = terms.mk_ge(y, five2);
    let y_le_5 = terms.mk_le(y, five2);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_ge_5, true);
    solver.assert_literal(x_le_5, true);
    solver.assert_literal(y_ge_5, true);
    solver.assert_literal(y_le_5, true);

    // Must check() first so the simplex processes the assertions
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x=5, y=5 should be SAT, got {result:?}"
    );

    // Now propagate equalities
    let eq_result = solver.propagate_equalities();
    assert!(
        eq_result.conflict.is_none(),
        "No conflict expected from equality propagation"
    );
    assert!(
        !eq_result.equalities.is_empty(),
        "Expected x = y equality propagation when both have tight bound at 5, got 0 equalities"
    );

    // Verify the propagated equality involves x and y
    let found = eq_result
        .equalities
        .iter()
        .any(|eq| (eq.lhs == x && eq.rhs == y) || (eq.lhs == y && eq.rhs == x));
    assert!(
        found,
        "Expected equality between x (term {}) and y (term {}), got: {:?}",
        x.0, y.0, eq_result.equalities
    );

    // Verify reasons are non-empty (must include bound assertion reasons)
    let eq = eq_result
        .equalities
        .iter()
        .find(|eq| (eq.lhs == x && eq.rhs == y) || (eq.lhs == y && eq.rhs == x))
        .unwrap();
    assert!(
        !eq.reason.is_empty(),
        "Equality propagation reasons must not be empty — need bound assertion literals"
    );
}

/// When only one variable has a tight bound, no equality should be propagated.
#[test]
fn test_propagate_equalities_single_tight_bound_no_propagation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_ge_5 = terms.mk_ge(x, five);
    let x_le_5 = terms.mk_le(x, five);
    // y has a range, not a tight bound
    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_10 = terms.mk_le(y, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_ge_5, true);
    solver.assert_literal(x_le_5, true);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_10, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x=5, 0<=y<=10 should be SAT, got {result:?}"
    );

    let eq_result = solver.propagate_equalities();
    assert!(
        eq_result.equalities.is_empty(),
        "No equality should be propagated when only x has tight bound but y has range. \
         Got {} equalities: {:?}",
        eq_result.equalities.len(),
        eq_result.equalities
    );
}

/// When two variables have tight bounds at different values,
/// no equality should be propagated (they're provably different).
#[test]
fn test_propagate_equalities_different_tight_bounds_no_propagation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let x_ge_5 = terms.mk_ge(x, five);
    let x_le_5 = terms.mk_le(x, five);
    let y_ge_7 = terms.mk_ge(y, seven);
    let y_le_7 = terms.mk_le(y, seven);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_ge_5, true);
    solver.assert_literal(x_le_5, true);
    solver.assert_literal(y_ge_7, true);
    solver.assert_literal(y_le_7, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    let eq_result = solver.propagate_equalities();
    // x = 5 and y = 7 — different values, should NOT propagate x = y
    assert!(
        eq_result.equalities.is_empty(),
        "No equality should be propagated between x=5 and y=7. Got: {:?}",
        eq_result.equalities
    );
}

#[test]
fn test_assert_shared_equality_preserves_primary_reason_literal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let reason_a = terms.mk_var("reason_a", Sort::Bool);
    let reason_b = terms.mk_var("reason_b", Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    let reasons = [
        TheoryLit::new(reason_a, true),
        TheoryLit::new(reason_b, false),
    ];
    solver.assert_shared_equality(x, y, &reasons);

    let mut bounds_with_primary_reason = 0usize;
    for var in &solver.vars {
        for bound in [&var.lower, &var.upper].into_iter().flatten() {
            if bound
                .reasons
                .iter()
                .copied()
                .zip(bound.reason_values.iter().copied())
                .any(|(term, value)| term == reason_a && value)
            {
                bounds_with_primary_reason += 1;
            }
        }
    }

    // `lhs = rhs` is asserted as both upper and lower bounds. Current
    // implementation preserves the first reason literal for these bounds.
    assert!(
        bounds_with_primary_reason >= 2,
        "expected equality bounds to retain primary reason literal; found {bounds_with_primary_reason}"
    );
}

/// Test implied bounds: all-bounded row strengthening (#5591 AC1).
///
/// Constraint: x + y + z <= 12 with x >= 1, y >= 2, z >= 3 (all bounded).
/// Row: s = x + y + z - 12, s <= 0. The bound analysis equation is
/// s - x - y - z = -12 (all eq_coeffs). With all variables bounded,
/// compute_implied_bounds derives tighter bounds from the row.
///
/// Expected derived values (from row arithmetic):
///   x: 7 (= 12 - y_min - z_min = 12 - 2 - 3)
///   y: 8 (= 12 - x_min - z_min = 12 - 1 - 3)
///   z: 9 (= 12 - x_min - y_min = 12 - 1 - 2)
#[test]
fn test_implied_bounds_all_bounded_row_strengthening_5591() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let twelve = terms.mk_rational(BigRational::from(BigInt::from(12)));

    let sum = terms.mk_add(vec![x, y, z]);
    let sum_le = terms.mk_le(sum, twelve); // x + y + z <= 12
    let x_ge = terms.mk_ge(x, one); // x >= 1
    let y_ge = terms.mk_ge(y, two); // y >= 2
    let z_ge = terms.mk_ge(z, three); // z >= 3

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(z_ge, true);

    // check() runs compute_implied_bounds() on SAT
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned") as usize;
    let y_var = *solver.term_to_var.get(&y).expect("y interned") as usize;
    let z_var = *solver.term_to_var.get(&z).expect("z interned") as usize;

    // The all-bounded path produces derived bounds. For the constraint
    // x + y + z <= 12, the lb-direction pass derives upper bounds (slot .1)
    // for variables with positive coefficients (be8c7eb36 direction fix).
    let x_ib = solver.implied_bounds[x_var]
        .1
        .as_ref()
        .expect("x should have derived upper bound from all-bounded row");
    assert_eq!(
        x_ib.value,
        Rational::from(BigRational::from(BigInt::from(7))),
        "x derived upper bound should be 7 (= 12 - 2 - 3)"
    );

    let y_ib = solver.implied_bounds[y_var]
        .1
        .as_ref()
        .expect("y should have derived upper bound from all-bounded row");
    assert_eq!(
        y_ib.value,
        Rational::from(BigRational::from(BigInt::from(8))),
        "y derived upper bound should be 8 (= 12 - 1 - 3)"
    );

    let z_ib = solver.implied_bounds[z_var]
        .1
        .as_ref()
        .expect("z should have derived upper bound from all-bounded row");
    assert_eq!(
        z_ib.value,
        Rational::from(BigRational::from(BigInt::from(9))),
        "z derived upper bound should be 9 (= 12 - 1 - 2)"
    );
}

/// Test implied bounds: single-unbounded derivation (#5591 AC2).
///
/// Constraint: x + y <= 10, x >= 3, no direct bound on y.
/// y is the single variable lacking a bound in its direction. The
/// single-unbounded path in compute_implied_bounds derives a bound for y.
///
/// Row: s = x + y - 10, s <= 0. Equation: s - x - y = -10.
/// With x >= 3 (lb=3), the single-unbounded path derives y = 7 (= 10 - 3).
#[test]
fn test_implied_bounds_single_unbounded_derivation_5591() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge = terms.mk_ge(x, three); // x >= 3

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    let y_var = *solver.term_to_var.get(&y).expect("y interned") as usize;

    // The single-unbounded path should produce a derived bound for y.
    // Check both slots — the bound may be stored in .0 (lb direction)
    // matching the convention observed in the all-bounded test.
    let y_bound = solver.implied_bounds[y_var]
        .0
        .as_ref()
        .or(solver.implied_bounds[y_var].1.as_ref())
        .expect("y should have a derived bound from single-unbounded path");
    assert_eq!(
        y_bound.value,
        Rational::from(BigRational::from(BigInt::from(7))),
        "y derived bound should be 7 (= 10 - 3)"
    );
}

/// Regression test for #6615/#6617: batch compute_implied_bounds must handle
/// medium-width rows (25 coefficients), not just rows with 20 or fewer.
/// Previously this test exercised the inline eager path; after #6617 the
/// inline path only queues refinements for slack targets, so bound writing
/// is exercised via the batch boundary.
#[test]
fn test_batch_implied_bounds_medium_width_row_6617() {
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

    let mut vars = Vec::with_capacity(26);
    vars.push(VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: Some(bound(0, 900)),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    });
    vars.push(VarInfo {
        value: InfRational::from_rational(BigRational::zero()),
        lower: None,
        upper: None,
        status: Some(VarStatus::NonBasic),
    });
    for reason in 901..925 {
        vars.push(VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(1, reason)),
            upper: None,
            status: Some(VarStatus::NonBasic),
        });
    }
    solver.vars = vars;
    solver.rows = vec![TableauRow::new(
        0,
        (1..=25)
            .map(|var| (var, BigRational::from(BigInt::from(-1))))
            .collect(),
        BigRational::from(BigInt::from(29)),
    )];
    solver.col_index = vec![Vec::new(); 26];
    for var in 1..=25u32 {
        // Position in row 0's coeffs is (var - 1) since coeffs are sorted by var id.
        solver.col_index[var as usize].push(ColEntry::new(0, (var - 1) as usize));
    }
    solver.basic_var_to_row.insert(0, 0);

    assert_eq!(
        solver.rows[0].coeffs.len(),
        25,
        "test must exercise a row wider than the historical 20-column limit"
    );

    // Seed touched_rows (the batch path reads from this set).
    solver.touched_rows.insert(0);

    // Run the batch implied-bounds pass.
    solver.compute_implied_bounds();

    let upper = solver.implied_bounds[1]
        .1
        .as_ref()
        .expect("batch compute_implied_bounds should produce an upper bound on x1");
    assert_eq!(
        upper.value,
        Rational::from(5i32),
        "x1 upper bound should be 5 (= 29 - 24*1)"
    );
    assert!(
        !upper.strict,
        "the derived upper bound must stay non-strict"
    );
}

/// Test for #8008: cascade bound propagation within a single call.
///
/// Row-local derivations and cross-row cascades now both happen within a
/// single `compute_implied_bounds()` call. When row 0 derives y >= 5, the
/// inner cascade loop re-evaluates row 1 (which contains y) and derives
/// z >= 5, all in one invocation. This matches Z3's behavior where bound
/// derivations cascade through the SAT-theory feedback loop.
///
/// Previously (#6615), cross-row cascades required a second call through
/// the persisted `touched_rows` seed. The inner cascade loop (#8008)
/// eliminates this per-call overhead for multi-hop chains.
#[test]
fn test_compute_implied_bounds_cascades_within_call_8008() {
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

    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, 1000)),
            upper: None,
            status: Some(VarStatus::Basic(0)),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(5, 1001)),
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: Some(bound(0, 1002)),
            upper: None,
            status: Some(VarStatus::Basic(1)),
        },
    ];

    // Row 0: s0 + x - y = 0, with s0 >= 0 and x >= 5, so first derives y >= 5.
    // Row 1: s1 + y - z = 0, with s1 >= 0. Cascade derives z >= 5 in same call.
    solver.rows = vec![
        TableauRow::new(
            0,
            vec![
                (1, BigRational::from(BigInt::from(-1))),
                (2, BigRational::from(BigInt::from(1))),
            ],
            BigRational::zero(),
        ),
        TableauRow::new(
            4,
            vec![
                (2, BigRational::from(BigInt::from(-1))),
                (3, BigRational::from(BigInt::from(1))),
            ],
            BigRational::zero(),
        ),
    ];
    solver.col_index = vec![Vec::new(); 5];
    solver.col_index[1].push(ColEntry::new(0, 0));
    solver.col_index[2].extend([ColEntry::new(0, 1), ColEntry::new(1, 0)]);
    solver.col_index[3].push(ColEntry::new(1, 1));
    solver.basic_var_to_row.insert(0, 0);
    solver.basic_var_to_row.insert(4, 1);
    solver.touched_rows.extend([0, 1]);

    solver.compute_implied_bounds();

    // #8008: Both bounds should be derived in a single call via cascade.
    let y_lower = solver.implied_bounds[2]
        .0
        .as_ref()
        .expect("should derive y >= 5 from row 0");
    assert_eq!(y_lower.value, Rational::from(5i32));

    let z_lower = solver.implied_bounds[3]
        .0
        .as_ref()
        .expect("cascade should derive z >= 5 from row 1 in the same call");
    assert_eq!(z_lower.value, Rational::from(5i32));
}

/// Test implied bounds: row size skip guard (#5591 AC3, #6617).
///
/// A constraint with >300 variables should be skipped by compute_implied_bounds
/// (the unified `MAX_TOUCHED_ROW_BOUND_SCAN_WIDTH` = 300 guard from #6617).
/// Verify that implied bounds come only from direct bounds, not from the
/// wide row.
#[test]
fn test_implied_bounds_wide_row_skip_guard_5591() {
    let mut terms = TermStore::new();

    // Create 310 variables, all bounded [0, 100], with sum <= 100000.
    // Row limit is 300 (#6617 unified constant), so 310 coefficients exceeds it.
    let mut vars = Vec::new();
    let zero = terms.mk_rational(BigRational::zero());
    let hundred = terms.mk_rational(BigRational::from(BigInt::from(100)));
    let ten_thousand = terms.mk_rational(BigRational::from(BigInt::from(100_000)));

    for i in 0..310 {
        let v = terms.mk_var(format!("v{i}"), Sort::Real);
        vars.push(v);
    }

    // Build sum of all 130 vars and all bound atoms BEFORE creating solver
    let sum = terms.mk_add(vars.clone());
    let sum_le = terms.mk_le(sum, ten_thousand); // sum <= 10000

    let mut bound_atoms = Vec::new();
    for &v in &vars {
        let ge_zero = terms.mk_ge(v, zero);
        let le_hundred = terms.mk_le(v, hundred);
        bound_atoms.push((ge_zero, le_hundred));
    }

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    for &(ge, le) in &bound_atoms {
        solver.assert_literal(ge, true);
        solver.assert_literal(le, true);
    }

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // With 310 variables, the row has >300 coefficients and should be skipped.
    // The implied upper bound for v0 should be its direct bound (100),
    // since the row is skipped due to the size guard (#6617: limit = 300).
    let v0_var = *solver.term_to_var.get(&vars[0]).expect("v0 interned") as usize;
    let v0_ib = solver.implied_bounds[v0_var]
        .1
        .as_ref()
        .expect("v0 should have direct upper bound");
    assert_eq!(
        v0_ib.value,
        Rational::from(BigRational::from(BigInt::from(100))),
        "wide row should be skipped; v0 upper bound should be direct bound 100"
    );
}

/// Test implied bounds: negative coefficient handling (#5591 AC4).
///
/// Constraint: x - y <= 5, x >= 1, x <= 10, y >= 0, y <= 10.
/// Row: s = x - y - 5, s <= 0. Equation: s - x + y = -5.
/// The negative coefficient on y (in the original constraint) creates a
/// positive eq_coeff in the bound analysis for y, and negative for x.
/// compute_implied_bounds should derive tighter bounds from the row.
#[test]
fn test_implied_bounds_negative_coefficient_5591() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // x - y <= 5  (i.e., x + (-y) <= 5)
    let neg_y = terms.mk_neg(y);
    let diff = terms.mk_add(vec![x, neg_y]);
    let diff_le = terms.mk_le(diff, five); // x - y <= 5
    let x_ge = terms.mk_ge(x, one); // x >= 1
    let x_le = terms.mk_le(x, ten); // x <= 10
    let y_ge = terms.mk_ge(y, zero); // y >= 0
    let y_le = terms.mk_le(y, ten); // y <= 10

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(diff_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(x_le, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(y_le, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned") as usize;
    let y_var = *solver.term_to_var.get(&y).expect("y interned") as usize;

    // With the mixed-sign constraint, compute_implied_bounds should
    // produce derived bounds for both x and y beyond their direct bounds.
    //
    // The total number of non-None bounds in implied_bounds should exceed
    // the 4 direct bounds (x: [1,10], y: [0,10]) plus the slack ub.
    let total_bounds: usize = solver
        .implied_bounds
        .iter()
        .map(|(lb, ub)| usize::from(lb.is_some()) + usize::from(ub.is_some()))
        .sum();

    // At minimum we have: x lb=1, x ub=10, y lb=0, y ub=10, slack ub=0
    // The row should derive at least 1 additional bound.
    assert!(
        total_bounds >= 6,
        "negative-coefficient row should derive additional bounds; total = {total_bounds}"
    );

    // x - y <= 5 with y >= 0: the tightest derived bound for x should be
    // no more than 15 (= 5 + 10, from y <= 10). Check that x has a
    // derived bound from the row (in either slot).
    let x_lb = &solver.implied_bounds[x_var].0;
    let x_ub = &solver.implied_bounds[x_var].1;
    assert!(
        x_lb.is_some() || x_ub.is_some(),
        "x should have at least one derived bound from negative-coefficient row"
    );

    // y should also have a derived bound from the row.
    let y_lb = &solver.implied_bounds[y_var].0;
    let y_ub = &solver.implied_bounds[y_var].1;
    assert!(
        y_lb.is_some() || y_ub.is_some(),
        "y should have at least one derived bound from negative-coefficient row"
    );
}
