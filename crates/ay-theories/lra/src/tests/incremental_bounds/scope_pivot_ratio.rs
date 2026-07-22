// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #3682: assertions from a popped scope must not leak.
///
/// Scenario: push, assert x >= 5, pop, then assert x <= 3. If x >= 5 leaks
/// from the popped scope, x <= 3 AND x >= 5 would be UNSAT. Correct behavior:
/// x >= 5 is removed by pop, so x <= 3 alone is SAT.
#[test]
fn test_lra_asserted_scoped_on_pop_3682() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let ge_five = terms.mk_ge(x, five); // x >= 5
    let le_three = terms.mk_le(x, three); // x <= 3

    let mut solver = LraSolver::new(&terms);

    // Push scope, assert x >= 5 within the scope
    solver.push();
    solver.assert_literal(ge_five, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Pop — x >= 5 must be removed from asserted
    solver.pop();

    // Assert x <= 3 at base scope — should be SAT (x >= 5 was popped)
    solver.assert_literal(le_three, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "After pop, x >= 5 should not leak. x <= 3 alone is SAT, got {result:?}"
    );
}

/// Regression test for #3682: pre-push assertions must survive pop.
///
/// Asserts x <= 10 and x >= 5 at base scope, then pushes, adds x < 3
/// (creating a conflict), then pops. After pop, x <= 10 and x >= 5 should
/// still be active and check() should return SAT without calling reset().
#[test]
fn test_lra_pre_push_assertions_survive_pop_3682() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let le_ten = terms.mk_le(x, ten); // x <= 10
    let ge_five = terms.mk_ge(x, five); // x >= 5
    let lt_three = terms.mk_lt(x, three); // x < 3

    let mut solver = LraSolver::new(&terms);

    // Assert at base scope
    solver.assert_literal(le_ten, true);
    solver.assert_literal(ge_five, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push and add conflicting constraint
    solver.push();
    solver.assert_literal(lt_three, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x >= 5 AND x < 3 should be UNSAT, got {result:?}"
    );

    // Pop — base assertions survive, scoped assertion removed
    solver.pop();

    // check() should return SAT (x in [5, 10], no reset needed)
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Pre-push assertions should survive pop. x in [5,10] is SAT, got {result:?}"
    );
}

/// Regression test for #4842: adding a multi-term constraint after a pivot
/// must substitute basic variables in the new row's coefficients. Without the
/// substitution, the row would reference a basic variable, violating the
/// tableau invariant that row coefficients are non-basic.
#[test]
fn test_new_row_substitutes_basic_variables_after_pivot() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let twenty = terms.mk_rational(BigRational::from(BigInt::from(20)));

    // Create all terms before the solver (LraSolver borrows terms immutably).
    let x_plus_y = terms.mk_add(vec![x, y]);
    let le_xy_10 = terms.mk_le(x_plus_y, ten);
    let ge_x_0 = terms.mk_ge(x, zero);
    let ge_y_0 = terms.mk_ge(y, zero);
    let x_plus_y_plus_z = terms.mk_add(vec![x, y, z]);
    let le_xyz_20 = terms.mk_le(x_plus_y_plus_z, twenty);
    let ge_z_0 = terms.mk_ge(z, zero);

    let mut solver = LraSolver::new(&terms);

    // Phase 1: Assert x + y <= 10, x >= 0, y >= 0.
    solver.assert_literal(le_xy_10, true);
    solver.assert_literal(ge_x_0, true);
    solver.assert_literal(ge_y_0, true);

    // Run simplex — may pivot, making some vars basic.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x + y <= 10, x >= 0, y >= 0 should be SAT, got {result:?}"
    );

    // Phase 2: Assert x + y + z <= 20 after the simplex has run. If x or y
    // became basic during the previous check(), the new row's coefficients
    // must substitute them. The debug_assert_no_basic_in_coeffs assertion
    // (in dual_simplex) will catch violations.
    solver.assert_literal(le_xyz_20, true);
    solver.assert_literal(ge_z_0, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x + y + z <= 20 (all >= 0) should be SAT, got {result:?}"
    );
}

/// Regression test for #5946: incremental assert after pivot must substitute basic
/// variables. The ORIGINAL test (x+y<=5, x>=1, y>=1) was a false regression test:
/// those constraints are too loose to force any pivots (non-basic repair satisfies
/// all bounds immediately), so the substitution code at lib.rs:680-700 was never
/// exercised.
///
/// This REPLACEMENT test uses a lower-bound constraint (x + y >= 2) that forces
/// the slack to violate its upper bound at initial values (x=0, y=0), triggering
/// a dual-simplex pivot that makes y basic. Then an incremental constraint
/// (2x + y <= 6) is added referencing the now-basic y, requiring substitution.
/// In debug mode, debug_assert_tableau_consistency's cross-row check catches
/// any basic variable left unsubstituted in a coefficient list.
#[test]
fn test_incremental_assert_substitutes_basic_vars_cross_row_5946() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));

    // Phase 1: x + y >= 2, x + y <= 5, x <= 1
    //
    // The >= constraint: x + y >= 2 is encoded as 2 - x - y <= 0 (slack s1).
    // At non-basic repair: x=0, y=0 → s1 = 2-0-0 = 2 > 0. Violation!
    // Dual simplex pivots s1 out, bringing x or y into the basis.
    // After pivot: y becomes basic (expressed via s1 and x). SAT at x=0, y=2.
    let x_plus_y = terms.mk_add(vec![x, y]);
    let ge_2 = terms.mk_ge(x_plus_y, two);
    let le_5 = terms.mk_le(x_plus_y, five);
    let le_x_1 = terms.mk_le(x, one);

    // Phase 2: 2x + y <= 6 (references y, which should now be basic).
    // The new row creation at lib.rs:680-700 must substitute the basic
    // variable y with its row expression to maintain the cross-row invariant.
    let two_x = terms.mk_mul(vec![two, x]);
    let two_x_plus_y = terms.mk_add(vec![two_x, y]);
    let le_6 = terms.mk_le(two_x_plus_y, six);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_2, true);
    solver.assert_literal(le_5, true);
    solver.assert_literal(le_x_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x+y>=2, x+y<=5, x<=1 should be SAT (e.g. x=0, y=2), got {result:?}"
    );

    // Phase 2: assert 2x + y <= 6 incrementally. If y became basic during
    // phase 1 pivots, this new row's creation must substitute y with its
    // row expression. Without the substitution, debug_assert_tableau_consistency
    // fires in debug mode (cross-row invariant violation).
    solver.assert_literal(le_6, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x+y>=2, x+y<=5, x<=1, 2x+y<=6 should be SAT (e.g. x=0, y=2), got {result:?}"
    );
}

/// Tests for proportional_coefficient_ratio edge cases (#4891).
/// After variable substitution, disequality expressions can become scalar multiples
/// of their tableau rows (e.g., 4294967296*(A-B) vs (A-B)). The ratio function
/// must handle positive, negative, and fractional k values.
#[test]
fn test_proportional_coefficient_ratio_positive_integer() {
    // 3*(A - B) vs (A - B)  →  k = 3
    let expr = LinearExpr {
        coeffs: vec![(1, Rational::from(3_i64)), (2, Rational::from(-3_i64))],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (2, Rational::from(-1_i64))],
        constant: Rational::zero(),
    };
    let k = expr.proportional_coefficient_ratio(&row);
    assert_eq!(k, Some(BigRational::from(BigInt::from(3))));
}

#[test]
fn test_proportional_coefficient_ratio_negative_k() {
    // -(A - B) vs (A - B)  →  k = -1
    let expr = LinearExpr {
        coeffs: vec![(1, Rational::from(-1_i64)), (2, Rational::from(1_i64))],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (2, Rational::from(-1_i64))],
        constant: Rational::zero(),
    };
    let k = expr.proportional_coefficient_ratio(&row);
    assert_eq!(k, Some(BigRational::from(BigInt::from(-1))));
}

#[test]
fn test_proportional_coefficient_ratio_fractional_k() {
    // (1/3)*(A + 2B) vs (A + 2B)  →  k = 1/3
    let third = BigRational::new(BigInt::from(1), BigInt::from(3));
    let two_thirds = BigRational::new(BigInt::from(2), BigInt::from(3));
    let expr = LinearExpr {
        coeffs: vec![
            (1, Rational::from_big(third.clone())),
            (2, Rational::from_big(two_thirds)),
        ],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (2, Rational::from(2_i64))],
        constant: Rational::zero(),
    };
    let k = expr.proportional_coefficient_ratio(&row);
    assert_eq!(k, Some(third));
}

#[test]
fn test_proportional_coefficient_ratio_not_proportional() {
    // (2A + 3B) vs (A + B) — different ratios per variable → None
    let expr = LinearExpr {
        coeffs: vec![(1, Rational::from(2_i64)), (2, Rational::from(3_i64))],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (2, Rational::from(1_i64))],
        constant: Rational::zero(),
    };
    assert!(expr.proportional_coefficient_ratio(&row).is_none());
}

#[test]
fn test_proportional_coefficient_ratio_different_variables() {
    // (A + B) vs (A + C) — different variables → None
    let expr = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (2, Rational::from(1_i64))],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (3, Rational::from(1_i64))],
        constant: Rational::zero(),
    };
    assert!(expr.proportional_coefficient_ratio(&row).is_none());
}

#[test]
fn test_proportional_coefficient_ratio_empty() {
    // Empty expressions → None
    let expr = LinearExpr {
        coeffs: vec![],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![],
        constant: Rational::zero(),
    };
    assert!(expr.proportional_coefficient_ratio(&row).is_none());
}

#[test]
fn test_proportional_coefficient_ratio_zero_denominator() {
    // (2A) vs (0A) — zero coefficient in denominator → None
    let expr = LinearExpr {
        coeffs: vec![(1, Rational::from(2_i64))],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::zero())],
        constant: Rational::zero(),
    };
    assert!(expr.proportional_coefficient_ratio(&row).is_none());
}

#[test]
fn test_proportional_coefficient_ratio_large_k() {
    // 4294967296*(A - B) vs (A - B)  →  k = 2^32
    // This is the actual regression case from convert-jpg2gif
    let big = BigRational::from(BigInt::from(4294967296_u64));
    let neg_big = -big.clone();
    let expr = LinearExpr {
        coeffs: vec![
            (1, Rational::from_big(big.clone())),
            (2, Rational::from_big(neg_big)),
        ],
        constant: Rational::zero(),
    };
    let row = LinearExpr {
        coeffs: vec![(1, Rational::from(1_i64)), (2, Rational::from(-1_i64))],
        constant: Rational::zero(),
    };
    let k = expr.proportional_coefficient_ratio(&row);
    assert_eq!(k, Some(big));
}
// ── propagate_equalities coverage tests (#4891, proof_coverage) ─────────────
