// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// A tableau coefficient of `i64::MIN` has no `Small` reciprocal: the sign
/// fix-up of `1 / (i64::MIN / d)` needs `-i64::MIN`. The update amount used
/// `wrapping_neg`, which maps `i64::MIN` to itself, and built the reciprocal
/// `-d / i64::MIN` — a `Small` with a NEGATIVE denominator, breaking the
/// `d > 0` invariant every cross-multiplied comparison relies on (debug
/// builds panic `Rational::Small invariant violated: -1/-9223372036854775808`;
/// release builds compute with it). Measured through deductive-checks's exact
/// Euclidean division lemmas over 64-bit shifted values.
#[test]
fn test_update_amount_through_i64_min_coefficient_is_exact() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    // Basic x0 = i64::MIN * x1 must rise to its lower bound 1.
    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(1, 10, true, 1, 1)), None),
        nonbasic_var(None, None),
    ];
    solver.rows = vec![TableauRow::new(0, vec![(1, int(i64::MIN))], int(0))];
    let coeff = solver.rows[0].coeff_ref(1).expect("row carries x1").clone();
    let amount = solver.compute_update_amount_with_coeff(0, 1, BoundType::Lower, &coeff);
    // x1 = 1 / i64::MIN = -1 / 2^63, exactly.
    let expected =
        InfRational::from_rational(BigRational::new(BigInt::from(-1), BigInt::from(1u64 << 63)));
    assert!(
        amount == expected,
        "the update amount through an i64::MIN coefficient must be -1/2^63"
    );

    // Anti-vacuity: an ordinary negative coefficient still takes the i64 fast
    // path to the exact reciprocal.
    solver.rows = vec![TableauRow::new(0, vec![(1, int(-4))], int(0))];
    let coeff = solver.rows[0].coeff_ref(1).expect("row carries x1").clone();
    let amount = solver.compute_update_amount_with_coeff(0, 1, BoundType::Lower, &coeff);
    assert!(amount == InfRational::from_rational(frac(-1, 4)));
}

#[test]
fn test_update_amount_exact_reciprocal_and_fast_path_clamp_lower_bound() {
    for coefficient in [frac(i64::MIN, i64::MAX), int(-1)] {
        let expected_unbounded = InfRational::from_rational(int(2) / coefficient.clone());
        let terms = TermStore::new();
        let mut solver = LraSolver::new(&terms);
        solver.vars = vec![
            basic_var(0, Some(bound_with_reason(2, 10, true, 1, 1)), None),
            nonbasic_var(Some(bound_with_reason(-1, 11, true, 1, 1)), None),
        ];
        solver.rows = vec![TableauRow::new(0, vec![(1, coefficient)], int(0))];
        // x1 can decrease from 0 to -1, so this is an eligible pivot, not an
        // at-bound variable that the real caller would already have rejected.
        assert_eq!(
            solver.find_beneficial_entering(0, BoundType::Lower),
            Some((1, -1, 0))
        );
        let coeff = solver.rows[0].coeff_ref(1).expect("row carries x1").clone();
        assert!(matches!(&coeff, Rational::Small(_, _)));
        let amount = solver.compute_update_amount_with_coeff(0, 1, BoundType::Lower, &coeff);
        assert!(
            amount == InfRational::from_rational(int(-1)),
            "both reciprocal paths must stop at the nonbasic lower bound"
        );

        // Removing only the bound restores the exact target below -1; neither
        // a constant-zero result nor unconditional clamping can satisfy this.
        solver.vars[1].lower = None;
        let unbounded = solver.compute_update_amount_with_coeff(0, 1, BoundType::Lower, &coeff);
        assert!(unbounded == expected_unbounded);
        assert!(unbounded < amount);
    }
}

#[test]
fn test_update_amount_exact_reciprocal_and_fast_path_clamp_upper_bound() {
    for coefficient in [frac(i64::MIN, i64::MAX), int(-1)] {
        let expected_unbounded = InfRational::from_rational(int(-2) / coefficient.clone());
        let terms = TermStore::new();
        let mut solver = LraSolver::new(&terms);
        solver.vars = vec![
            basic_var(0, None, Some(bound_with_reason(-2, 10, false, 1, 1))),
            nonbasic_var(None, Some(bound_with_reason(1, 11, false, 1, 1))),
        ];
        solver.rows = vec![TableauRow::new(0, vec![(1, coefficient)], int(0))];
        // The symmetric pivot can increase x1 from 0 to 1.
        assert_eq!(
            solver.find_beneficial_entering(0, BoundType::Upper),
            Some((1, 1, 0))
        );
        let coeff = solver.rows[0].coeff_ref(1).expect("row carries x1").clone();
        assert!(matches!(&coeff, Rational::Small(_, _)));
        let amount = solver.compute_update_amount_with_coeff(0, 1, BoundType::Upper, &coeff);
        assert!(
            amount == InfRational::from_rational(int(1)),
            "both reciprocal paths must stop at the nonbasic upper bound"
        );

        solver.vars[1].upper = None;
        let unbounded = solver.compute_update_amount_with_coeff(0, 1, BoundType::Upper, &coeff);
        assert!(unbounded == expected_unbounded);
        assert!(unbounded > amount);
    }
}
