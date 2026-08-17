// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `algebraic::tests` to preserve test FQNs.

/// The whole point: `(= (* x x) 2.0)` must be CONFIRMED for `x = sqrt(2)`.
/// This is the constraint `nra_algebraic_sqrt2_model_is_exact_and_validated`
/// needs the gate to check.
#[test]
fn sqrt2_squared_is_exactly_two() {
    let x = sqrt2();
    let x_squared = x.mul(&x).expect("same extension");
    assert_eq!(x_squared.as_rational(), Some(int(2)));
    assert!(x_squared.equals_rational(&int(2)));
}

/// And it must NOT confirm a near miss. `2` is the only rational it equals.
#[test]
fn sqrt2_squared_is_not_any_other_rational() {
    let x = sqrt2();
    let x_squared = x.mul(&x).expect("same extension");
    for wrong in [
        int(0),
        int(1),
        int(3),
        int(-2),
        rat(199, 100),
        rat(201, 100),
    ] {
        assert!(
            !x_squared.equals_rational(&wrong),
            "sqrt(2)^2 must not equal {wrong}"
        );
    }
}

/// `sqrt(2)` itself is irrational — it must never reduce to a rational, which
/// is precisely what `Real(BigRational)` could not express.
#[test]
fn sqrt2_itself_is_not_rational() {
    assert_eq!(sqrt2().as_rational(), None);
}

#[test]
fn cbrt2_cubed_is_exactly_two() {
    let x = cbrt2();
    let cubed = x.mul(&x).and_then(|s| s.mul(&x)).expect("same extension");
    assert_eq!(cubed.as_rational(), Some(int(2)));
}

/// `cbrt(2)^2` stays irrational: reduction must not over-collapse.
#[test]
fn cbrt2_squared_stays_irrational() {
    let x = cbrt2();
    assert_eq!(x.mul(&x).expect("same extension").as_rational(), None);
}

// ---------------------------------------------------------------------------
// Arithmetic laws, checked against closed forms
// ---------------------------------------------------------------------------

/// `(sqrt(2) + sqrt(2))^2 = 4 * 2 = 8`.
#[test]
fn doubling_then_squaring_matches_the_closed_form() {
    let x = sqrt2();
    let doubled = x.add(&x).expect("same extension");
    let squared = doubled.mul(&doubled).expect("same extension");
    assert_eq!(squared.as_rational(), Some(int(8)));
}

/// `(sqrt(2) + 1) * (sqrt(2) - 1) = 2 - 1 = 1`.
#[test]
fn conjugate_product_is_rational() {
    let x = sqrt2();
    let one = x.with_rational(BigRational::one());
    let plus = x.add(&one).expect("same extension");
    let minus = x.add(&one.neg()).expect("same extension");
    assert_eq!(
        plus.mul(&minus).expect("same extension").as_rational(),
        Some(int(1))
    );
}

/// `x + (-x) = 0`.
#[test]
fn negation_cancels() {
    let x = sqrt2();
    let sum = x.add(&x.neg()).expect("same extension");
    assert_eq!(sum.as_rational(), Some(BigRational::zero()));
}

/// Rationals carried in the extension behave as rationals.
#[test]
fn rationals_round_trip_through_the_extension() {
    let x = sqrt2();
    for q in [int(0), int(7), rat(-3, 4), rat(22, 7)] {
        assert_eq!(x.with_rational(q.clone()).as_rational(), Some(q));
    }
}

/// Multiplication is commutative and associative over the extension.
#[test]
fn multiplication_is_commutative_and_associative() {
    let x = cbrt2();
    let a = x.add(&x.with_rational(int(1))).expect("ok"); // cbrt(2) + 1
    let b = x.mul(&x).expect("ok"); // cbrt(2)^2

    let ab = a.mul(&b).expect("ok");
    let ba = b.mul(&a).expect("ok");
    assert_eq!(ab.equals(&ba), Some(true));

    let left = ab.mul(&x).expect("ok");
    let right = a.mul(&b.mul(&x).expect("ok")).expect("ok");
    assert_eq!(left.equals(&right), Some(true));
}

// ---------------------------------------------------------------------------
// Rejections: each one, accepted, would let the gate confirm a wrong model
// ---------------------------------------------------------------------------

/// A constant polynomial defines no algebraic number.
#[test]
fn rejects_a_degenerate_minimal_polynomial() {
    assert_eq!(
        Algebraic::root_of(integer_poly(&[5]), int(0), int(1)).unwrap_err(),
        AlgebraicError::DegenerateMinimalPolynomial
    );
    assert_eq!(
        Algebraic::root_of(Vec::new(), int(0), int(1)).unwrap_err(),
        AlgebraicError::DegenerateMinimalPolynomial
    );
}

#[test]
fn rejects_an_empty_or_inverted_interval() {
    let p = integer_poly(&[-2, 0, 1]);
    assert_eq!(
        Algebraic::root_of(p.clone(), int(2), int(1)).unwrap_err(),
        AlgebraicError::EmptyInterval
    );
    assert_eq!(
        Algebraic::root_of(p, int(1), int(1)).unwrap_err(),
        AlgebraicError::EmptyInterval
    );
}

/// THE structural rejection: an interval with no sign change is not known to
/// bracket a root, so the root object is refused rather than assumed.
#[test]
fn rejects_an_interval_that_brackets_no_root() {
    // x^2 - 2 is negative across (0, 1) — no root there.
    assert_eq!(
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(0), int(1)).unwrap_err(),
        AlgebraicError::NoSignChange
    );
    // ... and positive across (2, 3).
    assert_eq!(
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(2), int(3)).unwrap_err(),
        AlgebraicError::NoSignChange
    );
}

/// Combining values over DIFFERENT extensions needs resultants. Refused, not
/// approximated — a wrong answer here is a wrong model confirmed.
#[test]
fn refuses_to_combine_different_extensions() {
    let a = sqrt2();
    let b = cbrt2();
    assert_eq!(a.mul(&b).unwrap_err(), AlgebraicError::DifferentExtension);
    assert_eq!(a.add(&b).unwrap_err(), AlgebraicError::DifferentExtension);
    assert_eq!(a.equals(&b), None, "cross-extension equality is undecided");
}

/// Same polynomial, different isolating interval, is a different value
/// (`+sqrt(2)` vs `-sqrt(2)`), so they must not be silently combined.
#[test]
fn treats_distinct_roots_of_one_polynomial_as_distinct_extensions() {
    let positive = sqrt2();
    let negative =
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(-2), int(-1)).expect("negative root");
    assert_eq!(positive.equals(&negative), None);
    assert_eq!(
        positive.add(&negative).unwrap_err(),
        AlgebraicError::DifferentExtension
    );
}

/// A root exactly at an endpoint is still bracketed.
#[test]
fn accepts_a_root_sitting_on_an_endpoint() {
    // x^2 - 4 has a root at exactly 2.
    assert!(Algebraic::root_of(integer_poly(&[-4, 0, 1]), int(2), int(3)).is_ok());
}

/// Both roots of the same polynomial square to the same rational — the reason
/// equality conclusions do NOT depend on resolving which root was meant.
#[test]
fn equality_conclusions_hold_for_either_root() {
    let positive = sqrt2();
    let negative =
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(-2), int(-1)).expect("negative root");
    for x in [positive, negative] {
        assert_eq!(
            x.mul(&x).expect("same extension").as_rational(),
            Some(int(2))
        );
    }
}

/// Reduction must handle a non-monic minimal polynomial: `2x^2 - 4` also
/// defines sqrt(2), and the leading coefficient must be divided out exactly.
#[test]
fn handles_a_non_monic_minimal_polynomial() {
    let x = Algebraic::root_of(integer_poly(&[-4, 0, 2]), int(1), int(2)).expect("2x^2-4");
    assert_eq!(
        x.mul(&x).expect("same extension").as_rational(),
        Some(int(2))
    );
}

/// Rational coefficients, not just integers: `x^2 - 1/4` has root `1/2`, which
/// IS rational, so squaring gives exactly `1/4`.
#[test]
fn handles_rational_coefficients() {
    let x = Algebraic::root_of(
        vec![-rat(1, 4), BigRational::zero(), BigRational::one()],
        int(0),
        int(1),
    )
    .expect("x^2 - 1/4");
    assert_eq!(
        x.mul(&x).expect("same extension").as_rational(),
        Some(rat(1, 4))
    );
}
