// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for exact real-algebraic arithmetic.
//!
//! The acceptance cases matter less than the rejections: this module exists to
//! let the independent gate confirm a witness, so a bug here confirms a WRONG
//! model. Every operation is checked against a value known in closed form.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::{integer_poly, Algebraic, AlgebraicError};

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn int(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

/// `sqrt(2)`: the root of `x^2 - 2` in `(1, 2)`.
fn sqrt2() -> Algebraic {
    Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(1), int(2)).expect("sqrt(2) is well-formed")
}

/// `cbrt(2)`: the root of `x^3 - 2` in `(1, 2)`.
fn cbrt2() -> Algebraic {
    Algebraic::root_of(integer_poly(&[-2, 0, 0, 1]), int(1), int(2)).expect("cbrt(2)")
}

// ---------------------------------------------------------------------------
// The case this module was built for
// ---------------------------------------------------------------------------

include!("algebraic_tests/extension_arithmetic.rs");

// ---------------------------------------------------------------------------
// Integration with `value_eq` — the gate's actual comparison path
// ---------------------------------------------------------------------------

use crate::{value_eq, ModelValue};

fn av(a: Algebraic) -> ModelValue {
    ModelValue::Algebraic(Box::new(a))
}

/// The end-to-end shape the NRA gate needs: `sqrt(2)^2` compares EQUAL to the
/// rational 2 through the same `value_eq` the evaluator calls.
#[test]
fn value_eq_confirms_sqrt2_squared_against_the_rational_two() {
    let x = sqrt2();
    let squared = av(x.mul(&x).expect("same extension"));
    assert_eq!(value_eq(&squared, &ModelValue::Real(int(2))), Ok(true));
    assert_eq!(value_eq(&ModelValue::Real(int(2)), &squared), Ok(true));
    assert_eq!(
        value_eq(&squared, &ModelValue::Int(BigInt::from(2))),
        Ok(true)
    );
}

/// ... and REFUTES a wrong rational, rather than declining. A decline would be
/// merely incomplete; returning `true` here would be unsound.
#[test]
fn value_eq_refutes_sqrt2_squared_against_a_wrong_rational() {
    let x = sqrt2();
    let squared = av(x.mul(&x).expect("same extension"));
    assert_eq!(value_eq(&squared, &ModelValue::Real(int(3))), Ok(false));
    assert_eq!(
        value_eq(&squared, &ModelValue::Int(BigInt::from(0))),
        Ok(false)
    );
}

/// An irrational is never equal to a rational.
#[test]
fn value_eq_says_sqrt2_is_not_any_rational() {
    let x = av(sqrt2());
    for q in [int(1), int(2), rat(141, 100), rat(1414, 1000)] {
        assert_eq!(value_eq(&x, &ModelValue::Real(q)), Ok(false));
    }
}

/// Same extension, same value.
#[test]
fn value_eq_identifies_equal_algebraic_values() {
    assert_eq!(value_eq(&av(sqrt2()), &av(sqrt2())), Ok(true));
}

/// Cross-extension equality is UNDECIDED, and must surface as an error the
/// gate fails closed on -- never as `false`, which would be a refutation the
/// checker has not earned.
#[test]
fn value_eq_declines_cross_extension_comparison() {
    assert!(value_eq(&av(sqrt2()), &av(cbrt2())).is_err());
}

/// An algebraic value is not comparable to an unrelated shape, and the
/// diagnostic names both.
#[test]
fn value_eq_reports_shapes_for_an_incomparable_pair() {
    let err = value_eq(&av(sqrt2()), &ModelValue::Bool(true))
        .expect_err("Algebraic vs Bool is incomparable");
    assert!(err.contains("Algebraic"), "{err}");
    assert!(err.contains("Bool"), "{err}");
}

// ---------------------------------------------------------------------------
// Sturm: exact root counting, isolation, and the z3 root index
// ---------------------------------------------------------------------------

/// THE parity number. z3 publishes `sqrt(2)` as
/// `(root-obj (+ (^ x 2) (- 2)) 2)` — root index 2, because `-sqrt(2)` comes
/// first in increasing order.
#[test]
fn sqrt2_is_root_index_two_matching_z3() {
    assert_eq!(sqrt2().root_index(), 2);
}

/// ... and the negative root is index 1.
#[test]
fn negative_sqrt2_is_root_index_one() {
    let negative =
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(-2), int(-1)).expect("negative root");
    assert_eq!(negative.root_index(), 1);
}

/// `x^3 - 2` has ONE real root, so `cbrt(2)` is index 1.
#[test]
fn cbrt2_is_root_index_one() {
    assert_eq!(cbrt2().root_index(), 1);
}

/// Indices over a polynomial with three real roots: `x^3 - x = x(x-1)(x+1)`
/// has roots -1, 0, 1 at indices 1, 2, 3.
#[test]
fn root_indices_are_in_increasing_order() {
    let p = integer_poly(&[0, -1, 0, 1]);
    for (lo, hi, expected) in [
        (rat(-3, 2), rat(-1, 2), 1usize),
        (rat(-1, 2), rat(1, 2), 2),
        (rat(1, 2), rat(3, 2), 3),
    ] {
        let r = Algebraic::root_of(p.clone(), lo, hi).expect("isolated root");
        assert_eq!(r.root_index(), expected);
    }
}

#[test]
fn counts_distinct_roots_in_an_interval() {
    let x =
        Algebraic::root_of(integer_poly(&[0, -1, 0, 1]), rat(-1, 2), rat(1, 2)).expect("root 0");
    assert_eq!(
        x.count_roots_in(&int(-2), &int(2)),
        3,
        "all three of -1, 0, 1"
    );
    assert_eq!(x.count_roots_in(&rat(1, 2), &int(2)), 1, "just 1");
    assert_eq!(x.count_roots_in(&int(2), &int(3)), 0, "none above 1");
}

/// THE isolation rejection. A sign change alone proves only an ODD number of
/// roots, so an interval holding three roots would pass the old check and
/// leave the value ambiguous. Sturm counts them and refuses.
#[test]
fn rejects_an_interval_holding_more_than_one_root() {
    // (-2, 2) contains all three roots of x^3 - x.
    let err = Algebraic::root_of(integer_poly(&[0, -1, 0, 1]), int(-2), int(2)).unwrap_err();
    assert_eq!(err, AlgebraicError::IntervalDoesNotIsolate { roots: 3 });
}

/// Repeated factors must not be counted twice: `(x-1)^2` has ONE distinct
/// root.
///
/// NOTE this case alone does NOT exercise the square-free reduction — its
/// Sturm chain terminates immediately and gives the right count either way.
/// `counts_distinct_roots_of_a_polynomial_with_a_repeated_factor` below is the
/// one that discriminates; verified by mutation.
#[test]
fn counts_a_repeated_root_once() {
    // (x-1)^2 = x^2 - 2x + 1
    let r = Algebraic::root_of(integer_poly(&[1, -2, 1]), rat(1, 2), rat(3, 2))
        .expect("the repeated root is still a single distinct root");
    assert_eq!(r.root_index(), 1);
}

/// THE square-free case. `(x-1)^2 (x+1) = x^3 - x^2 - x + 1` has a DOUBLE root
/// at 1 alongside a simple root at -1, so two distinct real roots. Sturm's
/// theorem counts distinct roots only after the repeated factors are divided
/// out; without that reduction this count is wrong.
#[test]
fn counts_distinct_roots_of_a_polynomial_with_a_repeated_factor() {
    let p = integer_poly(&[1, -1, -1, 1]);
    let simple = Algebraic::root_of(p.clone(), rat(-3, 2), rat(-1, 2)).expect("root at -1");
    assert_eq!(
        simple.count_roots_in(&int(-2), &int(2)),
        2,
        "distinct roots are -1 and 1, not three counted with multiplicity"
    );
    assert_eq!(simple.root_index(), 1, "-1 is the smallest root");

    let doubled = Algebraic::root_of(p, rat(1, 2), rat(3, 2)).expect("double root at 1");
    assert_eq!(doubled.root_index(), 2, "1 is the second DISTINCT root");
}

/// An even number of roots in the interval also fails isolation — and this one
/// has NO sign change, so it is exactly the case a bracket test misses.
#[test]
fn rejects_an_interval_holding_two_roots() {
    // x^2 - 1 has roots -1 and 1; p(-2) and p(2) are both positive.
    let err = Algebraic::root_of(integer_poly(&[-1, 0, 1]), int(-2), int(2)).unwrap_err();
    assert_eq!(err, AlgebraicError::IntervalDoesNotIsolate { roots: 2 });
}

/// SOUNDNESS PROBE: a NON-minimal defining polynomial.
///
/// `(x-1)(x-2) = x^2 - 3x + 2` with the root 1 isolated in `(1/2, 3/2)`. The
/// element `x` and the element `1` are DIFFERENT representations that denote
/// the SAME value there. A structural comparison of reduced representations
/// reports them unequal, and a wrong `false` is not merely incomplete: through
/// a negated equality `(not (= a b))` it lets the gate CONFIRM a wrong model.
#[test]
fn equal_values_with_different_representations_are_not_reported_unequal() {
    let alpha = Algebraic::root_of(integer_poly(&[2, -3, 1]), rat(1, 2), rat(3, 2))
        .expect("root 1 of (x-1)(x-2)");
    let one = alpha.with_rational(int(1));
    assert_ne!(
        alpha.equals(&one),
        Some(false),
        "alpha IS 1 here; reporting them unequal would license a wrong model"
    );
}

/// The same soundness hole on the rational path: over `(x-1)(x-2)` with the
/// root 1, the element `x` IS the rational 1, but its representation is not a
/// constant. Deciding by "did the representation reduce to a constant" reports
/// `false`, and through `(not (= x 1))` that confirms a wrong model.
#[test]
fn a_rational_valued_element_is_recognized_even_when_its_representation_is_not_constant() {
    let alpha = Algebraic::root_of(integer_poly(&[2, -3, 1]), rat(1, 2), rat(3, 2))
        .expect("root 1 of (x-1)(x-2)");
    assert!(
        alpha.equals_rational(&int(1)),
        "alpha IS 1 here, whatever shape its representation has"
    );
    assert!(
        !alpha.equals_rational(&int(2)),
        "the OTHER root is not this one"
    );
    assert!(!alpha.equals_rational(&int(0)));
}

/// And the same through `value_eq`, the path the gate actually calls.
#[test]
fn value_eq_recognizes_a_rational_valued_algebraic_element() {
    let alpha = Algebraic::root_of(integer_poly(&[2, -3, 1]), rat(1, 2), rat(3, 2))
        .expect("root 1 of (x-1)(x-2)");
    assert_eq!(value_eq(&av(alpha), &ModelValue::Real(int(1))), Ok(true));
}

// ---------------------------------------------------------------------------
// Ordering: sign determination by interval refinement
// ---------------------------------------------------------------------------

use core::cmp::Ordering;

/// THE case ordering exists for: the two roots of `x^2 - 2` have OPPOSITE
/// signs, so reduction alone can never separate them — only the isolating
/// interval can.
#[test]
fn the_two_roots_of_x2_minus_2_have_opposite_signs() {
    let positive = sqrt2();
    let negative =
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(-2), int(-1)).expect("negative root");
    assert_eq!(positive.sign(), Some(1));
    assert_eq!(negative.sign(), Some(-1));
}

/// A value that IS zero is settled exactly, not by refinement.
#[test]
fn a_zero_value_has_sign_zero() {
    let x = sqrt2();
    assert_eq!(x.add(&x.neg()).expect("same extension").sign(), Some(0));
    assert_eq!(x.with_rational(BigRational::zero()).sign(), Some(0));
}

/// Rationals carried in the extension keep their own signs.
#[test]
fn carried_rationals_keep_their_sign() {
    let x = sqrt2();
    assert_eq!(x.with_rational(int(5)).sign(), Some(1));
    assert_eq!(x.with_rational(rat(-1, 3)).sign(), Some(-1));
}

/// `sqrt(2) - 1 > 0` and `sqrt(2) - 2 < 0`: the classic bracketing of an
/// irrational between neighbouring rationals.
#[test]
fn sqrt2_is_bracketed_between_one_and_two() {
    let x = sqrt2();
    assert_eq!(x.compare_to_rational(&int(1)), Some(Ordering::Greater));
    assert_eq!(x.compare_to_rational(&int(2)), Some(Ordering::Less));
}

/// Tight decimal bounds: `1.414 < sqrt(2) < 1.415`. This is what forces real
/// refinement rather than a lucky first enclosure.
#[test]
fn sqrt2_is_bracketed_tightly() {
    let x = sqrt2();
    assert_eq!(
        x.compare_to_rational(&rat(1414, 1000)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        x.compare_to_rational(&rat(1415, 1000)),
        Some(Ordering::Less)
    );
    assert_eq!(
        x.compare_to_rational(&rat(14142135, 10000000)),
        Some(Ordering::Greater),
        "sqrt(2) = 1.41421356..."
    );
}

/// Comparison against the exact value reports Equal — via the exact zero test,
/// not refinement.
#[test]
fn comparison_against_the_exact_value_is_equal() {
    let x = sqrt2();
    let two = x.mul(&x).expect("same extension");
    assert_eq!(two.compare_to_rational(&int(2)), Some(Ordering::Equal));
}

/// `cbrt(2)` is between 1.259 and 1.260.
#[test]
fn cbrt2_is_bracketed_tightly() {
    let x = cbrt2();
    assert_eq!(
        x.compare_to_rational(&rat(1259, 1000)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        x.compare_to_rational(&rat(1260, 1000)),
        Some(Ordering::Less)
    );
}

/// Ordering is consistent with the arithmetic: `sqrt(2) + sqrt(2) > sqrt(2)`.
#[test]
fn ordering_agrees_with_arithmetic() {
    let x = sqrt2();
    let doubled = x.add(&x).expect("same extension");
    let difference = doubled.add(&x.neg()).expect("same extension");
    assert_eq!(
        difference.sign(),
        Some(1),
        "2*sqrt(2) - sqrt(2) = sqrt(2) > 0"
    );
}

/// A negative-root extension still orders correctly against rationals.
#[test]
fn the_negative_root_orders_below_its_rational_neighbours() {
    let negative =
        Algebraic::root_of(integer_poly(&[-2, 0, 1]), int(-2), int(-1)).expect("negative root");
    assert_eq!(
        negative.compare_to_rational(&rat(-1414, 1000)),
        Some(Ordering::Less)
    );
    assert_eq!(
        negative.compare_to_rational(&rat(-1415, 1000)),
        Some(Ordering::Greater)
    );
}

/// The interval-arithmetic case: an isolating interval that STRADDLES ZERO.
///
/// `x^3 - 2` has a single real root near 1.26, which `(-1, 2)` isolates while
/// containing zero. Squaring then requires the true extremes of the four
/// corner products: a two-corner shortcut computes `[2, 2]` for `-(x^2)` over
/// that window and reports the value POSITIVE, when it is about -1.587.
///
/// Every other ordering test here uses a one-signed interval, where two
/// corners happen to suffice — verified by mutation, which is why this case
/// exists.
#[test]
fn sign_is_correct_when_the_isolating_interval_straddles_zero() {
    let alpha = Algebraic::root_of(integer_poly(&[-2, 0, 0, 1]), int(-1), int(2))
        .expect("cbrt(2) isolated by a window containing 0");
    let squared = alpha.mul(&alpha).expect("same extension");
    assert_eq!(squared.sign(), Some(1), "cbrt(2)^2 is about 1.587");
    assert_eq!(
        squared.neg().sign(),
        Some(-1),
        "-cbrt(2)^2 is about -1.587; a two-corner enclosure calls it positive"
    );
}
