// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::mroot`].
//!
//! The interesting cases are all degenerate ones, because the non-degenerate
//! case is just "isolate the roots of a resultant". What the tests have to pin
//! down is everything the resultant CANNOT tell you:
//!
//! * conjugate roots the resultant introduces and the sieve must remove;
//! * a leading coefficient that vanishes at the sample point, dropping the
//!   degree;
//! * a resultant that vanishes identically, which is the only case with a
//!   completely different code path;
//! * repeated roots, zero and constant polynomials, unassigned coordinates.

use super::*;

use num_traits::FromPrimitive;
use std::f64::consts::SQRT_2;

// ---------------------------------------------------------------------------
// Builders
// ---------------------------------------------------------------------------

const X: MVar = 0;
const Y: MVar = 1;
const W: MVar = 2;

/// A multivariate polynomial from `(coefficient, [(var, exponent)])` terms.
fn mp(terms: &[(i64, &[(MVar, u32)])]) -> MPolyZ {
    MPolyZ::from_terms(
        terms
            .iter()
            .map(|(c, m)| (Mono::from_pairs(m.to_vec()), BigInt::from(*c)))
            .collect(),
    )
}

fn q(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn int(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// A univariate integer polynomial from low-to-high coefficients.
fn up(coeffs: &[i64]) -> UniPoly {
    UniPoly::from_coeffs(coeffs.iter().map(|c| int(*c)).collect())
}

/// The real algebraic number isolated by `(lo, hi)` on `coeffs`.
fn alg(coeffs: &[i64], lo: i64, hi: i64) -> RealAlgebraic {
    RealAlgebraic::from_isolating_interval(&up(coeffs), &int(lo), &int(hi))
        .expect("interval isolates one root")
}

/// `sqrt(2)`, as the positive root of `x^2 - 2`.
fn sqrt2() -> RealAlgebraic {
    alg(&[-2, 0, 1], 1, 2)
}

/// `sqrt(2)`, but defined by the REDUCIBLE square-free polynomial
/// `(y^2 - 2)(y - 5) = y^3 - 5y^2 - 2y + 10`.
///
/// z3's `algebraic_cell` polynomial is square-free but not necessarily
/// irreducible, and that is the only way a resultant against it can vanish
/// while the polynomial still has a non-zero leading coefficient at the point.
/// Every vanishing-resultant test below needs this.
fn sqrt2_reducible() -> RealAlgebraic {
    alg(&[10, -2, -5, 1], 1, 2)
}

fn assign(pairs: &[(MVar, Anum)]) -> Var2Anum {
    let mut a = Var2Anum::new();
    for (v, n) in pairs {
        a.set(*v, n.clone());
    }
    a
}

/// Assert a root's value to within `1e-6`, by exact comparison against two
/// rationals straddling the expected value.
fn approx(r: &Anum, expected: f64) {
    let eps = q(1, 1_000_000);
    let e = BigRational::from_f64(expected).expect("finite");
    let lo = &e - &eps;
    let hi = &e + &eps;
    assert_eq!(
        r.cmp_rational(&lo),
        Some(Ordering::Greater),
        "root {r:?} not above {expected} - 1e-6"
    );
    assert_eq!(
        r.cmp_rational(&hi),
        Some(Ordering::Less),
        "root {r:?} not below {expected} + 1e-6"
    );
}

/// Assert the roots are exactly these values (in order), to `1e-6`.
fn assert_roots(roots: &[Anum], expected: &[f64]) {
    assert_eq!(
        roots.len(),
        expected.len(),
        "expected {} roots, got {}: {roots:?}",
        expected.len(),
        roots.len()
    );
    for (r, e) in roots.iter().zip(expected) {
        approx(r, *e);
    }
}

// ---------------------------------------------------------------------------
// Representation: recursive view, substitution
// ---------------------------------------------------------------------------

#[test]
fn recursive_view_round_trips() {
    // 3x^2 y - 5x y^3 + 7y - 2
    let p = mp(&[
        (3, &[(X, 2), (Y, 1)]),
        (-5, &[(X, 1), (Y, 3)]),
        (7, &[(Y, 1)]),
        (-2, &[]),
    ]);
    assert_eq!(from_rpoly(&to_rpoly(&p, X), X), p);
    assert_eq!(from_rpoly(&to_rpoly(&p, Y), Y), p);
    assert_eq!(degree_in(&p, X), 2);
    assert_eq!(degree_in(&p, Y), 3);
    assert_eq!(degree_in(&p, W), 0);
    assert_eq!(vars_of(&p), vec![X, Y]);
}

#[test]
fn coeff_in_splits_by_the_named_variable() {
    let p = mp(&[(3, &[(X, 2), (Y, 1)]), (-5, &[(X, 1)]), (7, &[])]);
    assert_eq!(coeff_in(&p, X, 2), mp(&[(3, &[(Y, 1)])]));
    assert_eq!(coeff_in(&p, X, 1), mp(&[(-5, &[])]));
    assert_eq!(coeff_in(&p, X, 0), mp(&[(7, &[])]));
    assert_eq!(coeff_in(&p, X, 3), MPolyZ::zero());
}

#[test]
fn rational_substitution_clears_denominators_by_a_positive_factor() {
    // p = 4x^2 + 2x + 1 at x = 1/2 is 1 + 1 + 1 = 3; cleared by den^deg = 4.
    let p = mp(&[(4, &[(X, 2)]), (2, &[(X, 1)]), (1, &[])]);
    assert_eq!(subst_rational(&p, X, &q(1, 2)), mp(&[(12, &[])]));
    // A negative rational: -1/2 gives 1 - 1 + 1 = 1, times 4.
    assert_eq!(subst_rational(&p, X, &q(-1, 2)), mp(&[(4, &[])]));
    // Degree 0 in the variable: untouched.
    assert_eq!(subst_rational(&p, Y, &q(3, 7)), p);
}

// ---------------------------------------------------------------------------
// eval_sign_at
// ---------------------------------------------------------------------------

#[test]
fn sign_at_rational_point() {
    let p = mp(&[(1, &[(X, 2)]), (-2, &[])]);
    let a = assign(&[(X, Anum::Rat(q(3, 2)))]);
    assert_eq!(eval_sign_at(&p, &a), Some(1)); // 9/4 - 2 > 0
    let b = assign(&[(X, Anum::Rat(q(1, 1)))]);
    assert_eq!(eval_sign_at(&p, &b), Some(-1));
}

#[test]
fn sign_at_algebraic_point_is_exactly_zero() {
    // x^2 - 2 at sqrt(2). The interval fast path can NEVER decide this; only
    // the algebraic zero certificate can.
    let p = mp(&[(1, &[(X, 2)]), (-2, &[])]);
    let a = assign(&[(X, Anum::Alg(sqrt2()))]);
    assert_eq!(eval_sign_at(&p, &a), Some(0));
}

#[test]
fn sign_at_two_algebraic_coordinates() {
    // x*y - 2 at x = y = sqrt(2) is exactly zero: the full exact-arithmetic
    // path, since neither coordinate can be substituted away.
    let s = sqrt2();
    let p = mp(&[(1, &[(X, 1), (Y, 1)]), (-2, &[])]);
    let a = assign(&[(X, Anum::Alg(s.clone())), (Y, Anum::Alg(s.clone()))]);
    assert_eq!(eval_sign_at(&p, &a), Some(0));

    // x*y - 3 at the same point is negative (2 - 3).
    let n = mp(&[(1, &[(X, 1), (Y, 1)]), (-3, &[])]);
    assert_eq!(eval_sign_at(&n, &a), Some(-1));

    // Two DIFFERENT algebraic points: sqrt(2)*sqrt(3) - 2 > 0.
    let s3 = alg(&[-3, 0, 1], 1, 2);
    let b = assign(&[(X, Anum::Alg(s)), (Y, Anum::Alg(s3))]);
    assert_eq!(eval_sign_at(&p, &b), Some(1));
}

#[test]
fn sign_of_zero_and_constant_polynomials() {
    let a = Var2Anum::new();
    assert_eq!(eval_sign_at(&MPolyZ::zero(), &a), Some(0));
    assert_eq!(eval_sign_at(&mp(&[(-7, &[])]), &a), Some(-1));
    assert_eq!(eval_sign_at(&mp(&[(7, &[])]), &a), Some(1));
}

#[test]
fn sign_refuses_an_unassigned_coordinate() {
    let p = mp(&[(1, &[(X, 1)]), (1, &[(Y, 1)])]);
    let a = assign(&[(X, Anum::Rat(int(1)))]);
    assert_eq!(eval_sign_at(&p, &a), None);
}

// ---------------------------------------------------------------------------
// isolate_roots_at — the ordinary paths
// ---------------------------------------------------------------------------

#[test]
fn univariate_needs_no_assignment() {
    // x^2 - 2 with nothing assigned: +- sqrt(2).
    let p = mp(&[(1, &[(X, 2)]), (-2, &[])]);
    let roots = isolate_roots_at(&p, X, &Var2Anum::new()).expect("isolates");
    assert_roots(&roots, &[-SQRT_2, SQRT_2]);
}

#[test]
fn rational_coordinates_are_substituted() {
    // y*x - 3 at y = 2: the single root 3/2, exactly rational.
    let p = mp(&[(1, &[(X, 1), (Y, 1)]), (-3, &[])]);
    let a = assign(&[(Y, Anum::Rat(int(2)))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_eq!(roots.len(), 1);
    match &roots[0] {
        Anum::Rat(r) => assert_eq!(*r, q(3, 2)),
        other => panic!("expected an exact rational root, got {other:?}"),
    }
}

#[test]
fn the_sieve_removes_conjugate_roots() {
    // p = x - y at y = sqrt(2). The resultant Res_y(x - y, y^2 - 2) is
    // x^2 - 2, whose roots are BOTH +-sqrt(2) — but only +sqrt(2) is a root
    // of p at this sample point. If the sieve is missing, this test reports
    // two roots.
    let p = mp(&[(1, &[(X, 1)]), (-1, &[(Y, 1)])]);
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_roots(&roots, &[SQRT_2]);
}

#[test]
fn genuine_conjugate_pair_survives_the_sieve() {
    // p = x^2 - y at y = sqrt(2): both +-2^(1/4) really are roots, so the
    // sieve must NOT remove either. (The complement of the test above.)
    let p = mp(&[(1, &[(X, 2)]), (-1, &[(Y, 1)])]);
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_roots(&roots, &[-1.189_207_115, 1.189_207_115]);
}

#[test]
fn two_algebraic_coordinates() {
    // p = x - y - w at y = sqrt(2), w = sqrt(3): the single root
    // sqrt(2) + sqrt(3), reached through two successive resultants.
    let p = mp(&[(1, &[(X, 1)]), (-1, &[(Y, 1)]), (-1, &[(W, 1)])]);
    let a = assign(&[
        (Y, Anum::Alg(sqrt2())),
        (W, Anum::Alg(alg(&[-3, 0, 1], 1, 2))),
    ]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_roots(&roots, &[3.146_264_370]);
}

#[test]
fn repeated_roots_are_reported_once() {
    // (x - y)^2 at y = sqrt(2): one root, sqrt(2).
    let p = mp(&[(1, &[(X, 2)]), (-2, &[(X, 1), (Y, 1)]), (1, &[(Y, 2)])]);
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_roots(&roots, &[SQRT_2]);
}

#[test]
fn leading_coefficient_vanishing_at_the_point_drops_the_degree() {
    // p = (y^2 - 2)x^2 + x - 1 at y = sqrt(2). The x^2 coefficient is zero
    // AT THE SAMPLE POINT but not identically, so the specialized polynomial
    // is x - 1 with the single root 1 — not a quadratic.
    let p = mp(&[
        (1, &[(X, 2), (Y, 2)]),
        (-2, &[(X, 2)]),
        (1, &[(X, 1)]),
        (-1, &[]),
    ]);
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_eq!(roots.len(), 1);
    match &roots[0] {
        Anum::Rat(r) => assert_eq!(*r, int(1)),
        other => panic!("expected the exact rational root 1, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// isolate_roots_at — degenerate inputs
// ---------------------------------------------------------------------------

#[test]
fn zero_and_constant_polynomials_have_no_roots() {
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    assert_eq!(isolate_roots_at(&MPolyZ::zero(), X, &a), Some(Vec::new()));
    assert_eq!(isolate_roots_at(&mp(&[(5, &[])]), X, &a), Some(Vec::new()));
}

#[test]
fn a_polynomial_whose_x_vanishes_reports_no_roots() {
    // (y - 2)x + 1 at y = 2 collapses to the constant 1. z3 reports no roots
    // here, and so does AY.
    let p = mp(&[(1, &[(X, 1), (Y, 1)]), (-2, &[(X, 1)]), (1, &[])]);
    let a = assign(&[(Y, Anum::Rat(int(2)))]);
    assert_eq!(isolate_roots_at(&p, X, &a), Some(Vec::new()));
}

#[test]
fn a_polynomial_identically_zero_at_the_point_reports_no_roots() {
    // (y - 2)x at y = 2 is identically zero in x. z3's convention is to
    // report NO roots rather than infinitely many; AY matches it, and
    // `eval_sign_at` is how a caller distinguishes the two.
    let p = mp(&[(1, &[(X, 1), (Y, 1)]), (-2, &[(X, 1)])]);
    let a = assign(&[(Y, Anum::Rat(int(2)))]);
    assert_eq!(isolate_roots_at(&p, X, &a), Some(Vec::new()));
    let both = assign(&[(X, Anum::Rat(int(9))), (Y, Anum::Rat(int(2)))]);
    assert_eq!(eval_sign_at(&p, &both), Some(0));
}

#[test]
fn an_unassigned_coordinate_is_refused() {
    let p = mp(&[(1, &[(X, 1)]), (-1, &[(Y, 1)])]);
    assert_eq!(isolate_roots_at(&p, X, &Var2Anum::new()), None);
}

#[test]
fn no_real_roots_at_the_point() {
    // x^2 + y at y = sqrt(2) has no real roots.
    let p = mp(&[(1, &[(X, 2)]), (1, &[(Y, 1)])]);
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    assert_eq!(isolate_roots_at(&p, X, &a), Some(Vec::new()));
}

// ---------------------------------------------------------------------------
// isolate_roots_at — the vanishing-resultant escape
// ---------------------------------------------------------------------------

#[test]
fn vanishing_resultant_escape() {
    // p = (y - 5)(x^2 - y), with y = sqrt(2) defined by the REDUCIBLE
    // square-free polynomial (y^2 - 2)(y - 5).
    //
    // `p` and the defining polynomial share the factor (y - 5), so
    // Res_y(p, m_y) vanishes identically and says nothing. The escape has to
    // pick up the leading coefficient (y - 5), which is NOT zero at the
    // sample point, bind it to a fresh variable, and recurse.
    //
    // The answer is the root set of (sqrt(2) - 5)(x^2 - sqrt(2)) = 0, i.e.
    // +-2^(1/4).
    let p = mp(&[
        (1, &[(X, 2), (Y, 1)]),
        (-5, &[(X, 2)]),
        (-1, &[(Y, 2)]),
        (5, &[(Y, 1)]),
    ]);
    let a = assign(&[(Y, Anum::Alg(sqrt2_reducible()))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_roots(&roots, &[-1.189_207_115, 1.189_207_115]);
}

#[test]
fn vanishing_resultant_escape_linear_case() {
    // p = (y - 5)(x - y) at the same reducible sqrt(2). Linear in x, so the
    // escape solves c1*x + c0 = 0 with exact algebraic arithmetic instead of
    // recursing. The root is sqrt(2).
    let p = mp(&[
        (1, &[(X, 1), (Y, 1)]),
        (-5, &[(X, 1)]),
        (-1, &[(Y, 2)]),
        (5, &[(Y, 1)]),
    ]);
    let a = assign(&[(Y, Anum::Alg(sqrt2_reducible()))]);
    let roots = isolate_roots_at(&p, X, &a).expect("isolates");
    assert_roots(&roots, &[SQRT_2]);
}

#[test]
fn vanishing_resultant_with_every_coefficient_zero() {
    // p = (y^2 - 2)(x^2 + x + 1) at the reducible sqrt(2): the resultant
    // vanishes AND every coefficient of x is zero at the point, so `p` is
    // identically zero there and no roots are reported.
    let p = mp(&[
        (1, &[(X, 2), (Y, 2)]),
        (-2, &[(X, 2)]),
        (1, &[(X, 1), (Y, 2)]),
        (-2, &[(X, 1)]),
        (1, &[(Y, 2)]),
        (-2, &[]),
    ]);
    let a = assign(&[(Y, Anum::Alg(sqrt2_reducible()))]);
    assert_eq!(isolate_roots_at(&p, X, &a), Some(Vec::new()));
}

// ---------------------------------------------------------------------------
// isolate_roots_closest_at
// ---------------------------------------------------------------------------

#[test]
fn closest_roots_bracket_the_query_point() {
    // x^3 - x = x(x-1)(x+1): roots -1, 0, 1.
    let p = mp(&[(1, &[(X, 3)]), (-1, &[(X, 1)])]);
    let a = Var2Anum::new();

    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &q(1, 2)).expect("isolates");
    assert_roots(&roots, &[0.0, 1.0]);
    assert_eq!(idx, vec![2, 3]);

    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &q(-1, 2)).expect("isolates");
    assert_roots(&roots, &[-1.0, 0.0]);
    assert_eq!(idx, vec![1, 2]);
}

#[test]
fn closest_roots_below_and_above_everything() {
    let p = mp(&[(1, &[(X, 3)]), (-1, &[(X, 1)])]);
    let a = Var2Anum::new();

    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &int(-5)).expect("isolates");
    assert_roots(&roots, &[-1.0]);
    assert_eq!(idx, vec![1]);

    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &int(5)).expect("isolates");
    assert_roots(&roots, &[1.0]);
    assert_eq!(idx, vec![3]);
}

#[test]
fn a_query_point_that_is_itself_a_root_returns_only_that_root() {
    let p = mp(&[(1, &[(X, 3)]), (-1, &[(X, 1)])]);
    let a = Var2Anum::new();
    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &int(0)).expect("isolates");
    assert_roots(&roots, &[0.0]);
    assert_eq!(idx, vec![2]);
}

#[test]
fn closest_roots_at_an_algebraic_sample_point() {
    // x^2 - y at y = sqrt(2): roots -+2^(1/4). Around 0 both bracket it.
    let p = mp(&[(1, &[(X, 2)]), (-1, &[(Y, 1)])]);
    let a = assign(&[(Y, Anum::Alg(sqrt2()))]);
    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &int(0)).expect("isolates");
    assert_roots(&roots, &[-1.189_207_115, 1.189_207_115]);
    assert_eq!(idx, vec![1, 2]);

    // Above both: only the larger one comes back.
    let (roots, idx) = isolate_roots_closest_at(&p, X, &a, &int(3)).expect("isolates");
    assert_roots(&roots, &[1.189_207_115]);
    assert_eq!(idx, vec![2]);
}

#[test]
fn no_roots_means_no_closest_roots() {
    let p = mp(&[(1, &[(X, 2)]), (1, &[])]);
    let (roots, idx) =
        isolate_roots_closest_at(&p, X, &Var2Anum::new(), &int(0)).expect("isolates");
    assert!(roots.is_empty());
    assert!(idx.is_empty());
}

// ---------------------------------------------------------------------------
// Anum
// ---------------------------------------------------------------------------

#[test]
fn anum_round_trips_through_the_scalar_representation() {
    let s = sqrt2();
    let back = Anum::from_scalar(&Anum::Alg(s.clone()).to_scalar()).expect("representable");
    assert_eq!(
        back.cmp_rational(&q(14_142_135, 10_000_000)),
        Some(Ordering::Greater)
    );
    assert_eq!(
        back.cmp_rational(&q(14_142_136, 10_000_000)),
        Some(Ordering::Less)
    );

    let r = Anum::Rat(q(-7, 3));
    let back = Anum::from_scalar(&r.to_scalar()).expect("representable");
    assert_eq!(back.cmp_rational(&q(-7, 3)), Some(Ordering::Equal));
    assert_eq!(r.degree(), 1);
    assert_eq!(Anum::Alg(s).degree(), 2);
}
