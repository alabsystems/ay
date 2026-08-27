// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::ialg`].
//!
//! These pin the algebraic-endpoint behaviour that `feasible_set.rs` cannot
//! express at all, plus the guards and the liveness bounds. The differential
//! coverage against z3 lives in `crates/ay-nra-oracle/src/ialg.rs`.

use super::*;

use num_bigint::BigInt;
use num_rational::BigRational;

fn q(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn ri(n: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(n)))
}

fn rq(n: i64, d: i64) -> Anum {
    Anum::rational(q(n, d))
}

/// `sqrt(d)`: the positive root of `x^2 - d`, isolated in `(0, d + 1)`.
fn sqrt(d: i64) -> Anum {
    let p = vec![BigInt::from(-d), BigInt::zero(), BigInt::one()];
    let iv =
        BqInterval::new(Bq::zero(), Bq::from_int(BigInt::from(d + 1))).expect("bracket is ordered");
    Anum::from_poly_interval(&p, &iv).expect("x^2 - d has one root in (0, d+1)")
}

fn fin(a: Anum) -> AEnd {
    AEnd::Fin(a)
}

fn iv(lo: AEnd, lo_open: bool, hi: AEnd, hi_open: bool) -> AInterval {
    DecidedInterval::from_bounds(lo, lo_open, hi, hi_open, Just::none())
        .expect("decided")
        .into_interval()
        .expect("expected non-empty")
}

fn set(ivs: Vec<AInterval>) -> IntervalSet {
    IntervalSet::normalize(ivs).expect("normalizes")
}

// ====== endpoints ======

#[test]
fn ialg_endpoint_order_algebraic() {
    let s2 = fin(sqrt(2));
    let s3 = fin(sqrt(3));
    assert_eq!(s2.cmp_value(&s3), Some(Ordering::Less));
    assert_eq!(s3.cmp_value(&s2), Some(Ordering::Greater));
    assert_eq!(s2.cmp_value(&s2), Some(Ordering::Equal));
    assert_eq!(AEnd::NegInf.cmp_value(&s2), Some(Ordering::Less));
    assert_eq!(AEnd::PosInf.cmp_value(&s2), Some(Ordering::Greater));
    assert_eq!(AEnd::NegInf.cmp_value(&AEnd::PosInf), Some(Ordering::Less));
}

/// The endpoint `feasible_set.rs` cannot name: `sqrt(2)` sits strictly between
/// every pair of rationals that bracket it, and equals none of them.
#[test]
fn ialg_algebraic_endpoint_is_not_rational() {
    let s2 = sqrt(2);
    assert!(!s2.is_rational());
    assert_eq!(s2.cmp_anum(&rq(1414, 1000)), Some(Ordering::Greater));
    assert_eq!(s2.cmp_anum(&rq(1415, 1000)), Some(Ordering::Less));
}

/// An infinite endpoint that is not open is malformed, and is refused.
#[test]
fn ialg_closed_infinity_refused() {
    assert_eq!(
        DecidedInterval::from_bounds(AEnd::NegInf, false, fin(ri(1)), true, Just::none()),
        None
    );
    assert_eq!(
        DecidedInterval::from_bounds(fin(ri(1)), true, AEnd::PosInf, false, Just::none()),
        None
    );
}

// ====== emptiness ======

#[test]
fn ialg_empty_cases_are_proved_not_guessed() {
    // (3, 3) is empty; [3, 3] is not.
    assert!(
        DecidedInterval::from_bounds(fin(ri(3)), true, fin(ri(3)), true, Just::none())
            .expect("decided")
            .into_interval()
            .is_none()
    );
    assert!(
        DecidedInterval::from_bounds(fin(ri(3)), false, fin(ri(3)), true, Just::none())
            .expect("decided")
            .into_interval()
            .is_none()
    );
    assert!(
        DecidedInterval::from_bounds(fin(ri(3)), false, fin(ri(3)), false, Just::none())
            .expect("decided")
            .into_interval()
            .is_some()
    );
    // Inverted.
    assert!(
        DecidedInterval::from_bounds(fin(ri(5)), false, fin(ri(1)), false, Just::none())
            .expect("decided")
            .into_interval()
            .is_none()
    );
}

#[test]
fn ialg_empty_set_is_the_conflict_signal() {
    let e = IntervalSet::empty();
    assert!(e.is_empty());
    assert_eq!(e.len(), 0);
    assert_eq!(e.pick(), None);
    assert_eq!(e.contains(&ri(0)), Some(false));
}

/// Two intervals with algebraic endpoints that do not overlap intersect to the
/// empty set — the conflict — and the emptiness is decided exactly.
#[test]
fn ialg_disjoint_algebraic_intersection_is_empty() {
    let a = set(vec![iv(AEnd::NegInf, true, fin(sqrt(2)), true)]);
    let b = set(vec![iv(fin(sqrt(3)), true, AEnd::PosInf, true)]);
    assert!(a.intersect(&b).expect("decided").is_empty());
}

// ====== justifications ======

#[test]
fn ialg_intersection_keeps_both_justifications() {
    let ja = Just::of(7).expect("nonzero");
    let jb = Just::of(-9).expect("nonzero");
    let a = DecidedInterval::from_bounds(fin(ri(0)), false, fin(ri(10)), false, ja)
        .expect("decided")
        .into_interval()
        .expect("non-empty");
    let b = DecidedInterval::from_bounds(fin(ri(5)), false, fin(ri(20)), false, jb)
        .expect("decided")
        .into_interval()
        .expect("non-empty");
    let sa = IntervalSet::normalize(vec![a]).expect("ok");
    let sb = IntervalSet::normalize(vec![b]).expect("ok");
    let inter = sa.intersect(&sb).expect("decided");
    assert_eq!(inter.len(), 1);
    assert_eq!(inter.intervals()[0].just().lits(), &[-9, 7]);
    assert_eq!(inter.justification().expect("ok").lits(), &[-9, 7]);
}

#[test]
fn ialg_just_rejects_zero_and_dedups() {
    assert_eq!(Just::of(0), None);
    let a = Just::of(3).expect("ok");
    let b = Just::of(3).expect("ok");
    assert_eq!(a.merge(&b).expect("ok").len(), 1);
}

/// `feasible_set.rs` has no justification field at all; this is the closest
/// thing it can do, and the difference is the point.
#[test]
fn ialg_justification_survives_a_chain_of_intersections() {
    let mut s = IntervalSet::full(Just::none());
    for lit in 1..=5i32 {
        let interval = DecidedInterval::from_bounds(
            fin(ri(-100)),
            true,
            fin(ri(100)),
            true,
            Just::of(lit).expect("nonzero"),
        )
        .expect("decided")
        .into_interval()
        .expect("non-empty");
        let piece = IntervalSet::normalize(vec![interval]).expect("ok");
        s = s.intersect(&piece).expect("decided");
    }
    assert_eq!(s.justification().expect("ok").lits(), &[1, 2, 3, 4, 5]);
}

// ====== union / adjacency ======

#[test]
fn ialg_union_merges_adjacent_closed_open() {
    // [1,2] U (2,3] has no gap.
    let s = set(vec![
        iv(fin(ri(1)), false, fin(ri(2)), false),
        iv(fin(ri(2)), true, fin(ri(3)), false),
    ]);
    assert_eq!(s.len(), 1);
    assert_eq!(s.contains(&ri(2)), Some(true));
    assert_eq!(s.contains(&rq(5, 2)), Some(true));
}

#[test]
fn ialg_union_keeps_the_single_point_gap() {
    // (1,2) U (2,3) leaves out exactly 2.
    let s = set(vec![
        iv(fin(ri(1)), true, fin(ri(2)), true),
        iv(fin(ri(2)), true, fin(ri(3)), true),
    ]);
    assert_eq!(s.len(), 2);
    assert_eq!(s.contains(&ri(2)), Some(false));
    assert_eq!(s.contains(&rq(3, 2)), Some(true));
}

/// Normalisation must sort, and the sort must handle algebraic endpoints given
/// in the wrong order.
#[test]
fn ialg_normalize_sorts_algebraic_endpoints() {
    let s = set(vec![
        iv(fin(sqrt(7)), true, AEnd::PosInf, true),
        iv(AEnd::NegInf, true, fin(sqrt(2)), true),
        iv(fin(sqrt(3)), true, fin(sqrt(5)), true),
    ]);
    assert_eq!(s.len(), 3);
    let los: Vec<bool> = s.intervals().iter().map(|i| i.lo().is_finite()).collect();
    assert_eq!(los, vec![false, true, true]);
    assert_eq!(s.contains(&ri(0)), Some(true));
    assert_eq!(s.contains(&rq(19, 10)), Some(true)); // between sqrt3 and sqrt5
    assert_eq!(s.contains(&rq(3, 2)), Some(false)); // between sqrt2 and sqrt3
}

// ====== complement / subtract ======

#[test]
fn ialg_complement_of_full_is_empty_and_back() {
    let f = IntervalSet::full(Just::none());
    let c = f.complement().expect("decided");
    assert!(c.is_empty());
    assert!(!c.complement().expect("decided").is_empty());
}

#[test]
fn ialg_complement_flips_strictness() {
    // complement of [1,2] is (-inf,1) U (2,+inf)
    let s = set(vec![iv(fin(ri(1)), false, fin(ri(2)), false)]);
    let c = s.complement().expect("decided");
    assert_eq!(c.len(), 2);
    assert_eq!(c.contains(&ri(1)), Some(false));
    assert_eq!(c.contains(&ri(2)), Some(false));
    assert_eq!(c.contains(&ri(0)), Some(true));
    assert_eq!(c.contains(&ri(3)), Some(true));
}

#[test]
fn ialg_complement_with_algebraic_endpoints() {
    // complement of (sqrt2, sqrt3) is (-inf, sqrt2] U [sqrt3, +inf)
    let s = set(vec![iv(fin(sqrt(2)), true, fin(sqrt(3)), true)]);
    let c = s.complement().expect("decided");
    assert_eq!(c.len(), 2);
    assert_eq!(c.contains(&sqrt(2)), Some(true));
    assert_eq!(c.contains(&sqrt(3)), Some(true));
    assert_eq!(c.contains(&rq(3, 2)), Some(false));
}

/// Removing a refuted cell — the operation MCSAT performs on every conflict,
/// and the one `feasible_set.rs` has no method for.
#[test]
fn ialg_subtract_removes_a_refuted_cell() {
    let s = set(vec![iv(fin(ri(0)), false, fin(ri(10)), false)]);
    let refuted = set(vec![iv(fin(ri(3)), false, fin(ri(5)), false)]);
    let r = s.subtract(&refuted).expect("decided");
    assert_eq!(r.len(), 2);
    assert_eq!(r.contains(&ri(2)), Some(true));
    assert_eq!(r.contains(&ri(3)), Some(false));
    assert_eq!(r.contains(&ri(4)), Some(false));
    assert_eq!(r.contains(&ri(5)), Some(false));
    assert_eq!(r.contains(&ri(6)), Some(true));
}

#[test]
fn ialg_subtract_everything_is_the_conflict() {
    let s = set(vec![iv(fin(ri(0)), false, fin(ri(10)), false)]);
    assert!(s
        .subtract(&IntervalSet::full(Just::none()))
        .expect("decided")
        .is_empty());
}

// ====== pick ======

#[test]
fn ialg_pick_prefers_an_integer() {
    // (1/3, 7/3) holds 1 and 2; the midpoint would be 4/3.
    let s = set(vec![iv(fin(rq(1, 3)), true, fin(rq(7, 3)), true)]);
    let v = s.pick().expect("non-empty");
    assert_eq!(classify_value(&v), Rung::Integer);
    assert_eq!(s.contains(&v), Some(true));
}

#[test]
fn ialg_pick_prefers_zero_among_integers() {
    let s = set(vec![iv(fin(ri(-5)), true, fin(ri(5)), true)]);
    let v = s.pick().expect("non-empty");
    assert_eq!(v.to_rational().expect("rational"), &BigRational::zero());
}

#[test]
fn ialg_pick_falls_to_a_simple_rational() {
    // (1/3, 2/3) holds no integer; 1/2 is the simplest thing in it.
    let s = set(vec![iv(fin(rq(1, 3)), true, fin(rq(2, 3)), true)]);
    let v = s.pick().expect("non-empty");
    assert_eq!(s.contains(&v), Some(true));
    assert_eq!(classify_value(&v), Rung::Simple);
    assert_eq!(v.to_rational().expect("rational"), &q(1, 2));
}

/// The behaviour `Interval::pick_value` at `feasible_set.rs:182` does not have:
/// its midpoint of `(1/3, 7/3)` is `4/3`, and iterating doubles the denominator
/// forever. Here the answer stays an integer.
#[test]
fn ialg_pick_does_not_grow_the_denominator_under_iteration() {
    let mut s = set(vec![iv(fin(rq(1, 3)), true, fin(rq(7, 3)), true)]);
    for _ in 0..8 {
        let v = s.pick().expect("non-empty");
        assert!(
            classify_value(&v) <= Rung::Simple,
            "rung grew to {:?}",
            classify_value(&v)
        );
        // Narrow around the pick the way a search would, and pick again.
        s = s
            .intersect(&set(vec![iv(fin(rq(1, 3)), true, fin(rq(7, 3)), true)]))
            .expect("decided");
    }
}

#[test]
fn ialg_pick_between_two_algebraic_endpoints() {
    // (sqrt2, sqrt3) holds no integer; it does hold 3/2.
    let s = set(vec![iv(fin(sqrt(2)), true, fin(sqrt(3)), true)]);
    let v = s.pick().expect("non-empty");
    assert_eq!(s.contains(&v), Some(true));
    assert!(classify_value(&v) <= Rung::Dyadic);
}

/// A singleton at an algebraic point has NOTHING simpler in it, so the ladder
/// must fall all the way to the algebraic rung and return the point itself.
#[test]
fn ialg_pick_algebraic_singleton() {
    let s2 = sqrt(2);
    let s = set(vec![iv(fin(s2.clone()), false, fin(s2.clone()), false)]);
    let v = s.pick().expect("non-empty");
    assert_eq!(classify_value(&v), Rung::Algebraic);
    assert_eq!(v.cmp_anum(&s2), Some(Ordering::Equal));
    assert_eq!(s.contains(&v), Some(true));
}

#[test]
fn ialg_pick_skips_an_interval_it_cannot_serve() {
    // First interval is an algebraic singleton, second holds the integer 5.
    let s2 = sqrt(2);
    let s = set(vec![
        iv(fin(s2.clone()), false, fin(s2), false),
        iv(fin(ri(4)), true, fin(ri(6)), true),
    ]);
    assert_eq!(s.len(), 2);
    let v = s.pick().expect("non-empty");
    assert_eq!(s.contains(&v), Some(true));
}

#[test]
fn ialg_pick_unbounded_sides() {
    assert_eq!(
        IntervalSet::full(Just::none())
            .pick()
            .expect("non-empty")
            .to_rational()
            .expect("rational"),
        &BigRational::zero()
    );
    let up = set(vec![iv(fin(sqrt(2)), true, AEnd::PosInf, true)]);
    let v = up.pick().expect("non-empty");
    assert_eq!(up.contains(&v), Some(true));
    assert_eq!(classify_value(&v), Rung::Integer);
    let down = set(vec![iv(AEnd::NegInf, true, fin(sqrt(2)), true)]);
    let v = down.pick().expect("non-empty");
    assert_eq!(down.contains(&v), Some(true));
    assert_eq!(classify_value(&v), Rung::Integer);
}

/// Every value `pick` returns is VERIFIED in the set before it is returned, so
/// the ladder being a heuristic never turns into a wrong answer.
#[test]
fn ialg_pick_result_is_always_in_the_set() {
    let cases = vec![
        set(vec![iv(fin(rq(1, 7)), true, fin(rq(2, 7)), true)]),
        set(vec![iv(fin(sqrt(2)), true, fin(sqrt(3)), true)]),
        set(vec![iv(fin(sqrt(11)), false, fin(sqrt(13)), false)]),
        set(vec![iv(AEnd::NegInf, true, fin(rq(-100_001, 100)), true)]),
        set(vec![iv(fin(rq(99_999, 100)), true, AEnd::PosInf, true)]),
    ];
    for s in cases {
        let v = s.pick().expect("non-empty");
        assert_eq!(s.contains(&v), Some(true), "pick escaped its set");
    }
}

// ====== classify ======

#[test]
fn ialg_classify_is_derived_from_the_value() {
    assert_eq!(classify_value(&ri(0)), Rung::Integer);
    assert_eq!(classify_value(&ri(-7)), Rung::Integer);
    assert_eq!(classify_value(&rq(1, 2)), Rung::Simple);
    assert_eq!(classify_value(&rq(3, 16)), Rung::Simple);
    assert_eq!(classify_value(&rq(1, 32)), Rung::Dyadic);
    assert_eq!(classify_value(&rq(1, 1024)), Rung::Dyadic);
    assert_eq!(classify_value(&rq(1, 17)), Rung::Rational);
    assert_eq!(classify_value(&sqrt(2)), Rung::Algebraic);
}

#[test]
fn ialg_rungs_are_ordered_simplest_first() {
    assert!(Rung::Integer < Rung::Simple);
    assert!(Rung::Simple < Rung::Dyadic);
    assert!(Rung::Dyadic < Rung::Rational);
    assert!(Rung::Rational < Rung::Algebraic);
}

// ====== from_sign_condition ======

#[test]
fn ialg_sign_condition_x2_minus_2_negative() {
    // x^2 - 2 < 0 on (-sqrt2, sqrt2).
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let s2 = sqrt(2);
    let ns2 = s2.neg().expect("negation");
    let s = from_sign_condition(&p, &[ns2, s2], SignCond::Lt, Just::none()).expect("decided");
    assert_eq!(s.len(), 1);
    assert_eq!(s.contains(&ri(0)), Some(true));
    assert_eq!(s.contains(&ri(1)), Some(true));
    assert_eq!(s.contains(&ri(2)), Some(false));
    assert_eq!(s.contains(&ri(-2)), Some(false));
    assert_eq!(s.contains(&sqrt(2)), Some(false));
}

#[test]
fn ialg_sign_condition_x2_minus_2_positive_is_two_rays() {
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let s2 = sqrt(2);
    let ns2 = s2.neg().expect("negation");
    let s = from_sign_condition(&p, &[ns2, s2], SignCond::Gt, Just::none()).expect("decided");
    assert_eq!(s.len(), 2);
    assert_eq!(s.contains(&ri(2)), Some(true));
    assert_eq!(s.contains(&ri(-2)), Some(true));
    assert_eq!(s.contains(&ri(0)), Some(false));
}

#[test]
fn ialg_sign_condition_ge_glues_the_root_cells_on() {
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let s2 = sqrt(2);
    let ns2 = s2.neg().expect("negation");
    let s =
        from_sign_condition(&p, &[ns2, s2.clone()], SignCond::Ge, Just::none()).expect("decided");
    assert_eq!(s.len(), 2);
    // The closed root cell merged onto the open ray.
    assert_eq!(s.contains(&s2), Some(true));
    assert_eq!(s.contains(&ri(0)), Some(false));
}

#[test]
fn ialg_sign_condition_eq_is_the_root_set() {
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let s2 = sqrt(2);
    let ns2 = s2.neg().expect("negation");
    let s = from_sign_condition(&p, &[ns2.clone(), s2.clone()], SignCond::Eq, Just::none())
        .expect("decided");
    assert_eq!(s.len(), 2);
    assert_eq!(s.contains(&s2), Some(true));
    assert_eq!(s.contains(&ns2), Some(true));
    assert_eq!(s.contains(&ri(0)), Some(false));
    assert_eq!(s.pick().map(|v| classify_value(&v)), Some(Rung::Algebraic));
}

#[test]
fn ialg_sign_condition_rootless_polynomial() {
    // x^2 + 1 > 0 everywhere; no roots.
    let p = vec![BigInt::one(), BigInt::zero(), BigInt::one()];
    let s = from_sign_condition(&p, &[], SignCond::Gt, Just::none()).expect("decided");
    assert_eq!(s.len(), 1);
    assert_eq!(s.contains(&ri(0)), Some(true));
    let e = from_sign_condition(&p, &[], SignCond::Lt, Just::none()).expect("decided");
    assert!(e.is_empty());
}

#[test]
fn ialg_sign_condition_zero_polynomial() {
    let z: Vec<BigInt> = vec![BigInt::zero()];
    let equal = from_sign_condition(&z, &[], SignCond::Eq, Just::none()).expect("decided");
    assert_eq!(equal.len(), 1);
    assert!(from_sign_condition(&z, &[], SignCond::Ne, Just::none())
        .expect("decided")
        .is_empty());
}

/// The precondition is VERIFIED, not assumed: a descending or duplicated root
/// list is refused rather than producing a malformed decomposition.
#[test]
fn ialg_sign_condition_refuses_unsorted_roots() {
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let s2 = sqrt(2);
    let ns2 = s2.neg().expect("negation");
    assert_eq!(
        from_sign_condition(&p, &[s2.clone(), ns2], SignCond::Lt, Just::none()),
        None
    );
    assert_eq!(
        from_sign_condition(&p, &[s2.clone(), s2], SignCond::Lt, Just::none()),
        None
    );
}

/// A root list that does not match the polynomial makes a sample point land on
/// a root; that is refused, not papered over.
#[test]
fn ialg_sign_condition_refuses_a_wrong_root_list() {
    // p = x^2 - 2, but claim the root is at 0.
    //
    // STRENGTHENED 2026-08-06. This test is named "refuses", but what it
    // originally asserted was weaker than its name: the old code ACCEPTED the
    // wrong list and merely happened not to claim `x^2 - 2 < 0` anywhere,
    // because both cells sample outside the Cauchy bound where `p > 0`. That is
    // luck about this particular input, not a property.
    //
    // A verifier showed the luck runs out: with `p = x^2 - 1` and the root `-1`
    // DROPPED, `SignCond::Lt` returned the EMPTY set for a feasible set that is
    // genuinely `(-1, 1)`. `from_sign_condition` now verifies by Sturm count
    // that the list is exactly the real roots, so a wrong list is refused
    // outright — which is what this test's name always claimed.
    let p = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    assert_eq!(
        from_sign_condition(&p, &[ri(0)], SignCond::Lt, Just::none()),
        None,
        "a root list that is not the real roots of p must be REFUSED"
    );
}

// ====== guards and bounds ======

/// [`IntervalSet::from_ordered`] is a guard that CAN fire: hand it an
/// out-of-order pair and it declines instead of producing a malformed set.
#[test]
fn ialg_intersect_guard_fires() {
    let bad = vec![
        iv(fin(ri(5)), false, fin(ri(6)), false),
        iv(fin(ri(1)), false, fin(ri(2)), false),
    ];
    assert_eq!(IntervalSet::from_ordered(bad), None);
    // Overlapping is also refused.
    let overlap = vec![
        iv(fin(ri(1)), false, fin(ri(6)), false),
        iv(fin(ri(2)), false, fin(ri(3)), false),
    ];
    assert_eq!(IntervalSet::from_ordered(overlap), None);
    // Adjacent-with-no-gap is refused too: it should have been merged.
    let adjacent = vec![
        iv(fin(ri(1)), false, fin(ri(2)), false),
        iv(fin(ri(2)), true, fin(ri(3)), false),
    ];
    assert_eq!(IntervalSet::from_ordered(adjacent), None);
}

include!("ialg_tests/bounds.rs");

/// `inner_dyadic` terminates on a singleton, which has no interior at all.
#[test]
fn ialg_inner_dyadic_declines_on_a_singleton() {
    let s2 = sqrt(2);
    let point = iv(fin(s2.clone()), false, fin(s2), false);
    assert_eq!(inner_dyadic(&point), None);
}

/// Interval-set laws that must hold whatever the endpoints are.
#[test]
fn ialg_algebraic_laws() {
    let a = set(vec![iv(fin(sqrt(2)), true, fin(sqrt(7)), true)]);
    let b = set(vec![iv(fin(sqrt(3)), true, fin(sqrt(13)), true)]);
    // Commutative.
    assert_eq!(a.intersect(&b).expect("d"), b.intersect(&a).expect("d"));
    assert_eq!(a.union(&b).expect("d"), b.union(&a).expect("d"));
    // Double complement is the identity.
    let cc = a.complement().expect("d").complement().expect("d");
    assert_eq!(cc, a);
    // a \ b, then union with a n b, gives a back.
    let left = a.subtract(&b).expect("d");
    let mid = a.intersect(&b).expect("d");
    assert_eq!(left.union(&mid).expect("d"), a);
    // Subtracting the empty set changes nothing.
    assert_eq!(a.subtract(&IntervalSet::empty()).expect("d"), a);
}

/// `from_sign_condition` must refuse incomplete or padded root lists.
///
/// Ordering alone is unsound: dropping -1 from x^2 - 1 made `Lt` empty instead
/// of `(-1, 1)`, a nonexistent conflict and potentially wrong UNSAT that no
/// SAT-side model gate could catch. The oracle always supplies z3's complete
/// list, so this regression needs a focused unit test.
#[test]
fn from_sign_condition_refuses_an_incomplete_or_padded_root_list() {
    // p = x^2 - 1, real roots -1 and 1.
    let p = vec![BigInt::from(-1), BigInt::zero(), BigInt::from(1)];
    let mk = |lo: i64, hi: i64| -> Anum {
        let bi = BqInterval::new(
            Bq::from_int(BigInt::from(lo)),
            Bq::from_int(BigInt::from(hi)),
        )
        .expect("bracket is ordered");
        Anum::from_poly_interval(&p, &bi).expect("isolates exactly one root")
    };
    let m1 = mk(-2, 0);
    let p1 = mk(0, 2);

    // Complete and ascending: accepted, and the answer is the true (-1, 1).
    let full = from_sign_condition(&p, &[m1.clone(), p1.clone()], SignCond::Lt, Just::none())
        .expect("the complete list must be accepted");
    assert!(
        !full.is_empty(),
        "x^2-1 < 0 is the non-empty interval (-1, 1)"
    );

    // A DROPPED root must be refused, not silently answered.
    assert!(
        from_sign_condition(&p, std::slice::from_ref(&p1), SignCond::Lt, Just::none()).is_none(),
        "an incomplete root list must be REFUSED: answering here returns the empty \
         set for a genuinely non-empty feasible set, which is a wrong conflict"
    );
    assert!(
        from_sign_condition(&p, std::slice::from_ref(&m1), SignCond::Lt, Just::none()).is_none(),
        "dropping the other root must be refused too"
    );

    // A PADDED list — an extra value that is not a root of p — must be refused.
    // 0 is not a root of x^2 - 1.
    let qq = vec![BigInt::zero(), BigInt::from(1)]; // x, root 0
    let zero = {
        let bi = BqInterval::new(
            Bq::from_int(BigInt::from(-1)),
            Bq::from_int(BigInt::from(1)),
        )
        .expect("bracket is ordered");
        Anum::from_poly_interval(&qq, &bi).expect("x has one root in (-1, 1)")
    };
    assert!(
        from_sign_condition(&p, &[m1, zero, p1], SignCond::Lt, Just::none()).is_none(),
        "a non-root in the list must be REFUSED"
    );
}
