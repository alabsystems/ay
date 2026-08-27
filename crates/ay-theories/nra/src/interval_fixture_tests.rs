// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded semantic invariants retained from the former measurement fixtures.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::anum::Anum;
use crate::ialg::{AEnd, AInterval, DecidedInterval, IntervalSet, Just};
use crate::mpbq::{Bq, BqInterval};

fn rational(value: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(value)))
}

fn closed_interval(lo: i64, hi: i64) -> AInterval {
    DecidedInterval::from_bounds(
        AEnd::Fin(rational(lo)),
        false,
        AEnd::Fin(rational(hi)),
        false,
        Just::none(),
    )
    .expect("rational endpoints are comparable")
    .into_interval()
    .expect("fixture interval must be non-empty")
}

fn generated_fixture(count: usize) -> Vec<AInterval> {
    (0..count)
        .map(|index| {
            let base = i64::try_from(index).expect("small fixture index") * 4;
            closed_interval(base, base + 2)
        })
        .collect()
}

#[test]
fn generated_fixture_preserves_cardinality_and_disjointness() {
    const COUNT: usize = 7;
    let set = IntervalSet::normalize(generated_fixture(COUNT)).expect("fixture normalizes");

    assert_eq!(set.len(), COUNT);
    for adjacent in set.intervals().windows(2) {
        assert_eq!(
            adjacent[0].hi().cmp_value(adjacent[1].lo()),
            Some(Ordering::Less),
            "generated intervals must have a certified gap"
        );
    }
    for index in 0..COUNT {
        let midpoint = i64::try_from(index).expect("small fixture index") * 4 + 1;
        assert_eq!(set.contains(&rational(midpoint)), Some(true));
    }
}

#[test]
fn normalization_is_permutation_invariant_by_exact_set_equality() {
    let fixture = generated_fixture(7);
    let ordered = IntervalSet::normalize(fixture.clone()).expect("ordered fixture normalizes");
    let permutation = [4usize, 1, 6, 0, 5, 2, 3];
    let permuted = permutation
        .into_iter()
        .map(|index| fixture[index].clone())
        .collect();
    let normalized = IntervalSet::normalize(permuted).expect("permuted fixture normalizes");

    assert_eq!(ordered.same_set_as(&normalized), Some(true));
}

#[test]
fn low_bit_close_roots_have_certified_order_and_sign() {
    // sqrt(2) and sqrt(2 + 1/64) share the small dyadic bracket (1, 2).
    // Their defining polynomials differ by exactly one at sqrt(2), providing
    // an independent exact sign certificate for the comparison.
    let bracket = BqInterval::new(Bq::from_int(BigInt::from(1)), Bq::from_int(BigInt::from(2)))
        .expect("ordered bracket");
    let lower_poly = vec![BigInt::from(-2), BigInt::from(0), BigInt::from(1)];
    let upper_poly = vec![BigInt::from(-129), BigInt::from(0), BigInt::from(64)];
    let lower = Anum::from_poly_interval(&lower_poly, &bracket).expect("sqrt(2) is isolated");
    let upper = Anum::from_poly_interval(&upper_poly, &bracket).expect("nearby root is isolated");

    assert_eq!(lower.cmp_anum(&upper), Some(Ordering::Less));
    assert_eq!(upper.cmp_anum(&lower), Some(Ordering::Greater));
    assert_eq!(lower.sign_of_poly(&upper_poly), Some(-1));
    assert_eq!(upper.sign_of_poly(&lower_poly), Some(1));
}
