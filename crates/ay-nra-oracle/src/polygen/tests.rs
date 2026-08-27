// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for deterministic polynomial generation.

use super::{gen_poly, gen_poly_shaped, render, work_cost, Rng, Shape, ALL_SHAPES};
use num_traits::Zero;

#[test]
fn rng_is_reproducible_from_seed() {
    let a: Vec<u64> = (0..8).map(|_| Rng::new(12345).next_u64()).collect();
    let mut r = Rng::new(12345);
    let b: Vec<u64> = (0..8).map(|_| r.next_u64()).collect();
    // Every fresh Rng(12345) starts the same stream.
    assert_eq!(a[0], b[0]);
    // And the stream itself does not repeat immediately.
    assert_ne!(b[0], b[1]);
}

#[test]
fn same_seed_gives_identical_polynomials() {
    let mut r1 = Rng::new(7);
    let mut r2 = Rng::new(7);
    for _ in 0..64 {
        let p = gen_poly(&mut r1, 8);
        let q = gen_poly(&mut r2, 8);
        assert_eq!(p.coeffs, q.coeffs);
        assert_eq!(p.shape, q.shape);
    }
}

#[test]
fn every_shape_builds_within_reason() {
    let mut rng = Rng::new(99);
    for shape in ALL_SHAPES {
        for _ in 0..32 {
            let p = gen_poly_shaped(&mut rng, shape, 8);
            if shape == Shape::Zero {
                assert!(p.coeffs.is_empty());
            } else {
                assert!(!p.coeffs.is_empty(), "{} produced nothing", shape.name());
            }
            // No trailing zero coefficient survives trimming.
            assert!(!p.coeffs.last().is_some_and(Zero::is_zero));
        }
    }
}

/// Whatever the shapes do internally, `gen_poly` must never hand the
/// driver a polynomial above the requested degree: the work budget and the
/// campaign's throughput both depend on that cap holding.
#[test]
fn gen_poly_never_exceeds_its_degree_cap() {
    for cap in [2usize, 3, 5, 8] {
        let mut rng = Rng::new(1234 + cap as u64);
        for _ in 0..4000 {
            let p = gen_poly(&mut rng, cap);
            assert!(
                p.coeffs.len() <= cap + 1,
                "{} produced degree {} for cap {cap}",
                p.shape.name(),
                p.coeffs.len() - 1
            );
        }
    }
}

#[test]
fn work_cost_separates_the_cheap_band_from_the_expensive_one() {
    let mut rng = Rng::new(4242);
    // A small dense polynomial is cheap; a huge-coefficient one is not.
    let small = gen_poly_shaped(&mut rng, Shape::AlgebraicSmall, 3);
    let huge = gen_poly_shaped(&mut rng, Shape::HugeCoeffs, 4);
    assert!(
        work_cost(&small.coeffs) < work_cost(&huge.coeffs),
        "small {} vs huge {}",
        work_cost(&small.coeffs),
        work_cost(&huge.coeffs)
    );
    // The zero polynomial costs nothing and must not underflow.
    assert_eq!(work_cost(&[]), 0);
}

#[test]
fn render_is_readable() {
    let mut rng = Rng::new(1);
    let p = gen_poly_shaped(&mut rng, Shape::Wilkinson, 4);
    let s = render(&p.coeffs);
    assert!(s.contains('x'), "{s}");
}
