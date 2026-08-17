// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::model::Model;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

/// Miniature: maximize x0+x1+x2 st x0+x1+x2 <= 2; center (1,0,0) value 1.
/// An improving point at distance 1 exists ((1,1,0), value 2); the search
/// must find SOME improving point within radius 2.
#[test]
fn cdcl_ball_finds_known_improvement() {
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    let c = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 2.0, &[(a, 1.0), (b, 1.0), (c, 1.0)]);
    m.set_objective(&[(a, 1.0), (b, 1.0), (c, 1.0)], Sense::Maximize);
    let ints = vec![0usize, 1, 2];
    let center = vec![rat(1), rat(0), rat(0)];
    let got = ball_propagation_search(&m, &ints, &center, 2.0, None, 1_000_000)
        .expect("an improving point exists at distance 1");
    let val: i64 = (0..3).map(|j| if got[j] == rat(1) { 1 } else { 0 }).sum();
    assert_eq!(val, 2, "must land on a sum-2 point");
}

/// A general-integer column rides through the feasibility jump FROZEN AT ITS START
/// VALUE — the regression pinned here is the harvest that binarized it (`x > 0.5` -> 1),
/// which made every exact check see a point the float walk never visited: on gt2 that
/// was 41,000 rejected harvests, 1.4s, and a 29x wall regression. Minimize `-x - y`
/// under `x + y + g >= 4` with `g` integer in `[0, 5]` starting at 3: the walk only
/// needs one binary flip, and the returned point must carry `g = 3`, not `g = 1`.
#[test]
fn feasibility_jump_keeps_frozen_general_integers_at_their_start_value() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    let g = m.add_int_col(0.0, 5.0);
    m.add_row(4.0, f64::INFINITY, &[(x, 1.0), (y, 1.0), (g, 1.0)]);
    m.set_objective(&[(x, -1.0), (y, -1.0)], Sense::Minimize);
    let ints = vec![0usize, 1, 2];
    let start = vec![rat(0), rat(0), rat(3)];
    let (lo, up) = ([0.0, 0.0, 0.0], [1.0, 1.0, 5.0]);
    let got = feasibility_jump(&m, &ints, &start, &lo, &up, &rat(0), 1, 10_000, None)
        .expect("one binary flip mends the row and beats the incumbent");
    assert_eq!(
        got[2],
        rat(3),
        "frozen general integer must keep its start value"
    );
    assert!(
        m.check_point(&got).is_ok(),
        "harvested point must be exactly feasible"
    );
    assert!(
        got[0] == rat(1) || got[1] == rat(1),
        "a binary flip carried the repair"
    );
}

/// The regime guard: a model whose integer columns are MOSTLY general-integer is out
/// of the binary sampler's regime (the walk would search with its hands tied — gt2
/// burned 0.04s per pass, every pass, finding nothing). It must decline immediately.
#[test]
fn feasibility_jump_declines_general_integer_majority_models() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let g = m.add_int_col(0.0, 5.0);
    let h = m.add_int_col(0.0, 5.0);
    m.add_row(f64::NEG_INFINITY, 6.0, &[(x, 1.0), (g, 1.0), (h, 1.0)]);
    m.set_objective(&[(x, -1.0)], Sense::Minimize);
    let ints = vec![0usize, 1, 2];
    let start = vec![rat(0), rat(1), rat(1)];
    let (lo, up) = ([0.0, 0.0, 0.0], [1.0, 5.0, 5.0]);
    assert!(
        feasibility_jump(&m, &ints, &start, &lo, &up, &rat(0), 1, 10_000, None).is_none(),
        "1 binary among 3 ints is out of regime — decline, do not wander"
    );
}

/// Same model, but the center is already optimal within the ball
/// (radius 0): must prove barren, not wander.
#[test]
fn cdcl_ball_barren_terminates() {
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
    m.set_objective(&[(a, 1.0), (b, 1.0)], Sense::Maximize);
    let ints = vec![0usize, 1];
    let center = vec![rat(1), rat(0)];
    assert!(
        ball_propagation_search(&m, &ints, &center, 0.0, None, 1_000_000).is_none(),
        "radius 0 around an optimum must be barren"
    );
}

/// Mixed signs and a forcing chain: maximize 3a+2b+c st a+b <= 1,
/// -a + c <= 0 (c requires a). Center (0,1,0) value 2; optimum (1,0,1)
/// value 4 at distance 3.
#[test]
fn cdcl_ball_crosses_a_swap() {
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    let c = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(a, -1.0), (c, 1.0)]);
    m.set_objective(&[(a, 3.0), (b, 2.0), (c, 1.0)], Sense::Maximize);
    let ints = vec![0usize, 1, 2];
    let center = vec![rat(0), rat(1), rat(0)];
    let got = ball_propagation_search(&m, &ints, &center, 3.0, None, 1_000_000)
        .expect("(1,0,1) improves at distance 3");
    assert_eq!(got[0], rat(1));
    assert_eq!(got[1], rat(0));
    assert_eq!(got[2], rat(1));
}
