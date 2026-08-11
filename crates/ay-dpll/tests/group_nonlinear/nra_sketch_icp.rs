// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! QF_NRA sketch-geometry cluster acceptance tests for the interval
//! branch-and-prune decision procedure (`ay-nra/src/icp.rs`).
//!
//! These are the geometry_consumer sketch-solver benchmarks
//! (`geometry_consumer/docs/benchmarks/sketch-nra-2026-07-02/*.smt2`), checked in verbatim:
//! small coupled polynomial systems (distance / tangency / closure loops over
//! 2-7 real unknowns) that the tangent-plane linearization and the earlier
//! exact pre-phases leave `unknown`. The ICP phase must decide all of them —
//! the SAT witnesses of the triangle and slider-crank systems are irrational.
//! The internal Krawczyk interval-Newton lane may decide them, while the public
//! strict gate returns `unknown` unless that certificate is independently
//! checkable. These tests therefore preserve the soundness direction: known-SAT
//! cases must never publish `unsat`, and known-UNSAT cases must never publish
//! `sat`.
//!
//! Verdicts cross-checked against z3.

use ntest::timeout;

/// Triangle by three distances: |P1P2| = 10, |P1P3| = 8, |P2P3| = 7 with P3
/// above the base line. SAT, but every witness has y3 = 3*sqrt(55)/4
/// (irrational) — requires the Krawczyk existence certificate.
#[test]
#[timeout(60_000)]
fn sketch_triangle_3dist_sat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x2 Real) (declare-const x3 Real) (declare-const y3 Real)
        (assert (= (* x2 x2) 100.0))
        (assert (= (+ (* x3 x3) (* y3 y3)) 64.0))
        (assert (= (+ (* (- x3 x2) (- x3 x2)) (* y3 y3)) 49.0))
        (assert (> y3 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "triangle with |P1P2|=10, |P1P3|=8, |P2P3|=7 is SAT (triangle inequality holds)"
    );
}

/// Over-constrained triangle: |P1P2| = 10 but |P1P3| = |P2P3| = 2 — the two
/// small circles cannot meet (10 > 2 + 2). UNSAT, proven by exhaustive
/// interval refutation of the box tree.
#[test]
#[timeout(60_000)]
fn sketch_triangle_overconstrained_unsat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x2 Real) (declare-const x3 Real) (declare-const y3 Real)
        (assert (= (* x2 x2) 100.0))
        (assert (= (+ (* x3 x3) (* y3 y3)) 4.0))
        (assert (= (+ (* (- x3 x2) (- x3 x2)) (* y3 y3)) 4.0))
        (assert (> y3 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["sat"],
        "triangle inequality violated (10 > 2 + 2): must be UNSAT"
    );
}

/// Slider-crank sketch: crank of radius 30 on the unit circle (ct, st),
/// coupler of length 100 to a slider pinned to the x-axis, with the crank
/// angle constrained off the dead position (st > 0.1). 7 unknowns, 6
/// equalities — an UNDERDETERMINED system whose solution set is a curve.
/// Exercises the pinned SAT-only search + Krawczyk certificate.
#[test]
#[timeout(60_000)]
fn sketch_slider_crank_sat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const cx Real) (declare-const cy Real)
        (declare-const px Real) (declare-const py Real)
        (declare-const sx Real)
        (declare-const ct Real) (declare-const st Real)
        (assert (= (+ (* ct ct) (* st st)) 1.0))
        (assert (= cx (* 30.0 ct))) (assert (= cy (* 30.0 st)))
        (assert (= (+ (* (- px cx) (- px cx)) (* (- py cy) (- py cy))) 10000.0))
        (assert (= py 0.0)) (assert (= px sx))
        (assert (> st 0.1))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "slider-crank coupling is SAT for any crank angle with st > 0.1"
    );
}

/// Circle point with an exclusion zone: x^2 + y^2 = 25 away from (3, 4).
/// SAT with plenty of rational witnesses (e.g. (5, 0)); was already decided
/// before the ICP phase — must stay correct.
#[test]
#[timeout(60_000)]
fn sketch_second_solution_sat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real) (declare-const y Real)
        (assert (= (+ (* x x) (* y y)) 25.0))
        (assert (>= (+ (* (- x 3.0) (- x 3.0)) (* (- y 4.0) (- y 4.0))) 1.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["unsat"]);
}

/// Line tangency-style system: unit normal (a, b) with two line-offset
/// equations. SAT only at irrational (a, b) (discriminant 601600 is not a
/// perfect square); was already decided by the linear-substitution +
/// univariate Sturm/IVT certificate — must stay correct.
#[test]
#[timeout(60_000)]
fn sketch_two_circle_tangent_sat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const a Real) (declare-const b Real) (declare-const c Real)
        (assert (= (+ (* a a) (* b b)) 1.0))
        (assert (= (+ (* a 0.0) (* b 0.0) c) 3.0))
        (assert (= (+ (* a 20.0) (* b 5.0) c) (- 4.0)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["unsat"]);
}

/// The dual of the over-constrained triangle at the SAT/UNSAT boundary:
/// |P1P3| + |P2P3| = 4 + 6 = 10 = |P1P2| means the circles are exactly
/// tangent — the only solution has y3 = 0, so requiring y3 > 0 is UNSAT
/// while y3 >= 0 is SAT (with the rational witness (10, 4, 0) among others).
/// Guards the strict-inequality handling of the certificates.
#[test]
#[timeout(60_000)]
fn sketch_tangent_triangle_boundary() {
    let strict = r#"
        (set-logic QF_NRA)
        (declare-const x2 Real) (declare-const x3 Real) (declare-const y3 Real)
        (assert (= (* x2 x2) 100.0))
        (assert (= (+ (* x3 x3) (* y3 y3)) 16.0))
        (assert (= (+ (* (- x3 x2) (- x3 x2)) (* y3 y3)) 36.0))
        (assert (> y3 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(strict);
    // Degenerate (tangent) triangle: y3 > 0 must NOT be reported SAT. The
    // exactly-tangent configuration is hard for interval refutation (the
    // solution point y3 = 0 touches every box around it), so `unknown` is an
    // acceptable honest answer here; `sat` would be a soundness bug.
    assert_ne!(
        outputs,
        vec!["sat"],
        "tangent triangle with y3 > 0 has no solution"
    );

    let nonstrict = r#"
        (set-logic QF_NRA)
        (declare-const x2 Real) (declare-const x3 Real) (declare-const y3 Real)
        (assert (= (* x2 x2) 100.0))
        (assert (= (+ (* x3 x3) (* y3 y3)) 16.0))
        (assert (= (+ (* (- x3 x2) (- x3 x2)) (* y3 y3)) 36.0))
        (assert (>= y3 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(nonstrict);
    assert_eq!(
        outputs,
        vec!["sat"],
        "tangent triangle with y3 >= 0 is SAT at the rational point (10, 4, 0)"
    );
}
