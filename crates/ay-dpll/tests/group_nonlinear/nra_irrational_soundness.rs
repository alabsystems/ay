// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! NRA irrational solution soundness tests.
//!
//! The NRA solver uses incremental linearization (tangent planes, McCormick
//! envelopes, sign lemmas) to approximate nonlinear constraints in LRA.
//! When a formula has irrational solutions (e.g., x^2 = 2 → x = ±√2),
//! the linear relaxation cannot represent the exact solution. The solver
//! must NOT return UNSAT for satisfiable formulas with irrational witnesses.
//!
//! Extends the #5959 regression test (x^2 = 2) to cover more irrational
//! cases: different non-perfect-square values, higher degrees, and
//! multi-variable constraints.

use ntest::timeout;

/// x^2 = 3 has solutions x = ±√3. Must NOT return UNSAT.
#[test]
#[timeout(30_000)]
fn nra_irrational_x_sq_eq_3() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) 3.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "x^2 = 3 is SAT (x = ±√3), must not return UNSAT"
    );
}

/// x^2 = 5 has solutions x = ±√5. Must NOT return UNSAT.
#[test]
#[timeout(30_000)]
fn nra_irrational_x_sq_eq_5() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) 5.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "x^2 = 5 is SAT (x = ±√5), must not return UNSAT"
    );
}

/// x^2 = 7 has solutions x = ±√7. Must NOT return UNSAT.
#[test]
#[timeout(30_000)]
fn nra_irrational_x_sq_eq_7() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) 7.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "x^2 = 7 is SAT (x = ±√7), must not return UNSAT"
    );
}

/// x^2 = 4 has rational solutions x = ±2. Should return SAT.
#[test]
#[timeout(30_000)]
fn nra_rational_x_sq_eq_4_sat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) 4.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "x^2 = 4 is SAT (x = ±2), must not return UNSAT"
    );
}

/// x^2 = -1 has no real solutions. Returning `unknown` is sound for the
/// public nonlinear gate; returning `sat` would be unsound.
#[test]
#[timeout(30_000)]
fn nra_unsat_x_sq_eq_neg1() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) (- 1.0)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["sat"], "x^2 = -1 has no real solutions");
}

/// x^2 = -0.001 has no real solutions. Returning `unknown` is sound for the
/// public nonlinear gate; returning `sat` would be unsound.
#[test]
#[timeout(30_000)]
fn nra_unsat_x_sq_eq_small_negative() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (= (* x x) (- 0.001)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["sat"], "x^2 = -0.001 has no real solutions");
}

/// x^2 + y^2 = 1 is the unit circle — satisfiable (e.g., x=0, y=1).
/// Tests multi-variable nonlinear with rational witness.
#[test]
#[timeout(30_000)]
fn nra_unit_circle_sat() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (+ (* x x) (* y y)) 1.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["unsat"], "x^2 + y^2 = 1 is SAT (unit circle)");
}

/// x^2 + y^2 = -1 is unsatisfiable (sum of squares is always >= 0).
/// NRA may return `unknown` for multi-variable nonlinear equalities with
/// negative RHS since the sum-of-squares lemma requires combining
/// even-power non-negativity across multiple monomials. Both `unsat` and
/// `unknown` are sound; `sat` would be a bug.
#[test]
#[timeout(30_000)]
fn nra_unsat_negative_sum_of_squares() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (+ (* x x) (* y y)) (- 1.0)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["sat"],
        "x^2 + y^2 = -1 has no real solutions — must not return SAT"
    );
}

/// x > 0 AND x^2 = 2 forces x = √2 (positive root only). Must NOT return UNSAT.
#[test]
#[timeout(30_000)]
fn nra_irrational_positive_root_only() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (= (* x x) 2.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["unsat"], "x > 0 AND x^2 = 2 is SAT (x = √2)");
}

/// x > 0 AND x^2 < 0 is unsatisfiable. Strict publication may return
/// `unknown` until the nonlinear refutation has independent proof authority.
#[test]
#[timeout(30_000)]
fn nra_unsat_positive_x_negative_square() {
    let smt = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< (* x x) 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_ne!(outputs, vec!["sat"], "x > 0 AND x^2 < 0 is UNSAT");
}
