// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Integrality of Int variables occurring ONLY under `to_real`
//! (#to-real-only-int-integrality).
//!
//! An Int variable that appears in no Int-side literal never registers with
//! LIA, so `propagate_cross_sort_values` (which iterates LIA's `term_to_var`)
//! never saw it. LRA then pinned the shared TermId to a non-integral value
//! (e.g. `(= (to_real xi) (/ 7 2))` pinned `xi = 7/2`), the LIRA fixpoint
//! returned SAT with an invalid model, and the model-validation gate honestly
//! degraded the answer to `unknown` — sound but incomplete.
//!
//! The fix has three parts (all in `combined_solvers/adapters/lira/`):
//! 1. At fixpoint, scan LRA's model for Int-sorted asserted-real terms holding
//!    non-integral values and request the existing cross-sort branch-and-bound
//!    split (`x <= floor(v) OR x >= ceil(v)`), so DPLL either integralizes the
//!    variable or flips the offending Real literal.
//! 2. Forward single-variable Int bound literals (including the split atoms
//!    from part 1, which route to LIA) to LRA when their subject is
//!    Real-shared, so LRA's model actually respects them — LIA can solve pure
//!    bound boxes without materializing simplex state, leaving the cross-sort
//!    value bridge blind.
//! 3. Fingerprint bounds-only cross-sort forwarding so tightened (but still
//!    non-tight) LIA bounds re-forward instead of being deduplicated away.

use ntest::timeout;

/// UNSAT: to_real(xi) = 3.5 has no integer solution. Previously `unknown`.
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_eq_half_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun xi () Int)
        (assert (= (to_real xi) (/ 7 2)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "no integer xi has to_real(xi) = 3.5"
    );
}

/// UNSAT: negative non-integral target. Exercises the floor/ceil bracketing
/// for negative values (floor(-7/2) = -4, not truncation to -3).
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_eq_negative_half_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun xi () Int)
        (assert (= (to_real xi) (/ -7 2)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "no integer xi has to_real(xi) = -3.5"
    );
}

/// UNSAT: open interval (3, 4) contains no integer, and xi occurs only under
/// to_real. LRA alone is satisfiable (e.g. 7/2), so the integrality split
/// must drive both branches to conflict.
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_open_unit_interval_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun xi () Int)
        (assert (> (to_real xi) 3.0))
        (assert (< (to_real xi) 4.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "no integer lies strictly in (3, 4)");
}

/// SAT: same shape but the interval (3, 5) contains the integer 4.
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_wider_interval_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun xi () Int)
        (assert (> (to_real xi) 3.0))
        (assert (< (to_real xi) 5.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "xi = 4 satisfies 3 < xi < 5");
}

/// SAT: the offending equality sits on the dead branch of an ite, so the SAT
/// core can flip it. Mirrors bindings/python
/// test_coercion_model.py::test_mixed_if_result_sort_and_solve, which lowered
/// If(b, xi, yr) == 3.5 to this shape and previously answered `unknown` when
/// the SAT core speculatively asserted the dead-branch literal.
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_dead_ite_branch_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun b () Bool)
        (declare-fun yr () Real)
        (declare-fun xi () Int)
        (assert (ite b (= (to_real xi) (/ 7 2)) (= yr (/ 7 2))))
        (assert (not b))
        (assert (= yr (/ 7 2)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "b = false, yr = 7/2, xi arbitrary");
}

/// UNSAT: both ite branches force a non-integral to_real-only Int value.
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_both_ite_branches_unsat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun b () Bool)
        (declare-fun xi () Int)
        (assert (ite b (= (to_real xi) (/ 7 2)) (= (to_real xi) (/ 9 2))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "neither 3.5 nor 4.5 is an integer value for xi"
    );
}

/// SAT: integral target — the fast path must not regress. xi occurs only
/// under to_real and the value 4.0 is integral, so no split is needed.
#[test]
#[timeout(60_000)]
fn test_to_real_only_int_integral_target_sat() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-fun xi () Int)
        (assert (= (to_real xi) 4.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "xi = 4 satisfies to_real(xi) = 4.0");
}
