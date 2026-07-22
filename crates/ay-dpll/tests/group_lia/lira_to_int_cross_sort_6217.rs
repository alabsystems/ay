// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6217: LIRA cross-sort split suppression with to_int.
//!
//! Before this fix, `propagate_cross_sort_values` would request integer-style
//! floor/ceil splits on Real-sorted variables (e.g., `x` in `to_int(x)`),
//! creating artificial gaps like `x <= 2 OR x >= 3` that exclude valid Real
//! values (like 2.5), causing false UNSAT.
//!
//! The fix:
//! 1. Filters Real-sorted terms from cross-sort propagation (Int-only)
//! 2. Suppresses cross-sort split requests when to_int terms exist

use ntest::timeout;

/// SAT: The core bug scenario from #6217.
/// `y = to_int(x)` with `x` in a fractional range should be SAT.
/// Before the fix, cross-sort propagation requested `x <= 2 OR x >= 3`
/// which excluded the valid assignment `x = 2.5, y = 2`.
#[test]
#[timeout(30_000)]
fn test_to_int_fractional_range_no_false_unsat_6217() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= y (to_int x)))
        (assert (>= x 2.5))
        (assert (<= x 2.9))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "to_int(x) with x in [2.5, 2.9] must be SAT (y=2). \
         False UNSAT indicates cross-sort splits on Real-sorted vars (#6217)."
    );
}

/// SAT: Multiple to_int terms with fractional Real ranges.
/// Tests that cross-sort split suppression works with multiple to_int pairs.
#[test]
#[timeout(30_000)]
fn test_to_int_multiple_vars_fractional_ranges_sat_6217() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (declare-const a Real)
        (declare-const b Int)
        (assert (= y (to_int x)))
        (assert (= b (to_int a)))
        (assert (>= x 1.3))
        (assert (<= x 1.7))
        (assert (>= a 3.1))
        (assert (<= a 3.9))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "Multiple to_int with fractional ranges must be SAT (y=1, b=3). \
         False UNSAT indicates cross-sort split regression (#6217)."
    );
}

/// SAT: to_int combined with integer arithmetic constraints.
/// The Integer variable y should be constrained by both to_int and explicit bounds.
#[test]
#[timeout(30_000)]
fn test_to_int_with_integer_arithmetic_sat_6217() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= y (to_int x)))
        (assert (>= x 5.5))
        (assert (<= x 5.9))
        (assert (>= y 5))
        (assert (<= y 6))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_int(5.5..5.9) = 5, and y=5 is in [5,6], so SAT.
    assert_eq!(
        outputs[0], "sat",
        "to_int with explicit integer bounds must be SAT (y=5)."
    );
}

/// UNSAT: to_int with genuinely conflicting constraints (not false UNSAT).
/// Ensures the fix doesn't make the solver too permissive.
#[test]
#[timeout(30_000)]
fn test_to_int_genuine_unsat_preserved_6217() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= y (to_int x)))
        (assert (>= x 2.5))
        (assert (<= x 2.9))
        (assert (>= y 3))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // to_int(2.5..2.9) = 2, but y >= 3 requires y >= 3. Genuine UNSAT.
    assert_eq!(
        outputs[0], "unsat",
        "to_int(x) = 2 with y >= 3 must be UNSAT (genuine conflict)."
    );
}

/// SAT: to_int at integer boundary (x = 3.0 exactly).
/// Edge case: when x is exactly an integer, to_int(x) = x.
#[test]
#[timeout(30_000)]
fn test_to_int_at_integer_boundary_sat_6217() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= y (to_int x)))
        (assert (= x 3.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat", "to_int(3.0) = 3 should be SAT.");
}

/// SAT: to_real(to_int(x)) model validation (#6227).
/// When z = to_real(y) and y = to_int(x), the model must have z = to_real(floor(x)).
/// Before the fix, the LRA model patched to_int(x) to floor(x) but did not
/// propagate the patch through tableau rows to z, leaving z at the raw simplex
/// value (which differs from floor(x) when x is non-integer).
#[test]
#[timeout(30_000)]
fn test_to_real_to_int_model_validation_6227() {
    let smt = r#"
        (set-logic QF_LIRA)
        (set-option :produce-models true)
        (declare-const x Real)
        (declare-const y Int)
        (declare-const z Real)
        (assert (= y (to_int x)))
        (assert (= z (to_real y)))
        (assert (>= x 4.2))
        (assert (<= x 4.8))
        (assert (<= z 5.0))
        (check-sat)
        (get-model)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "to_real(to_int(x)) with x in [4.2, 4.8] must be SAT. \
         Expected: y=4, z=4.0. Z3 confirms SAT."
    );
    // Verify model contains z = 4.0 (or equivalent rational for floor(4.2..4.8) = 4).
    // The model should have y = 4 and z = 4.0 since z = to_real(to_int(x)) = to_real(4) = 4.0.
    let model = &outputs[1];
    assert!(
        model.contains("define-fun z"),
        "Model should define z. Got: {model}"
    );
    // z must be 4.0 (or "4" as rational). Check that it's not a fractional value like 4.2.
    // The exact format may be "(/ 4 1)" or "4.0" or "4" depending on output formatting.
    assert!(
        !model.contains("4.2") && !model.contains("4.8"),
        "z should be 4.0 (floor), not the raw simplex value. Got: {model}"
    );
}

/// SAT: Independent variable with same value as to_int pre-patch (#6227 audit).
/// w is independently set to 37/10 (same as to_int(x)'s raw simplex value).
/// The fix must NOT patch w — only structurally connected variables should
/// be updated. The old value-based propagation would incorrectly change
/// w from 3.7 to 4 because it matched the BigRational value instead of
/// tracing through asserted equality atoms.
#[test]
#[timeout(30_000)]
fn test_to_int_no_false_positive_value_matching_6227() {
    let smt = r#"
        (set-logic QF_LIRA)
        (set-option :produce-models true)
        (declare-const x Real)
        (declare-const w Real)
        (assert (> (to_real (to_int x)) 3.0))
        (assert (>= x 4.2))
        (assert (<= x 4.8))
        (assert (= w (/ 37 10)))
        (check-sat)
        (get-model)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat", "Should be SAT.");
    let model = &outputs[1];
    // w must be 37/10 = 3.7, not 4. If w is patched to 4 that's the false positive.
    assert!(
        model.contains("37") || model.contains("3.7"),
        "w should be 37/10 (3.7), not patched to 4. Got: {model}"
    );
}

/// SAT: Direct LRA path — to_real(to_int(x)) equality propagation (#6227 audit).
/// w = to_real(to_int(x)) within LRA (no LIRA routing, all Real-sorted).
/// The asserted-atom-based propagation in extract_model must find
/// the equality atom and compute w = floor(x).
#[test]
#[timeout(30_000)]
fn test_to_int_direct_lra_equality_propagation_6227() {
    let smt = r#"
        (set-logic QF_LIRA)
        (set-option :produce-models true)
        (declare-const x Real)
        (declare-const w Real)
        (assert (> (to_real (to_int x)) 3.0))
        (assert (>= x 4.2))
        (assert (<= x 4.8))
        (assert (= w (to_real (to_int x))))
        (check-sat)
        (get-model)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat", "Should be SAT.");
    let model = &outputs[1];
    // w should be 4.0 (= to_real(to_int(4.2)) = to_real(4) = 4.0)
    assert!(
        model.contains("define-fun w"),
        "Model should define w. Got: {model}"
    );
    assert!(
        !model.contains("4.2") && !model.contains("4.8"),
        "w should be 4.0 (floor), not the raw simplex value. Got: {model}"
    );
}

/// SAT: Nested to_real(to_int(x)) with additional Real constraints (#6227).
/// z = to_real(to_int(x)) AND w = z + 1.0 should produce consistent model.
#[test]
#[timeout(30_000)]
fn test_to_real_to_int_chained_real_constraints_6227() {
    let smt = r#"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (declare-const y Int)
        (declare-const z Real)
        (assert (= y (to_int x)))
        (assert (= z (to_real y)))
        (assert (>= x 2.5))
        (assert (<= x 2.9))
        (assert (>= z 0.0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "to_real(to_int(x)) with x in [2.5, 2.9] must be SAT (z=2.0)."
    );
}
