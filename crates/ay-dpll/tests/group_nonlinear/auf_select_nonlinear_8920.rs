// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for array-select terms feeding nonlinear arithmetic in the
//! combined EUF + NIA / EUF + NRA path (QF_AUFNIA / QF_AUFNRA).
//!
//! Two failure modes were fixed:
//!
//! 1. **wrong-SAT (nested product over a zero select).** With
//!    `(= (select A 1) 0.0)` and
//!    `(= (* (* (select A 1) (select A 1)) (select A 5)) 2.0)` the formula is
//!    UNSAT (`0 * 0 * anything = 0 ≠ 2`), but AY returned SAT: the validation
//!    evaluator returned Unknown for the nested product because the unresolved
//!    `(select A 5)` factor poisoned it, so the strict gate could not observe
//!    that `(= <product> 2.0)` is definitively false. Fixed by a zero
//!    short-circuit in `*` evaluation (`0 * x = 0` for any x), which makes the
//!    product definitively `0`, the assertion `Bool(false)`, and degrades
//!    SAT → Unknown.
//!
//! 2. **debug-build PANIC (N-O non-convergence).** A select term feeding a
//!    nonlinear NIA/NRA atom (or sitting in a `div` divisor) plus an EUF pin
//!    made the EUF↔NIA/NRA interface-equality fixpoint loop oscillate and hit
//!    the iteration cap, firing a `debug_assert!` that panicked the debug build
//!    (release fell through to Unknown). Fixed by replacing the panic with a
//!    graceful break that returns a sound Unknown in both build profiles.
//!
//! The sound verdict for every case below is "never wrong-sat, never
//! wrong-unsat, never panic" — Unknown is an acceptable (fail-closed) outcome.

use crate::common::{sat_result, solve};

/// h1: nested product over a zero select must NOT be reported SAT.
/// True answer is UNSAT (`0 * 0 * x = 0 ≠ 2.0`); Unknown is acceptable.
#[test]
fn auf_nra_nested_product_zero_select_not_sat_8920() {
    let smt = r"
        (set-logic QF_AUFNRA)
        (declare-fun A () (Array Int Real))
        (assert (= (select A 1) 0.0))
        (assert (= (* (* (select A 1) (select A 1)) (select A 5)) 2.0))
        (check-sat)
    ";
    let out = solve(smt);
    let v = sat_result(&out);
    assert_ne!(
        v,
        Some("sat"),
        "0 * 0 * (select A 5) = 0 can never equal 2.0; must not be SAT. Got: {out}"
    );
    assert!(
        matches!(v, Some("unsat") | Some("unknown")),
        "expected unsat or unknown, got: {out}"
    );
}

/// Integer analogue of the zero-select product (single product). UNSAT
/// (`0 * (select A 4) = 0 ≠ 1`); must not be wrong-SAT and must not panic.
#[test]
fn auf_nia_product_zero_select_not_sat_8920() {
    let smt = r"
        (set-logic QF_AUFNIA)
        (declare-fun A () (Array Int Int))
        (assert (= (select A 1) 0))
        (assert (= (* (select A 1) (select A 4)) 1))
        (check-sat)
    ";
    let out = solve(smt);
    let v = sat_result(&out);
    assert_ne!(v, Some("sat"), "0 * x = 0 can never equal 1. Got: {out}");
    assert!(
        matches!(v, Some("unsat") | Some("unknown")),
        "expected unsat or unknown, got: {out}"
    );
}

/// h2: integer select feeding a nonlinear product + EUF pin must not panic
/// (was a debug_assert N-O non-convergence panic). Sound verdict is Unknown
/// or unsat; the key property is the call returns without panicking.
#[test]
fn auf_nia_select_in_product_no_panic_8920() {
    let smt = r"
        (set-logic QF_AUFNIA)
        (declare-fun A () (Array Int Int))
        (assert (= (select A 1) 0))
        (assert (= (* (select A 1) (select A 4)) 1))
        (check-sat)
    ";
    // The assertion is simply that solve() returns (does not panic).
    let out = solve(smt);
    assert!(
        matches!(sat_result(&out), Some("unsat") | Some("unknown")),
        "must terminate with a sound verdict, not panic. Got: {out}"
    );
}

/// h0: integer select in a `div` DIVISOR + EUF pin must not panic (was a
/// debug_assert N-O non-convergence panic). True answer is SAT (div-by-zero is
/// underspecified, so `(div 7 0)` may equal 99); Unknown is acceptable.
#[test]
fn auf_nia_select_in_div_divisor_no_panic_8920() {
    let smt = r"
        (set-logic QF_AUFNIA)
        (declare-fun A () (Array Int Int))
        (declare-fun x () Int)
        (assert (= x (div 7 (select A 0))))
        (assert (= x 99))
        (check-sat)
    ";
    let out = solve(smt);
    assert_ne!(
        sat_result(&out),
        Some("unsat"),
        "div-by-zero is underspecified so this is SAT; must not be wrong-UNSAT. Got: {out}"
    );
    assert!(
        matches!(sat_result(&out), Some("sat") | Some("unknown")),
        "must terminate with a sound verdict, not panic. Got: {out}"
    );
}

/// NRA analogue: select in a nonlinear product divisor-free chain plus an EUF
/// pin that oscillated the EUF↔NRA fixpoint. Must not panic.
#[test]
fn auf_nra_select_in_product_no_panic_8920() {
    let smt = r"
        (set-logic QF_AUFNRA)
        (declare-fun A0 () (Array Int Real))
        (declare-fun v0 () Real)
        (declare-fun v1 () Real)
        (assert (= (select A0 2) (- 2.0)))
        (assert (= (select A0 0) 3.0))
        (assert (= (* v1 v0) 4.0))
        (assert (= (* v0 v0) 0.0))
        (assert (= (* 3.0 (select A0 4)) 2.0))
        (check-sat)
    ";
    let out = solve(smt);
    assert!(
        matches!(
            sat_result(&out),
            Some("sat") | Some("unsat") | Some("unknown")
        ),
        "must terminate with a sound verdict, not panic. Got: {out}"
    );
}

/// Genuine-SAT guard: a zero product that is CONSISTENT must stay SAT — the
/// zero short-circuit must not over-degrade. `(select A 1) = 0` and
/// `(* (select A 1) (select A 4)) = 0` is satisfiable.
#[test]
fn auf_nia_zero_product_consistent_stays_sat_8920() {
    let smt = r"
        (set-logic QF_AUFNIA)
        (declare-fun A () (Array Int Int))
        (assert (= (select A 1) 0))
        (assert (= (* (select A 1) (select A 4)) 0))
        (check-sat)
    ";
    let out = solve(smt);
    assert_eq!(
        sat_result(&out),
        Some("sat"),
        "0 * x = 0 is consistent here; must remain SAT (no over-degradation). Got: {out}"
    );
}

/// Genuine-SAT guard (pure NIA): the zero short-circuit must not break a plain
/// satisfiable nonlinear product.
#[test]
fn nia_product_sat_regression_8920() {
    let smt = r"
        (set-logic QF_NIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (* x y) 6))
        (assert (= x 2))
        (assert (= y 3))
        (check-sat)
    ";
    assert_eq!(sat_result(&solve(smt)), Some("sat"));
}
