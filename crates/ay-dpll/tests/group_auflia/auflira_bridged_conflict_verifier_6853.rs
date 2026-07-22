// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for the int<->real-bridged conflict semantic-verification
//! false positive (#6853 completeness).
//!
//! The AUFLIRA theory derives VALID conflicts that couple an Int variable `k`
//! with `to_real(k)` (via the incremental bound-axiom injection, #6579). When
//! such a conflict's Farkas certificate fails structural verification, the
//! release backstop re-solves the conflict literals with a fresh
//! `TheoryCombiner` — but every combiner interprets a SINGLE numeric sort
//! (UF+LIA or UF+LRA) and leaves the `to_real` coupling uninterpreted, so it
//! wrongly reported the valid conflict `Sat`, and the hard
//! `ConflictIsSat -> Unknown` gate degraded a decidable linear mixed
//! int/real query to `unknown`.
//!
//! Regressed in the 2026-06-14 merge `fa8599a573` (bisected: both parents
//! solve `unsat`, the merge solves `unknown`); surfaced downstream as
//! deductive-checks's `archimedean_nat` (Verus real.rs port) flipping
//! verified -> incompleteness-Unknown. Fixed by scoping the semantic
//! re-verification to fragments the fresh verifiers are faithful for:
//! mixed int/real (LIRA-bridged) conflicts skip the re-check, mirroring the
//! nonlinear skip (#7978).

use ntest::timeout;

/// Ground core of the archimedean_nat obligation: the negated existential is
/// instantiated at `k+1`. Purely linear mixed int/real reasoning:
/// from `x >= 0` and `x < to_real(k+1)` follows `k+1 >= 1`, so the
/// instantiated disjunct `k+1 <= -1` is impossible, and the other disjunct
/// `f(k+1) < x` contradicts `x < f(k+1)` (with `f(k+1) = to_real(k+1)`).
#[test]
#[timeout(60_000)]
fn test_bridged_valid_conflict_ground_unsat_6853() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f (Int) Real)
        (declare-const x Real)
        (declare-const k Int)
        (assert (<= 0.0 x))
        (assert (<= (to_real k) x))
        (assert (< x (to_real (+ k 1))))
        (assert (< x (f (+ k 1))))
        (assert (or (< (f (+ k 1)) x) (not (<= 0 (+ k 1)))))
        (assert (= (to_real (+ k 1)) (f (+ k 1))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Full quantified archimedean_nat obligation shape (deductive-checks real.rs #2778):
/// `f` is definitionally `to_real` (universally quantified), the negated
/// postcondition is `forall n:nat. f(n) < x`, and the forwarded body assert
/// provides the witness `x < f(k+1)`. E-matching instantiates the negated
/// postcondition at the existing ground term `k+1`; the resulting conflict is
/// the bridged linear conflict above. Must be `unsat` WITHOUT any nonlinear
/// machinery.
#[test]
#[timeout(60_000)]
fn test_archimedean_nat_obligation_unsat_6853() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun nat_to_real (Int) Real)
        (declare-const x Real)
        (declare-const a Int)
        (declare-const inv Int)
        (declare-const n0 Int)
        (assert (<= 0 n0))
        (assert (<= 0.0 x))
        (assert (forall ((m Int)) (= (nat_to_real m) (to_real m))))
        (assert (<= (to_real a) x))
        (assert (< x (to_real (+ a 1))))
        (assert (or (not (<= 0.0 x)) (= a a)))
        (assert (or (not (<= 0.0 x)) (<= (to_real a) x)))
        (assert (or (not (<= 0.0 x)) (< x (to_real (+ a 1)))))
        (assert (< x (nat_to_real (+ a 1))))
        (assert (forall ((n Int)) (or (< (nat_to_real n) x) (not (<= 0 n)))))
        (assert (= (nat_to_real n0) (to_real n0)))
        (assert (= (to_real (+ a 1)) (nat_to_real (+ a 1))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Sound-direction control: same ground shape WITHOUT the contradiction
/// (no instantiated negated-goal disjunction) must not become `unsat`.
/// `sat` or `unknown` are both acceptable (model confirmation for the
/// uninterpreted bridge function may be incomplete); `unsat` would be a
/// soundness bug.
#[test]
#[timeout(60_000)]
fn test_bridged_control_not_unsat_6853() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f (Int) Real)
        (declare-const x Real)
        (declare-const k Int)
        (assert (<= 0.0 x))
        (assert (<= (to_real k) x))
        (assert (< x (to_real (+ k 1))))
        (assert (< x (f (+ k 1))))
        (assert (= (to_real (+ k 1)) (f (+ k 1))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 1);
    assert_ne!(outputs[0], "unsat", "control query must not be unsat");
}
