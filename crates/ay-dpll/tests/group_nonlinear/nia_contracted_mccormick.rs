// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #nia-mccormick-contracted-bounds.
//!
//! The refutation pattern (minimized from the QF_NIA VeryMax Farkas
//! certificates, e.g. `Stroeder_15__Choose...terminationG_0`): with
//! `x = y + z`, `y,z >= 0` and `c <= -3`, the inequality
//! `3x - 5y + c*z - 1 > 0` would need `c*z <= -3z` to refute. When the
//! `c <= -3` bound only flows through a compound linear equality
//! (`(= (+ -3 main) 0)` plus `c + main <= 0`), the LRA's stored bound
//! for `c` was the weaker sentinel `c <= 0`, so the McCormick envelope
//! emitted only `c*z <= 0` and the split loop walked `z` to the
//! oscillation guard. The interval contractor (run by bounded
//! enumeration in the same check) does derive `c <= -3`; McCormick now
//! consumes the tighter contracted endpoint, justified by the asserted
//! literals. z3 answers `unsat` for the first three shapes and `sat`
//! for the control.

use ntest::timeout;

fn verdict(smt: &str) -> Option<&'static str> {
    let result = crate::common::solve(smt);
    match crate::common::sat_result(&result) {
        Some("sat") => Some("sat"),
        Some("unsat") => Some("unsat"),
        Some("unknown") => Some("unknown"),
        _ => None,
    }
}

#[test]
#[timeout(10_000)]
fn contracted_bound_refutes_through_compound_equality() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun c () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun main () Int)
(assert (= (+ -3 main) 0))
(assert (<= (+ c main) 0))
(assert (>= x 0))
(assert (>= y 0))
(assert (>= z 0))
(assert (= (+ (* -1 x) y z) 0))
(assert (> (+ (* 3 x) (* -5 y) (* c z) -1) 0))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("unsat"));
}

#[test]
#[timeout(10_000)]
fn contracted_bound_refutes_through_scaled_product_bound() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun c () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun main () Int)
(assert (= a 1))
(assert (= (+ -3 main) 0))
(assert (<= (+ c (* (+ 0 a) main)) 0))
(assert (>= x 0))
(assert (>= y 0))
(assert (>= z 0))
(assert (= (+ (* -1 x) y (* a z)) 0))
(assert (> (+ (* 3 x) (* -5 y) (* c z) -1) 0))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("unsat"));
}

/// The B0 Farkas component of the VeryMax witness at `a = 1`, with the
/// original compound-equality spelling of the global bound.
#[test]
#[timeout(10_000)]
fn contracted_bound_refutes_verymax_b0_component() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun Nl2main_i1 () Int)
(declare-fun Nl2CT1 () Int)
(declare-fun lam2n0 () Int)
(declare-fun lam2n1 () Int)
(declare-fun lam2n2 () Int)
(declare-fun main_i () Int)
(assert (= Nl2main_i1 1))
(assert (and (<= -3 Nl2main_i1) (<= Nl2main_i1 3)))
(assert (and (= (+ -3 main_i) 0) (<= (+ Nl2CT1 (* (+ 0 Nl2main_i1) main_i)) 0) (<= (* -1 main_i) 0)))
(assert (and (>= lam2n0 0) (>= lam2n1 0) (>= lam2n2 0) (> (+ (* 3 lam2n0) (* -5 lam2n1) (* Nl2CT1 lam2n2) -1) 0) (= (+ (* -1 lam2n0) (* 1 lam2n1) (* Nl2main_i1 lam2n2)) 0)))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("unsat"));
}

/// Product-sum threshold (#nia-product-sum-bound): `(6 + c) * v > 1`
/// with `v >= 0` forces `c >= -5`; with `c <= -3` the factor split then
/// enumerates `c`, and every value refutes the B1 component. The
/// linear `6u` and the monomial `c*v` share their variable only
/// through the asserted equality `u = v`.
#[test]
#[timeout(10_000)]
fn product_sum_bound_through_equality_alias() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun c () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun main () Int)
(assert (= (+ -3 main) 0))
(assert (<= (+ c main) 0))
(assert (>= u 0))
(assert (>= v 0))
(assert (= (+ (* -1 u) v) 0))
(assert (> (+ (* 6 u) (* c v) -1) 0))
(assert (>= x 0))
(assert (>= y 0))
(assert (>= z 0))
(assert (= (+ (* -1 x) y z -1) 0))
(assert (> (+ (* 3 x) (* -5 y) (* c z) (* -1 c)) 0))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("unsat"));
}

/// Same threshold with the shared variable syntactically identical.
#[test]
#[timeout(10_000)]
fn product_sum_bound_same_variable() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun c () Int)
(declare-fun v () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun main () Int)
(assert (= (+ -3 main) 0))
(assert (<= (+ c main) 0))
(assert (>= v 0))
(assert (> (+ (* 6 v) (* c v) -1) 0))
(assert (>= x 0))
(assert (>= y 0))
(assert (>= z 0))
(assert (= (+ (* -1 x) y z -1) 0))
(assert (> (+ (* 3 x) (* -5 y) (* c z) (* -1 c)) 0))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("unsat"));
}

/// Offset-alias form (#nia-product-sum-bound): the A1 Farkas
/// component's equality is `u = v - 1` and `c` also appears linearly
/// in the rest; substituting `v = u + 1` cancels the stray `c` term
/// (`l == d`), leaving `(6 + c) * u - 2 > 0`, so the same threshold
/// bounds `c >= -5` and factor split finishes.
#[test]
#[timeout(10_000)]
fn product_sum_bound_through_offset_alias() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun Nl2main_i1 () Int)
(declare-fun Nl2CT1 () Int)
(declare-fun lam1n0 () Int)
(declare-fun lam1n1 () Int)
(declare-fun lam3n0 () Int)
(declare-fun lam3n1 () Int)
(declare-fun lam3n2 () Int)
(declare-fun main_i () Int)
(assert (= Nl2main_i1 1))
(assert (and (<= -3 Nl2main_i1) (<= Nl2main_i1 3)))
(assert (and (= (+ -3 main_i) 0) (<= (+ Nl2CT1 (* (+ 0 Nl2main_i1) main_i)) 0) (<= (* -1 main_i) 0)))
(assert (and (>= lam1n0 0) (>= lam1n1 0) (> (+ (* 6 lam1n0) (* Nl2CT1 lam1n1) (- 1 (+ Nl2CT1 (* Nl2main_i1 3)))) 0) (= (+ (* -1 lam1n0) (* Nl2main_i1 lam1n1) (- (+ 0 (* Nl2main_i1 1)))) 0)))
(assert (and (>= lam3n0 0) (>= lam3n1 0) (>= lam3n2 0) (> (+ (* 3 lam3n0) (* -5 lam3n1) (* Nl2CT1 lam3n2) (- 1 (+ Nl2CT1 (* Nl2main_i1 1)))) 0) (= (+ (* -1 lam3n0) (* 1 lam3n1) (* Nl2main_i1 lam3n2) (- (+ 0 (* Nl2main_i1 1)))) 0)))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("unsat"));
}

/// Sat control for the threshold rule: `(6 + c) * v > 1` alone is
/// satisfiable at c = -3, v = 1; deriving `c >= -5` must not refute it.
#[test]
#[timeout(10_000)]
fn product_sum_bound_sat_control() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun c () Int)
(declare-fun v () Int)
(declare-fun main () Int)
(assert (= (+ -3 main) 0))
(assert (<= (+ c main) 0))
(assert (>= v 0))
(assert (> (+ (* 6 v) (* c v) -1) 0))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("sat"));
}

/// #nia-contract-relevant-atoms: the compound-equality core padded
/// with 70 unrelated nonlinear atoms so the theory sees more than
/// MAX_CONTRACT_ATOMS (64) asserted atoms — the searched-trail shape
/// from VeryMax (103 atoms). Contraction used to return empty above
/// the threshold, so `c` kept only the sentinel bound and the
/// refutation was lost; relevant-atom contraction still derives
/// `c <= -3`. z3 agrees: unsat.
#[test]
#[timeout(10_000)]
fn contract_above_atom_threshold_still_refutes() {
    let mut smt = String::from(
        "(set-logic QF_NIA)\n\
         (declare-fun c () Int)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
         (declare-fun z () Int)\n(declare-fun main () Int)\n",
    );
    for i in 0..70 {
        smt += &format!("(declare-fun d{i} () Int)\n(assert (>= (* d{i} d{i}) 0))\n");
    }
    smt += "(assert (= (+ -3 main) 0))\n(assert (<= (+ c main) 0))\n\
            (assert (>= x 0))\n(assert (>= y 0))\n(assert (>= z 0))\n\
            (assert (= (+ (* -1 x) y z) 0))\n\
            (assert (> (+ (* 3 x) (* -5 y) (* c z) -1) 0))\n(check-sat)\n";
    assert_eq!(verdict(&smt), Some("unsat"));
}

/// Sat control above the atom threshold: the same padding with a
/// satisfiable core (x=y=z=0, c=-3). Guards
/// #nia-contract-empty-refutes against spurious emptiness verdicts
/// in the relevant-filtered mode. z3 agrees: sat.
#[test]
#[timeout(10_000)]
fn contract_above_atom_threshold_sat_control() {
    let mut smt = String::from(
        "(set-logic QF_NIA)\n\
         (declare-fun c () Int)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
         (declare-fun z () Int)\n(declare-fun main () Int)\n",
    );
    for i in 0..70 {
        smt += &format!("(declare-fun d{i} () Int)\n(assert (>= (* d{i} d{i}) 0))\n");
    }
    smt += "(assert (= (+ -3 main) 0))\n(assert (<= (+ c main) 0))\n\
            (assert (>= x 0))\n(assert (>= y 0))\n(assert (>= z 0))\n\
            (assert (= (+ (* -1 x) y z) 0))\n\
            (assert (> (+ (* 3 x) (* -5 y) (* c z) -1) -100))\n(check-sat)\n";
    assert_eq!(verdict(&smt), Some("sat"));
}

/// Sat control: the same derived bound must not over-refute. With
/// `c <= -3` (through the compound equality) and `z >= 1`, `c*z < 0`
/// has the witness c = -3, z = 1.
#[test]
#[timeout(10_000)]
fn contracted_bound_sat_control() {
    let smt = r#"
(set-logic QF_NIA)
(declare-fun c () Int)
(declare-fun z () Int)
(declare-fun main () Int)
(assert (= (+ -3 main) 0))
(assert (<= (+ c main) 0))
(assert (>= z 1))
(assert (< (* c z) 0))
(check-sat)
"#;
    assert_eq!(verdict(smt), Some("sat"));
}
