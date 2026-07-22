// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for EUF disequality propagation orientation (#6152).
//!
//! The EUF solver must correctly match disequality orientations when propagating
//! equalities as false. When (a != b) is asserted and a later equality (= c d)
//! has c in the same class as b and d in the same class as a (swapped orientation),
//! the solver must swap the match to produce correct explanations.
//!
//! Finding 1 from #6152: the orientation guard is a debug_assert that is compiled
//! out in release mode. These tests verify the propagation path works in both modes.

use ntest::timeout;

/// Test EUF disequality propagation with direct orientation.
/// distinct(a,b), a=c, b=d implies (= c d) = false.
#[test]
#[timeout(10_000)]
fn test_euf_diseq_propagation_direct_orientation_6152() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
; a != b
(assert (distinct a b))
; a = c
(assert (= a c))
; b = d
(assert (= b d))
; c = d would contradict a != b via transitivity
(assert (= c d))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    // a=c, b=d, a!=b => c!=d. But (= c d) asserted => UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Test EUF disequality propagation with swapped orientation.
/// distinct(a,b), b=c, a=d implies (= c d) = false.
/// Here the disequality pair (a,b) matches the equality (c,d) in swapped order:
/// c is in class of b (not a), and d is in class of a (not b).
#[test]
#[timeout(10_000)]
fn test_euf_diseq_propagation_swapped_orientation_6152() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
; a != b
(assert (distinct a b))
; b = c (so c is in class of b)
(assert (= b c))
; a = d (so d is in class of a)
(assert (= a d))
; c = d would contradict a != b via transitivity
; This forces the swapped orientation path in EUF propagation
(assert (= c d))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    // b=c, a=d, a!=b => c!=d (swapped). But (= c d) asserted => UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}

/// Test with function congruence + disequality propagation.
/// f(a) != f(b), a = c, b = d. Then f(c) = f(d) should be false by congruence.
#[test]
#[timeout(10_000)]
fn test_euf_diseq_with_congruence_6152() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (distinct (f a) (f b)))
(assert (= a c))
(assert (= b d))
; f(c) = f(d) would contradict f(a) != f(b) since a=c, b=d => f(a)=f(c), f(b)=f(d)
(assert (= (f c) (f d)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// SAT case: distinct(a,b), a=c but b!=d, so c and d can be equal.
#[test]
#[timeout(10_000)]
fn test_euf_diseq_sat_case_6152() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
; a != b
(assert (distinct a b))
; a = c only (no constraint on b=d)
(assert (= a c))
; c = d is fine because d is not constrained to equal b
(assert (= c d))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    // a=c=d, a!=b — satisfiable (just pick b != a)
    assert_eq!(outputs, vec!["sat"]);
}

/// Chain of equalities with disequality propagation.
/// Tests that the explanation is correct through a multi-step chain.
#[test]
#[timeout(10_000)]
fn test_euf_diseq_chain_explanation_6152() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const e U)
(declare-const f U)
; a != b
(assert (distinct a b))
; Chain: a = c = e and b = d = f
(assert (= a c))
(assert (= c e))
(assert (= b d))
(assert (= d f))
; e = f forces a = b (contradiction)
(assert (= e f))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    // a=c=e, b=d=f, a!=b, e=f => a=b contradiction => UNSAT
    assert_eq!(outputs, vec!["unsat"]);
}
