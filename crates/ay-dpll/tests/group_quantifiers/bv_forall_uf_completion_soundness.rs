// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression tests for BV/interpreted-sort `forall` wrong-SAT (#3).
//!
//! A bare `(= u v)` between two same-sort bound variables was treated as
//! "supported by UF completion" for ANY non-datatype sort by
//! `same_sort_variable_equality`. That is only sound for a freely-collapsible
//! *uninterpreted* sort (the completion model may identify `u` and `v`). For a
//! BitVector sort the domain is fixed at `2^width` distinct values, so
//! `(forall ((u (_ BitVec w)) (v (_ BitVec w))) (= u v))` is genuinely UNSAT
//! (e.g. `u=0, v=1`). The buggy shortcut returned a final `sat` for these,
//! a wrong answer. The fix restricts the var-var-equality completion shortcut
//! to non-datatype uninterpreted sorts, so BV (and Bool/Int/...) foralls fail
//! closed (decide UNSAT via MBQI, or degrade to Unknown) instead of wrong-SAT.

use ntest::timeout;

/// A SAT verdict for any of these is unsound (the formula is truly UNSAT).
/// UNSAT (decided) or Unknown (failed closed) are both acceptable.
fn assert_not_sat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must not return sat (truly UNSAT), got {results:?}"
    );
}

/// `(forall ((q0 (_ BitVec 8)) (q1 (_ BitVec 8))) (= q0 q1))` — two BV8 binders,
/// domain product 65536 > instantiation budget. Truly UNSAT (q0=0, q1=1).
/// Was wrong-SAT via the var-var UF-completion shortcut.
#[test]
#[timeout(20000)]
fn test_forall_two_bv8_var_equality_not_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((q0 (_ BitVec 8)) (q1 (_ BitVec 8))) (= q0 q1)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall two BV8 var equality");
}

/// `(forall ((q (_ BitVec 9))) (= c q))` — single BV9 binder, domain 512 > 256
/// budget. Truly UNSAT. Was wrong-SAT.
#[test]
#[timeout(20000)]
fn test_forall_bv9_equals_const_not_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const c (_ BitVec 9))
        (assert (forall ((q (_ BitVec 9))) (= c q)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall BV9 = const");
}

/// `(forall ((a (_ BitVec 16)) (b (_ BitVec 16))) (= a b))` — large domain,
/// truly UNSAT. Must not wrong-SAT.
#[test]
#[timeout(20000)]
fn test_forall_two_bv16_var_equality_not_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((a (_ BitVec 16)) (b (_ BitVec 16))) (= a b)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall two BV16 var equality");
}

/// `(forall ((a (_ BitVec 1)) (b (_ BitVec 1))) (= a b))` — even a 1-bit BV has
/// two distinct values (0 != 1), so this is UNSAT, not SAT.
#[test]
#[timeout(20000)]
fn test_forall_two_bv1_var_equality_not_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((a (_ BitVec 1)) (b (_ BitVec 1))) (= a b)))
        (check-sat)
    "#;
    assert_not_sat(smt, "forall two BV1 var equality");
}

/// A single BV8 binder (domain 256) is small enough to decide via finite-domain
/// expansion. It must remain `unsat` (decided), not regress to Unknown.
#[test]
#[timeout(20000)]
fn test_forall_bv8_equals_const_decides_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const c (_ BitVec 8))
        (assert (forall ((q (_ BitVec 8))) (= c q)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "single BV8 forall = const should decide unsat"
    );
}

/// NON-REGRESSION: the legitimate freely-collapsible uninterpreted-sort
/// completion path must still accept SAT. `(forall ((u U) (v U)) (= u v))` over
/// an uninterpreted sort U is SAT (interpret U as a one-element domain).
#[test]
#[timeout(20000)]
fn test_forall_uninterpreted_var_equality_still_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-sort U 0)
        (assert (forall ((u U) (v U)) (= u v)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall over uninterpreted sort var equality should still be sat (singleton domain)"
    );
}

/// NON-REGRESSION: a genuinely satisfiable BV forall (a tautology body) stays
/// SAT — the fix only constrains the var-var-equality shortcut.
#[test]
#[timeout(20000)]
fn test_forall_bv_tautology_body_still_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const c (_ BitVec 4))
        (assert (forall ((q (_ BitVec 4))) (=> (= q q) true)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall BV4 tautology body should be sat"
    );
}
