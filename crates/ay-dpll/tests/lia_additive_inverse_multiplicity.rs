// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end soundness regressions for additive-inverse cancellation in
//! `TermStore::mk_add`.
//!
//! A prior `mk_add` implementation cancelled `a + (-a)` using a deduplicating
//! hash set over hash-consed `TermId`s, losing multiplicity. For a sum such as
//! `(+ a (- a) a)` it dropped BOTH copies of `a` along with `(- a)`, rewriting
//! the whole linear term to the constant `0`. That corrupted constraints at the
//! formula-simplification level (before any theory solving) and produced WRONG
//! verdicts in both directions:
//!
//! * unsat-on-sat: `(<= (+ a (- a) a) -1)` is really `a <= -1` (SAT), but the
//!   buggy simplifier turned the LHS into `0`, saw `(0 <= -1)`, and reported
//!   UNSAT for a satisfiable formula (an unsound refutation).
//! * sat-on-unsat: `(<= (+ a (- a) a) 1) /\ (>= a 2)` is really `a <= 1` and
//!   `a >= 2` (UNSAT), but the buggy simplifier dropped the `a <= 1` constraint
//!   and reported SAT.
//!
//! Cancellation is now performed by per-base coefficient summation, which keeps
//! full multiplicity, so `(+ a (- a) a)` correctly stays `a`.

mod common;

use ntest::timeout;

#[test]
#[timeout(30_000)]
fn additive_inverse_multiplicity_unsat_on_sat_refutation_is_sound() {
    // `(+ a (- a) a)` must simplify to `a`, so `a <= -1` is satisfiable.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (assert (<= (+ a (- a) a) (- 1)))
        (check-sat)
    "#;
    assert_eq!(
        common::solve_vec(smt),
        vec!["sat"],
        "(<= (+ a (- a) a) -1) is a<=-1 and must be SAT; a buggy mk_add folded \
         the LHS to 0 and produced an unsound UNSAT"
    );
}

#[test]
#[timeout(30_000)]
fn additive_inverse_multiplicity_sat_on_unsat_not_dropped() {
    // `(+ a (- a) a)` is `a`, so `a <= 1` together with `a >= 2` is UNSAT.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (assert (<= (+ a (- a) a) 1))
        (assert (>= a 2))
        (check-sat)
    "#;
    assert_eq!(
        common::solve_vec(smt),
        vec!["unsat"],
        "(<= (+ a (- a) a) 1) is a<=1; with a>=2 the conjunction is UNSAT; a \
         buggy mk_add dropped the a<=1 constraint and produced a spurious SAT"
    );
}

#[test]
#[timeout(30_000)]
fn additive_inverse_multiplicity_negative_net_coefficient() {
    // `(+ a (- a) (- a))` is `-a`, so `-a <= -2` is `a >= 2`; with `a <= 0`
    // this is UNSAT.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (assert (<= (+ a (- a) (- a)) (- 2)))
        (assert (<= a 0))
        (check-sat)
    "#;
    assert_eq!(
        common::solve_vec(smt),
        vec!["unsat"],
        "(+ a (- a) (- a)) is -a; (-a <= -2) /\\ (a <= 0) is UNSAT"
    );
}
