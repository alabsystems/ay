// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Publication pin for the exact-source native SOS lane's search allowance.
//!
//! The lane is consulted by the common UNSAT mint only when the retained
//! Alethe proof carries a known wire gap, as an upgrade of a presentation the
//! mint has ALREADY checked strictly. On an integer-only infeasible linear
//! system (a feasible rational relaxation, so no degree-bounded SOS witness
//! exists) the search spends the lane's whole work allowance and stops. That
//! allowance stop used to be reported as the terminal
//! `exact-source native SOS publication stopped by its resource/deadline
//! control` rejection, and `?` in the mint turned a computed, strictly checked
//! UNSAT into `unknown (incomplete self-check-rejected)` — the
//! `differential_qf_lia_vs_z3` completeness failure on `system_03.smt2`.
//!
//! A spent lane allowance is no evidence, not a refutation of the presentation
//! it would have upgraded; the mint now falls back to that presentation, as it
//! already did when the bounded search found no witness within its own caps.
//! Deadline, interrupt and memory stops remain terminal (pinned beside the
//! lane's control tests).

#![allow(clippy::panic)]

mod common;

const PREFIX: &str = "
    (set-logic QF_LIA)
    (declare-const v0 Int) (declare-const v1 Int)
    (declare-const v2 Int) (declare-const v3 Int)
    (assert (<= (+ (* -4 v0) (* -2 v1) (* -4 v2) (* 3 v3)) 47))
    (assert (<= (+ (* 1 v0) (* 2 v1) (* 2 v2) (* -1 v3)) 25))
    (assert (= (+ (* -1 v0) (* 4 v1) (* 4 v2) (* -5 v3)) 28))
    (assert (= (+ (* -4 v0) (* -2 v1) (* 5 v2) (* -2 v3)) -17))
    (assert (>= (+ (* -4 v0) (* -3 v1) (* -2 v2) (* -3 v3)) 20))
";

/// `benchmarks/smt/QF_LIA/system_03.smt2`: with this equation the system has a
/// rational solution and no integer one (Z3: unsat).
const INTEGER_ONLY_INFEASIBLE: &str = "(assert (= (+ (* 4 v0) (* 4 v1) (* 4 v2) (* -2 v3)) 49))";

/// The same system with the right-hand side moved by one: integer-satisfiable
/// (Z3: sat, e.g. v1 = -11, v2 = -3, v3 = -20).
const INTEGER_SATISFIABLE: &str = "(assert (= (+ (* 4 v0) (* 4 v1) (* 4 v2) (* -2 v3)) 48))";

fn solve(equation: &str) -> Vec<String> {
    common::solve_vec(&format!("{PREFIX}{equation}(check-sat)"))
}

#[test]
fn a_spent_sos_search_allowance_does_not_withhold_a_strictly_checked_refutation() {
    let results = solve(INTEGER_ONLY_INFEASIBLE);
    assert!(
        results.iter().any(|result| result == "unsat"),
        "an integer-only infeasible system whose native SOS search merely ran \
         out of its lane allowance must keep its strictly checked refutation; \
         got {results:?}"
    );
    assert!(
        !results.iter().any(|result| result.starts_with("unknown")),
        "the lane allowance is not a terminal stop; got {results:?}"
    );
}

#[test]
fn the_fall_through_does_not_manufacture_a_refutation() {
    // Direction that would be a soundness defect: the sibling system differs by
    // one in a right-hand side and has an integer solution. Nothing about
    // keeping an existing presentation may turn that into `unsat`.
    let results = solve(INTEGER_SATISFIABLE);
    assert!(
        results.iter().any(|result| result == "sat"),
        "the integer-satisfiable sibling must stay sat; got {results:?}"
    );
    assert!(
        !results.iter().any(|result| result == "unsat"),
        "no refutation may be minted for a satisfiable system; got {results:?}"
    );
}
