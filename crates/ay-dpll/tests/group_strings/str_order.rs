// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `str.<` / `str.<=` lexicographic-order reasoning. These predicates are
//! uninterpreted for string variables, so order contradictions used to come back
//! `unknown`. The string solver now instantiates the VALID order axioms
//! (antisymmetry, transitivity, str.<= antisymmetry) so it can refute them.
//! Every verdict matches z3 4.15.4; soundness re-validated by a 406-instance
//! QF_SLIA/QF_S differential sweep (0 wrong answers). The sat side (a witness for
//! `x < y` alone) stays a sound `unknown` — never a wrong answer.

fn solve(smt: &str) -> String {
    crate::common::solve(smt)
}

#[test]
fn str_lt_antisymmetry_is_unsat() {
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
             (assert (str.< x y))(assert (str.< y x))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn str_lt_transitivity_cycle_is_unsat() {
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)(declare-fun z () String)\
             (assert (str.< x y))(assert (str.< y z))(assert (str.< z x))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn str_le_antisymmetry_is_unsat() {
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
             (assert (str.<= x y))(assert (str.<= y x))(assert (not (= x y)))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn str_lt_chain_is_not_over_rejected() {
    // A consistent chain must NOT be refuted (the axioms must not over-fire).
    // z3 says sat; AY may return unknown (no witness) but must never say unsat.
    let r = solve(
        "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)(declare-fun z () String)\
         (assert (str.< x y))(assert (str.< y z))(check-sat)",
    );
    assert_ne!(r, "unsat", "a consistent str.< chain must not be refuted");
}

#[test]
fn str_lt_ground_content_still_decides() {
    // Content-level contradiction (b > a lexicographically) still unsat.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
             (assert (str.< x y))(assert (= x \"b\"))(assert (= y \"a\"))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn str_le_totality_is_unsat() {
    // Totality: for any x, y, either x ≤ y or y ≤ x. So ¬(x≤y) ∧ ¬(y≤x) is unsat.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
             (assert (not (str.<= x y)))(assert (not (str.<= y x)))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn str_lt_le_relationship_is_enforced() {
    // a < b implies a ≤ b.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
             (assert (str.< x y))(assert (not (str.<= x y)))(check-sat)"
        ),
        "unsat"
    );
    // a ≤ b ∧ a ≠ b implies a < b.
    assert_eq!(
        solve(
            "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
             (assert (str.<= x y))(assert (not (str.< x y)))(assert (not (= x y)))(check-sat)"
        ),
        "unsat"
    );
}
