// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Clause budget for eager BV congruence (`generate_euf_bv_axioms_debug`).
//!
//! Congruence is expanded into CNF for every pair of same-symbol
//! applications, quadratic in their number. Past its clause budget the pass
//! stops; the clauses it emitted are a subset of the full axiomatization, so
//! an UNSAT still stands. A SAT under the partial encoding is completed
//! lazily (AY-SMT-7, `bv_congruence_refine`): the model is checked against
//! every pair the full pass would have emitted, the disagreeing pairs get
//! their clauses and the SAT solver runs again, so a SAT that survives is a
//! model of the full axiomatization.
//!
//! 200 applications of a 32-bit `f` are 19,900 pairs, about 190 clauses
//! each: past the budget.

use ntest::timeout;

const APPLICATIONS: usize = 200;

fn many_applications(extra: &str) -> String {
    let mut smt =
        String::from("(set-logic QF_UFBV)\n(declare-fun f ((_ BitVec 32)) (_ BitVec 32))\n");
    for i in 0..APPLICATIONS {
        smt.push_str(&format!("(declare-const x{i} (_ BitVec 32))\n"));
    }
    smt.push_str(extra);
    for i in 0..APPLICATIONS {
        smt.push_str(&format!("(assert (= (f x{i}) (bvadd x{i} #x00000001)))\n"));
    }
    smt.push_str("(check-sat)\n");
    smt
}

/// Satisfiable (`f(x) = x + 1`). The congruence pass stops at its budget,
/// and the lazy completion checks the model against every remaining pair
/// before `sat` is reported.
#[test]
#[timeout(120_000)]
fn congruence_past_budget_completes_lazily_to_sat() {
    let outputs = crate::common::solve_vec(&many_applications(""));
    assert_eq!(outputs, vec!["sat"]);
}

/// Twin: the first pair's congruence clause is emitted before the budget
/// is reached, and `x0 = x1` with `f(x0) != f(x1)` is refuted by it.
#[test]
#[timeout(120_000)]
fn congruence_past_budget_keeps_unsat() {
    let outputs = crate::common::solve_vec(&many_applications(
        "(assert (= x0 (bvadd x1 #x00000000)))\n(assert (not (= (f x0) (f x1))))\n",
    ));
    assert_eq!(outputs, vec!["unsat"]);
}
