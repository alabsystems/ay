// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! #row-chain-dn-conclusion: read-over-write under an array equality, at a
//! read index that is a DISTINCT NUMERAL from every store index, must publish
//! the `unsat` AY computes.
//!
//! `(= b (store a 3 9))` plus `(distinct (select b 4) (select a 4))` is UNSAT
//! by read-over-write-negative, and AY's ground lane refutes it every time. The
//! verdict was withheld:
//!
//! ```text
//! computed UNSAT rejected by mandatory strict certification: strict UNSAT
//! proof validation failed: step t2 has invalid theory lemma: array
//! read-over-write-chain clause does not match the exact schema
//! ```
//!
//! CAUSE. A theory conflict is recorded as the negation of each conflicting
//! literal, so refuting the AUTHORED negation `(not (= b[4] a[4]))` produces
//! the raw term `(not (not (= b[4] a[4])))` — `mk_not` does not fold the pair.
//! The `#ground-conflict-decomp` arm-2 planner read its two sides through
//! `strip_not_local`, which peels `not`s in PARITY, so it classified that
//! doubly-negated term as the clause's positive equality and copied it verbatim
//! into an `ArrayRowChain` lemma it labelled itself. The strict schema reaches
//! that literal through `equality_sides`, which peels ONE `not` and needs a
//! `(= u w)` under it, so the minted lemma failed its own validator — and
//! because the lemma was no longer trust-kind,
//! `collapse_double_negated_trust_lemma_literals` (the pass that exists for
//! exactly this normalization, and which only ever sees TRUST-kind lemmas)
//! could not see it either.
//!
//! The planner now peels ONE `not`, exactly as the schema does, and declines a
//! shape the schema cannot read. That is not a capability loss: the `Generic`
//! lemma survives untouched and the normalization pass rescues it, through the
//! checker's own recognizer and a whole-proof strict re-check.
//!
//! The SAT control pins that nothing was made to answer `unsat` that should not.

use crate::common::solve_vec;

fn unsat(name: &str, smt: &str) {
    assert_eq!(
        solve_vec(smt),
        vec!["unsat"],
        "{name}: read-over-write at a distinct numeral index is UNSAT"
    );
}

/// The measured defect: the store index and the read index are distinct
/// numerals, so a correct clause carries no `(= 4 3)` guard to peel and the
/// conclusion arrives doubly negated.
#[test]
fn store_equation_distinct_numeral_read_is_unsat() {
    unsat(
        "distinct_numeral_read",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (distinct (select b 4) (select a 4)))
        (check-sat)
    "#,
    );
}

/// Same shape with the store equation written the other way round.
#[test]
fn flipped_store_equation_distinct_numeral_read_is_unsat() {
    unsat(
        "flipped_store_equation",
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= (store a 3 9) b))
        (assert (distinct (select b 4) (select a 4)))
        (check-sat)
    "#,
    );
}

/// No `set-logic`: the routing must not be what decides this.
#[test]
fn no_set_logic_distinct_numeral_read_is_unsat() {
    unsat(
        "no_set_logic",
        r#"
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (distinct (select b 4) (select a 4)))
        (check-sat)
    "#,
    );
}

/// SOUNDNESS CONTROL. The same two arrays with the equality asserted POSITIVE
/// is satisfiable, and must never be answered `unsat`.
#[test]
fn matching_read_stays_satisfiable() {
    let results = solve_vec(
        r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (= (select b 4) (select a 4)))
        (check-sat)
    "#,
    );
    assert!(
        results.iter().all(|result| result != "unsat"),
        "a satisfiable read-over-write shape must never answer unsat: {results:?}"
    );
}
