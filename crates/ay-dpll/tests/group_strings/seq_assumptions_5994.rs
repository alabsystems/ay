// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #5994: check-sat-assuming with QF_SEQ/QF_SEQLIA
//! must use combined EUF+Seq solver (not bare SeqSolver).
//!
//! Before fix, check-sat-assuming routed through `TheoryKind::Seq` which
//! creates a bare `SeqSolver` — missing EUF transitivity, LIA constraints,
//! and seq.len/seq.nth axiom injection, producing false SAT.
//!
//! Note: the separate `seq.nth` variable-indirection false-SAT gap (#6236) is
//! intentionally not represented as a passing test here. A regression test that
//! accepts the current wrong `sat` answer is misleading and would fail if the
//! solver later returns the correct `unsat`.

use ntest::timeout;

/// QF_SEQ check-sat-assuming: transitive equality should be UNSAT.
///
/// `s = seq.unit(1)`, `t = seq.empty`, `s = t` under assumptions.
/// EUF transitivity needed: `seq.unit(1) = seq.empty` is contradictory
/// because unit sequences have length 1, empty has length 0.
/// Bare SeqSolver without EUF may not detect the conflict.
#[test]
#[timeout(10000)]
fn test_seq_assumptions_transitive_eq_unsat() {
    let smt = r#"
        (set-logic QF_SEQ)
        (declare-fun s () (Seq Int))
        (declare-fun t () (Seq Int))
        (assert (= s (seq.unit 1)))
        (assert (= t (as seq.empty (Seq Int))))
        (check-sat-assuming ((= s t)))
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results[0] == "unsat" || results[0] == "unknown",
        "Transitive equality seq.unit(1) = seq.empty must not be SAT, got: {results:?}"
    );
}

/// QF_SEQLIA check-sat-assuming: seq.len axiom needed.
///
/// `s = seq.unit(x)` implies `seq.len(s) = 1`. Under assumption
/// `seq.len(s) = 0`, this should be UNSAT. Without LIA + len axioms,
/// the bare SeqSolver has no length reasoning and may return SAT.
#[test]
#[timeout(10000)]
fn test_seq_lia_assumptions_len_axiom_unsat() {
    let smt = r#"
        (set-logic QF_SEQLIA)
        (declare-fun s () (Seq Int))
        (declare-fun x () Int)
        (assert (= s (seq.unit x)))
        (check-sat-assuming ((= (seq.len s) 0)))
    "#;
    let results = crate::common::solve_vec(smt);
    // seq.unit has length 1, so len(s) = 0 contradicts s = seq.unit(x).
    assert!(
        results[0] == "unsat" || results[0] == "unknown",
        "seq.unit length must be 1, len=0 should be UNSAT, got: {results:?}"
    );
}

/// QF_SEQ check-sat-assuming: basic SAT case.
///
/// `s = seq.unit(1)` with assumption `s = seq.unit(1)` — trivially SAT.
/// Ensures the assumptions path doesn't break SAT results.
#[test]
#[timeout(10000)]
fn test_seq_assumptions_basic_sat() {
    let smt = r#"
        (set-logic QF_SEQ)
        (declare-fun s () (Seq Int))
        (assert (= s (seq.unit 1)))
        (check-sat-assuming ((= s (seq.unit 1))))
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results[0] == "sat" || results[0] == "unknown",
        "Consistent assumptions should be SAT, got: {results:?}"
    );
}

/// QF_SEQLIA check-sat-assuming: seq.nth axiom.
///
/// `s = seq.unit(5)`, `seq.nth(s, 0) = 5` should be SAT with the
/// nth axiom: `seq.nth(seq.unit(x), 0) = x`.
#[test]
#[timeout(10000)]
fn test_seq_lia_assumptions_nth_axiom_sat() {
    let smt = r#"
        (set-logic QF_SEQLIA)
        (declare-fun s () (Seq Int))
        (assert (= s (seq.unit 5)))
        (check-sat-assuming ((= (seq.nth s 0) 5)))
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results[0] == "sat" || results[0] == "unknown",
        "seq.nth(seq.unit(5), 0) = 5 should be SAT, got: {results:?}"
    );
}
