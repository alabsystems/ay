// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression tests for the closed-universal-validity precheck
//! (#quant-ws closed-forall wrong-SAT).
//!
//! A top-level conjunct that is a `(forall vars body)` with a CLOSED,
//! quantifier-free body over FIXED-interpretation sorts (Bool/Int/Real/BitVec)
//! is model-independent: either valid, or unconditionally FALSE. When such a
//! universal is provably false (its skolemized negation is definitively SAT),
//! the whole conjunctive problem is UNSAT regardless of the other assertions.
//!
//! Before the fix, a bounded-guard array-extensionality `forall` sitting
//! alongside a closed false arithmetic universal derailed the refutation of the
//! latter and AY returned a wrong `sat`. The precheck decides UNSAT directly.
//!
//! SOUNDNESS GUARANTEE: the precheck only ever returns UNSAT, and only when a
//! conjunct is provably false. It is restricted to fixed-interpretation binder
//! sorts (so an uninterpreted-sort `∀u v:U. u=v` stays SAT — its model may
//! choose a singleton domain) and to quantifier-free, free-symbol-free bodies
//! (so `∀x∃y. y>x` alternations and array-extensionality `∀i. A0[i]=A1[i]`
//! universals are untouched).

use ntest::timeout;

fn assert_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "{label}: expected unsat (closed universal is false), got {results:?}"
    );
    assert!(
        !results.iter().any(|r| r == "sat"),
        "{label}: must NOT return sat (truly UNSAT), got {results:?}"
    );
}

fn assert_sat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "sat"),
        "{label}: expected sat, got {results:?}"
    );
}

fn assert_not_unsat(smt: &str, label: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "{label}: must NOT return unsat (it is satisfiable / valid), got {results:?}"
    );
}

/// The original wrong-SAT minimal repro: a bounded-guard array-extensionality
/// `forall` plus a CLOSED false arithmetic universal `∀q0 q1. q1>-6 ⇒ q0 >=
/// 2*q0-11` (≡ `q0 <= 11`, false at q0=12). Must be UNSAT.
#[test]
#[timeout(20000)]
fn closed_false_universal_with_array_ext_forall_is_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun A0 () (Array Int Int))
        (declare-fun A1 () (Array Int Int))
        (assert (forall ((i Int)) (=> (and (<= -2 i) (<= i 4)) (= (select A0 i) (select A1 i)))))
        (assert (forall ((q0 Int) (q1 Int)) (=> (> q1 -6) (>= q0 (+ -6 (+ -5 (* 2 q0)))))))
        (check-sat)
    "#;
    assert_unsat(smt, "closed false universal beside array-ext forall");
}

/// A closed false universal alone (no other quantifiers). Must be UNSAT.
#[test]
#[timeout(20000)]
fn closed_false_universal_alone_is_unsat() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((q0 Int) (q1 Int)) (=> (> q1 -6) (>= q0 (+ -6 (+ -5 (* 2 q0)))))))
        (check-sat)
    "#;
    assert_unsat(smt, "closed false universal alone");
}

/// A closed false universal as one conjunct of a top-level `(and ...)` with a
/// satisfiable ground conjunct. The `and`-conjunct still counts as top-level, so
/// the whole problem is UNSAT.
#[test]
#[timeout(20000)]
fn closed_false_universal_in_top_and_is_unsat() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun x () Int)
        (assert (and (>= x 0) (forall ((q0 Int)) (<= q0 11))))
        (check-sat)
    "#;
    assert_unsat(smt, "closed false universal in top-level and");
}

/// A closed BitVec false universal `∀a b:BV8. a=b` — fixed-domain sort, two
/// distinct values exist, so it is UNSAT.
#[test]
#[timeout(20000)]
fn closed_false_bv_universal_is_unsat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((a (_ BitVec 8)) (b (_ BitVec 8))) (= a b)))
        (check-sat)
    "#;
    assert_unsat(smt, "closed false BV universal");
}

/// NON-REGRESSION: a closed VALID universal must stay SAT — the precheck only
/// fires on PROVABLY-false universals (negation SAT), and a valid universal has
/// an UNSAT negation.
#[test]
#[timeout(20000)]
fn closed_valid_universal_stays_sat() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((q0 Int)) (=> (>= q0 5) (>= q0 0))))
        (check-sat)
    "#;
    assert_sat(smt, "closed valid universal");
}

/// NON-REGRESSION: a closed valid universal over a free constant `x` (still a
/// valid arithmetic identity for all q0 once x>=0) must stay SAT. Here the body
/// references the free constant `x`, so the precheck does NOT classify it as
/// closed and leaves it to the normal pipeline.
#[test]
#[timeout(20000)]
fn open_universal_with_free_const_stays_sat() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun x () Int)
        (assert (forall ((q0 Int)) (>= (+ q0 x) q0)))
        (assert (>= x 0))
        (check-sat)
    "#;
    assert_sat(smt, "open universal with free const");
}

/// CRITICAL NON-REGRESSION: a `∀x∃y. y>x` alternation is VALID over Int, so it
/// must NEVER become unsat. Its body contains an inner `exists` (a quantifier),
/// so the precheck excludes it.
#[test]
#[timeout(20000)]
fn forall_exists_alternation_never_unsat() {
    let smt = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (> y x))))
        (check-sat)
    "#;
    assert_not_unsat(smt, "forall-exists alternation");
}

/// CRITICAL NON-REGRESSION: a valid array-extensionality universal `∀i.
/// A0[i]=A1[i]` with `A0=A1` is SAT. Its body references free array symbols
/// (`select` over A0/A1), so the precheck excludes it (never unsat).
#[test]
#[timeout(20000)]
fn array_extensionality_universal_never_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun A0 () (Array Int Int))
        (declare-fun A1 () (Array Int Int))
        (assert (forall ((i Int)) (= (select A0 i) (select A1 i))))
        (assert (= A0 A1))
        (check-sat)
    "#;
    assert_not_unsat(smt, "valid array extensionality universal");
}

/// CRITICAL NON-REGRESSION: `∀u v:U. u=v` over an UNINTERPRETED sort U is SAT
/// (interpret U as a singleton domain). U is NOT a fixed-interpretation sort, so
/// the precheck excludes it — it must never become unsat.
#[test]
#[timeout(20000)]
fn uninterpreted_sort_var_equality_never_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-sort U 0)
        (assert (forall ((u U) (v U)) (= u v)))
        (check-sat)
    "#;
    assert_not_unsat(smt, "uninterpreted-sort var equality universal");
}

/// A partial arithmetic operator may still refute a universal at a concrete
/// point where its semantics are fully defined.  The literal-witness lane must
/// reach `y = 3` and use the fixed fact `(rem 2 3) = 2`.
#[test]
#[timeout(20000)]
fn defined_rem_literal_witness_is_unsat() {
    let smt = r#"
        (set-logic UFLIA)
        (assert (forall ((y Int)) (= (rem 2 y) 0)))
        (check-sat)
    "#;
    assert_unsat(smt, "defined rem literal witness");
}

/// The same lane must not treat an under-specified zero-divisor application as
/// false.  This universal is satisfiable by choosing the value of `(rem 0 0)`
/// to be zero; all nonzero divisor instances already equal zero.
#[test]
#[timeout(20000)]
fn rem_zero_divisor_literal_witness_never_refutes() {
    let smt = r#"
        (set-logic UFLIA)
        (assert (forall ((y Int)) (= (rem 0 y) 0)))
        (check-sat)
    "#;
    assert_not_unsat(smt, "under-specified rem-by-zero instance");
}

/// Integer `mod` has the same under-specified zero-divisor contract as `rem`.
/// Literal probing may use every nonzero `y`, but must not manufacture a
/// refutation from the unconstrained value `(mod 0 0)`.
#[test]
#[timeout(20000)]
fn mod_zero_divisor_literal_witness_never_refutes() {
    let smt = r#"
        (set-logic UFLIA)
        (assert (forall ((y Int)) (= (mod 0 y) 0)))
        (check-sat)
    "#;
    assert_not_unsat(smt, "under-specified mod-by-zero instance");
}

/// Integer `div` is likewise fixed at nonzero divisors and under-specified at
/// zero.  Choosing `(div 0 0) = 0` satisfies this universal, so a literal
/// witness must never turn it into UNSAT.
#[test]
#[timeout(20000)]
fn div_zero_divisor_literal_witness_never_refutes() {
    let smt = r#"
        (set-logic UFLIA)
        (assert (forall ((y Int)) (= (div 0 y) 0)))
        (check-sat)
    "#;
    assert_not_unsat(smt, "under-specified div-by-zero instance");
}
