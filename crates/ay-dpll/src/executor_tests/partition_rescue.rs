// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wave C P2-multitheory: post-dispatch symbol-disjoint partition rescue.
//!
//! Trivially-(un)sat multi-theory conjunctions with no combined solver lane —
//! `{Real|String|FP} × {BV|Real|String|Int}` over symbol-disjoint conjuncts —
//! must decide (matching z3) via the partition rescue, while every adversarial
//! coupling / cardinality / non-scalar shape must fail closed to unknown or
//! decide correctly, NEVER a wrong verdict.

use crate::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(smt: &str) -> Executor {
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    exec
}

fn assert_sat(smt: &str) {
    let exec = solve(smt);
    assert!(
        exec.last_result().is_some_and(|r| r.is_sat()),
        "expected SAT, got {:?}",
        exec.last_result()
    );
}

fn assert_unsat(smt: &str) {
    let exec = solve(smt);
    assert!(
        exec.last_result().is_some_and(|r| r.is_unsat()),
        "expected UNSAT, got {:?}",
        exec.last_result()
    );
}

fn assert_not_sat(smt: &str) {
    // sound: unknown or unsat, but NEVER a wrong sat.
    let exec = solve(smt);
    assert!(
        !exec.last_result().is_some_and(|r| r.is_sat()),
        "expected NOT-SAT (unknown/unsat), got sat"
    );
}

// ---------------------------------------------------------------------------
// Headline probes: trivially-SAT multi-theory conjunctions now decide.
// ---------------------------------------------------------------------------

#[test]
#[timeout(30000)]
fn real_bv_disjoint_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const b (_ BitVec 8))
        (assert (> r 1.5))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn real_string_disjoint_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const s String)
        (assert (> r 0.5))
        (assert (= s "hi"))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn string_bv_disjoint_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const s String)
        (declare-const b (_ BitVec 8))
        (assert (= s "hi"))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn real_string_int_three_theories_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const s String)
        (declare-const i Int)
        (assert (> r 0.5))
        (assert (= s "hi"))
        (assert (> i 7))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn int_bv_disjoint_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const i Int)
        (declare-const b (_ BitVec 8))
        (assert (> i 1))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

// ---------------------------------------------------------------------------
// UNSAT via any-component-unsat (subset monotonicity — no disjointness needed).
// ---------------------------------------------------------------------------

#[test]
#[timeout(30000)]
fn real_side_unsat_with_bv_present() {
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const b (_ BitVec 8))
        (assert (> r 1.5))
        (assert (< r 1.0))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn lra_unsat_with_bv_constant() {
    // g3a: trivial LRA contradiction missed by the AUFLIA-only indep lane today.
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-const x Real)
        (declare-const b (_ BitVec 1))
        (assert (< x 0.0))
        (assert (> x 1.0))
        (assert (= b #b1))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn string_side_unsat_with_real_present() {
    // wrong-fact twin on the String side.
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const s String)
        (assert (> r 0.5))
        (assert (= s "hi"))
        (assert (= (str.len s) 5))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn bv_side_unsat_with_real_present() {
    // wrong-fact twin on the BV side.
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const b (_ BitVec 8))
        (assert (> r 1.5))
        (assert (= b #x0a))
        (assert (= b #x0b))
        (check-sat)
    "#,
    );
}

// ---------------------------------------------------------------------------
// Adversarial coupling probes — conjuncts that SHARE a symbol must NOT be
// partitioned; the verdict must match z3, never a wrong combine.
// ---------------------------------------------------------------------------

#[test]
#[timeout(30000)]
fn shared_arity0_uf_over_interpreted_args_is_unsat_never_sat() {
    // (= (f 0) 1) ∧ (= (f 0) 2) share `f` (arity>0 UF) -> one component -> EUF
    // refutes. Must be unsat/unknown, NEVER sat (REVISE objection 3).
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (declare-const b (_ BitVec 8))
        (assert (= (f 0) 1))
        (assert (= (f 0) 2))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
    // z3 says unsat; AY should too (EUF puts (f 0) in one class).
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (declare-const b (_ BitVec 8))
        (assert (= (f 0) 1))
        (assert (= (f 0) 2))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn or_coupled_conjuncts_stay_one_component() {
    // (or (> r 1.5) (= b #x00)) ∧ (= b #x0a): the OR ties r and b into ONE
    // component -> rescue no-op -> stays unknown (sound; z3 sat is a documented
    // residual). Must never be a wrong verdict.
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const b (_ BitVec 8))
        (assert (or (> r 1.5) (= b #x00)))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn cross_theory_shared_symbol_not_wrongly_combined() {
    // r appears in a satisfiable and an unsatisfiable atom in the SAME
    // component; a shared-symbol partition must keep them together -> unsat.
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (declare-const b (_ BitVec 8))
        (assert (> r 1.5))
        (assert (< r 1.0))
        (assert (= b #x0a))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

// ---------------------------------------------------------------------------
// Non-trigger byte-identity: single-theory / already-deciding problems must be
// untouched by the rescue.
// ---------------------------------------------------------------------------

#[test]
#[timeout(30000)]
fn pure_real_still_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const r Real)
        (assert (> r 1.5))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn pure_bv_still_sat() {
    assert_sat(
        r#"
        (set-logic ALL)
        (declare-const b (_ BitVec 8))
        (assert (= b #x0a))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30000)]
fn single_component_lia_unsat_unchanged() {
    assert_unsat(
        r#"
        (set-logic ALL)
        (declare-const x Int)
        (assert (> x 5))
        (assert (< x 3))
        (check-sat)
    "#,
    );
}
