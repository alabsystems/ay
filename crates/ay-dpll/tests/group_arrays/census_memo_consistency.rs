// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The array model census answers each reconstruction question ONCE per pass
//! and reuses it (`CensusMemo`, model/dt_model.rs). These queries are shaped to
//! put three or more ARRAY-VALUED reads in one (identity class, evaluated
//! index) cell, which is the only shape whose all-pairs compatibility scan asks
//! `census_collect_cells` for the same term more than once — i.e. the only
//! shape that takes the memo's HIT path, where the debug-build differential
//! oracle recomputes and compares.
//!
//! Without a case like this the oracle is dead code in every test run: the
//! whole pre-existing ay-dpll suite queries each `(term, depth)` at most once,
//! so a memo that returned garbage on a hit would pass it silently. (Verified
//! by deliberately poisoning the memo's stored value: the entire suite stayed
//! green, and only these tests catch it.)
//!
//! The verdicts asserted here are the ordinary ones — the point is that they
//! are reached with the memo hit path live and the oracle armed.

use ay_dpll::Executor;
use ay_frontend::parse;

fn verdict(smt: &str) -> String {
    let commands = parse(smt).expect("parse ok");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("exec ok")
        .into_iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "NORESULT".into())
}

/// Three DERIVED-equal indices into an array of arrays. `(select a i)`,
/// `(select a j)` and `(select a k)` are array-valued reads that land in one
/// census cell, so the compatibility scan compares all three pairs and asks for
/// each inner array's cell map twice.
#[test]
fn nested_array_reads_at_derived_equal_indices_are_consistent_sat() {
    assert_eq!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-const a (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 4))))
        (declare-const i (_ BitVec 4))
        (declare-const j (_ BitVec 4))
        (declare-const k (_ BitVec 4))
        (assert (= i (bvadd j #x0)))
        (assert (= j (bvadd k #x0)))
        (assert (= (select (select a i) #x0) #x1))
        (assert (= (select (select a j) #x0) #x1))
        (assert (= (select (select a k) #x0) #x1))
        (check-sat)
    "#
        ),
        "sat"
    );
}

/// The same cell shape, but the three reads are pinned to values that cannot
/// all hold at one cell. Whatever the solver decides, it must NOT be `sat` —
/// the reads are congruent and the pins contradict.
#[test]
fn nested_array_reads_at_derived_equal_indices_conflict_is_never_sat() {
    assert_ne!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-const a (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 4))))
        (declare-const i (_ BitVec 4))
        (declare-const j (_ BitVec 4))
        (declare-const k (_ BitVec 4))
        (assert (= i (bvadd j #x0)))
        (assert (= j (bvadd k #x0)))
        (assert (= (select (select a i) #x0) #x1))
        (assert (= (select (select a j) #x0) #x2))
        (assert (= (select (select a k) #x0) #x3))
        (check-sat)
    "#
        ),
        "sat"
    );
}

/// Four reads on a store-built array of arrays: the store chain gives each
/// inner array a syntactic cell function as well as an observed one, so the
/// memoized map has both halves and is asked for repeatedly across the six
/// pairs — this is the case whose memo hits the oracle catches first.
///
/// The query is satisfiable, but AY answers `unknown` here today (the
/// extensionality expansion of the nested array equality evaluates Unknown, so
/// the gate fails closed — a pre-existing completeness gap, unrelated to the
/// census). Assert only the soundness-relevant half: it must never come back
/// `unsat`.
#[test]
fn stored_nested_arrays_at_derived_equal_indices_are_never_unsat() {
    assert_ne!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-const base (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 4))))
        (declare-const inner (Array (_ BitVec 4) (_ BitVec 4)))
        (declare-const p (_ BitVec 4))
        (declare-const q (_ BitVec 4))
        (declare-const r (_ BitVec 4))
        (declare-const s (_ BitVec 4))
        (assert (= p (bvadd q #x0)))
        (assert (= q (bvadd r #x0)))
        (assert (= r (bvadd s #x0)))
        (assert (= (select (store base p inner) p) inner))
        (assert (= (select (store base p inner) q) inner))
        (assert (= (select (store base p inner) r) inner))
        (assert (= (select (store base p inner) s) inner))
        (assert (= (select inner #x0) #x7))
        (check-sat)
    "#
        ),
        "unsat"
    );
}
