// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! END-TO-END verdict guards for AY's reserved-name gates.
//!
//! AY matches a large part of its theory vocabulary STRUCTURALLY, by the name
//! on `App(Symbol::Named(..))`, with no sort check and — for the
//! qualified-`(as …)` path — BEFORE declared-symbol resolution. Any spelling
//! reachable by such a matcher that a user can also `declare` is a silent
//! conflation channel: the user's symbol acquires the builtin's semantics.
//!
//! The frontend closes those channels by refusing the declaration
//! (`ElaborateError::ReservedSymbol`). Unit tests over the predicate live in
//! `ay-frontend`; this file pins what actually matters — the VERDICT AY
//! publishes — against the pinned oracle `/opt/homebrew/bin/z3` 5.0.0.
//!
//! Contract asserted here is deliberately one-sided and fail-closed: each
//! fixture forbids exactly the verdict that would be WRONG. A refusal (the
//! elaborator erroring out) and `unknown` are both acceptable; only publishing
//! the oracle's complement is not. That keeps these tests honest if the gates
//! are ever legitimately narrowed with a real shadowing guard behind them —
//! they will still catch the wrong answer, and only the wrong answer.

use crate::Executor;
use ay_frontend::parse;

/// Solve `smt`, tolerating an elaboration refusal.
///
/// Returns `None` when AY refuses the script (a fail-closed error is always a
/// sound outcome), otherwise the first `sat`/`unsat`/`unknown` line.
fn verdict_or_refusal(smt: &str) -> Option<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).ok()?;
    outputs
        .iter()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
}

/// Assert AY never publishes `forbidden` for `smt`.
fn assert_never(smt: &str, forbidden: &str, oracle: &str, why: &str) {
    let got = verdict_or_refusal(smt);
    assert!(
        got.as_deref() != Some(forbidden),
        "AY published `{forbidden}` where the pinned oracle z3 5.0.0 answers \
         `{oracle}` — {why}\nSMT2:\n{smt}"
    );
}

/// The `map[<f>]` capture, at the verdict level.
///
/// `TermStore::get_array_map` (ay-core/src/term/array.rs) treats ANY `App`
/// named `map[<f>]` as the array map of `<f>` and licenses
/// `select(map[f](a..), i) → f(select(a, i)..)`. A user function declared
/// `|map[f]|` therefore acquires map semantics, which makes the fixture below
/// look contradictory. Pinned oracle z3 5.0.0: `sat`. Before the reserved
/// namespace was single-sourced into the core elaborator, AY COMPUTED unsat
/// here (published `unknown` only because the strict certification gate
/// refused to certify it) — a false PROVE, the cardinal soundness failure.
#[test]
fn test_array_map_namespace_never_yields_unsat() {
    let smt = r#"
        (declare-fun f (Int) Int)
        (declare-fun |map[f]| ((Array Int Int)) (Array Int Int))
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (|map[f]| a)))
        (assert (distinct (select b 0) (f (select a 0))))
        (check-sat)
    "#;
    assert_never(
        smt,
        "unsat",
        "sat",
        "`|map[f]|` is an ordinary uninterpreted function to the oracle; AY's \
         array-map matcher keys on the NAME alone",
    );
}

/// Reproducer 1 — `set.empty` under a Bool-only logic must never be `unsat`.
///
/// `elaborate_qualified_app` matches the parsed name `set.empty` and returns
/// the constant-FALSE array before it ever consults the declared-symbol table,
/// so `(select (as set.empty (Array E Bool)) x)` elaborates to `false` no
/// matter what the user declared. Pinned oracle z3 5.0.0: `sat` (`set.empty`
/// is just a user constant there). Control: renaming the symbol to `g` makes
/// AY answer `unknown` — the divergence is the NAME, not the formula.
#[test]
fn test_declared_set_empty_never_yields_unsat() {
    let smt = r#"
        (set-logic BOOL)
        (declare-sort E 0)
        (declare-fun set.empty () (Array E Bool))
        (declare-const x E)
        (assert (select (as set.empty (Array E Bool)) x))
        (check-sat)
    "#;
    assert_never(
        smt,
        "unsat",
        "sat",
        "`set.empty` is intercepted by name in the qualified-identifier \
         elaborator and treated as the constant-false array",
    );

    // Control: the SAME formula under a name AY does not intercept must not be
    // refuted either. If this ever starts failing, the divergence stopped being
    // about the reserved spelling and the fixture above lost its meaning.
    let control = smt.replace("set.empty", "g");
    assert_never(
        &control,
        "unsat",
        "sat",
        "control: an ordinary uninterpreted array constant is satisfiable",
    );
}

/// Reproducer 2 — `map.empty` under a Bool-only logic must never be `sat`.
///
/// The opposite direction, and the reason a name-keyed interception cannot be
/// made safe by "just" letting the declaration through: the builtin path mints
/// a FRESH default value per occurrence, so two reads of the same declared
/// constant at the same index can disagree. Asserting both `= 7` and `= 8` is
/// then satisfied by a self-refuting model. Pinned oracle z3 5.0.0: `unsat`.
#[test]
fn test_declared_map_empty_never_yields_sat() {
    let smt = r#"
        (set-logic BOOL)
        (declare-sort E 0)
        (declare-fun map.empty () (Array E Int))
        (declare-const x E)
        (assert (= (select (as map.empty (Array E Int)) x) 7))
        (assert (= (select (as map.empty (Array E Int)) x) 8))
        (check-sat)
    "#;
    assert_never(
        smt,
        "sat",
        "unsat",
        "two selects of the SAME constant at the SAME index cannot differ; a \
         `sat` here means each occurrence minted a fresh internal default",
    );

    // Control: under a non-intercepted name the two equalities are genuinely
    // contradictory, and AY must not claim satisfiability there either.
    let control = smt.replace("map.empty", "g");
    assert_never(
        &control,
        "sat",
        "unsat",
        "control: `(= (select g x) 7)` and `(= (select g x) 8)` are contradictory",
    );
}

/// Reproducer 3 — `multiset.empty` under a Bool-only logic must never be
/// `unsat`.
///
/// Same interception, third spelling and third shape: the builtin empty
/// multiset reads 0 everywhere, so `(> (select … x) 0)` looks contradictory
/// while the declared constant is unconstrained. Pinned oracle z3 5.0.0: `sat`.
#[test]
fn test_declared_multiset_empty_never_yields_unsat() {
    let smt = r#"
        (set-logic BOOL)
        (declare-sort E 0)
        (declare-fun multiset.empty () (Array E Int))
        (declare-const x E)
        (assert (> (select (as multiset.empty (Array E Int)) x) 0))
        (check-sat)
    "#;
    assert_never(
        smt,
        "unsat",
        "sat",
        "`multiset.empty` is intercepted by name and read as the all-zero \
         multiset",
    );

    let control = smt.replace("multiset.empty", "g");
    assert_never(
        &control,
        "unsat",
        "sat",
        "control: an unconstrained Int-valued array can exceed 0 at x",
    );
}

/// Non-vacuity guard for the three reproducers above.
///
/// A one-sided "never publish X" guard passes trivially if the fixture stops
/// reaching the solver for an unrelated reason. Pin that the shapes are still
/// LIVE by running each one under an ordinary, non-intercepted name `g`: those
/// controls must be REFUSED BY NOTHING — AY must accept the script and reach a
/// verdict line. (Which line is not pinned here: AY answers `unknown` on the
/// uninterpreted-sort array controls today, and tightening that is a solver
/// question, not a naming question. What matters is that the fixture still
/// elaborates and still reaches `check-sat`, so the reserved-name divergence
/// above is about the NAME and nothing else.)
#[test]
fn test_reproducer_controls_are_accepted_and_reach_check_sat() {
    for smt in [
        r#"(set-logic BOOL)
           (declare-sort E 0)
           (declare-fun g () (Array E Bool))
           (declare-const x E)
           (assert (select g x))
           (check-sat)"#,
        r#"(set-logic BOOL)
           (declare-sort E 0)
           (declare-fun g () (Array E Int))
           (declare-const x E)
           (assert (= (select g x) 7))
           (assert (= (select g x) 8))
           (check-sat)"#,
        r#"(set-logic BOOL)
           (declare-sort E 0)
           (declare-fun g () (Array E Int))
           (declare-const x E)
           (assert (> (select g x) 0))
           (check-sat)"#,
    ] {
        assert!(
            verdict_or_refusal(smt).is_some(),
            "control fixture no longer elaborates and reaches `check-sat`; the \
             reserved-name reproducers it backs are no longer known to be \
             live\nSMT2:\n{smt}"
        );
    }
}
