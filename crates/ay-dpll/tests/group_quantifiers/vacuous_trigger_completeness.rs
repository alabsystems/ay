// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end guards for dead explicit triggers (#verification-consumer lang/while_let).
//!
//! A *triggered* `forall` whose trigger symbol has NO ground occurrence in the
//! problem cannot be instantiated by E-matching. That is an instantiation fact,
//! not a semantic SAT certificate: the body can still be impossible at every
//! binder value, and `no_mbqi` quantifiers have no independent fallback. The
//! solver therefore fails closed unless another semantic certificate applies.
//!
//! These tests pin the conservative result and the cardinal soundness property:
//! a genuinely UNSAT problem must still decide `unsat`, and a satisfiable
//! problem must never flip to `unsat`.

use ntest::timeout;

/// A satisfiable dead-trigger problem currently has no independently
/// constructed total model, so the honest result is `unknown`.
#[test]
#[timeout(60_000)]
fn dead_trigger_ground_sat_fails_closed() {
    let smt = r#"
        (set-logic UF)
        (declare-sort Option 0)
        (declare-fun Some (Int) Option)
        (declare-fun logic_Some (Int) Option)
        (declare-fun is_opt (Option) Bool)
        (declare-const a Option)
        (assert (= a (Some 10)))
        (assert (is_opt (Some 10)))
        ; Dead axiom: logic_Some never appears in any ground term.
        (assert (forall ((v Int)) (! (is_opt (logic_Some v)) :pattern ((logic_Some v)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    let res = outputs
        .iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"));
    assert_eq!(
        res.map(String::as_str),
        Some("unknown"),
        "dead-trigger SAT needs a semantic certificate, got {outputs:?}"
    );
}

/// SOUNDNESS GUARD: a genuinely UNSAT problem whose contradiction is reached
/// WITHOUT the dead-trigger forall must still decide `unsat`. The vacuous rule
/// only affects the SAT-escalation path, so ground UNSAT is unchanged.
#[test]
#[timeout(60_000)]
fn vacuous_trigger_ground_unsat_still_unsat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort Option 0)
        (declare-fun Some (Int) Option)
        (declare-fun logic_Some (Int) Option)
        (declare-fun is_opt (Option) Bool)
        (declare-const a Option)
        (assert (= a (Some 10)))
        (assert (is_opt (Some 10)))
        (assert (not (is_opt a)))            ; contradicts is_opt(Some 10) via a = Some 10
        (assert (forall ((v Int)) (! (is_opt (logic_Some v)) :pattern ((logic_Some v)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    let res = outputs
        .iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"));
    assert_eq!(
        res.map(String::as_str),
        Some("unsat"),
        "ground UNSAT must stay unsat under the vacuous-trigger rule, got {outputs:?}"
    );
}

/// SOUNDNESS GUARD (the critical one): when the trigger symbol DOES occur in a
/// ground term, the forall is NOT vacuous — its instance is live and must be
/// used. Here the live universal `forall v. logic_Some(v) != logic_None` plus
/// the ground fact `x = logic_Some 3` and the negated goal `x = logic_None`
/// makes the problem UNSAT, and the solver must still find it. The vacuous rule
/// must NOT have suppressed this live instantiation (which would have left it
/// `unknown`/`sat` — a missed proof, not unsound, but a regression we guard).
#[test]
#[timeout(60_000)]
fn live_trigger_still_instantiates_to_unsat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort Option 0)
        (declare-fun logic_Some (Int) Option)
        (declare-const logic_None Option)
        (declare-const x Option)
        (assert (= x (logic_Some 3)))
        (assert (forall ((v Int)) (! (not (= (logic_Some v) logic_None)) :pattern ((logic_Some v)))))
        (assert (= x logic_None))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    let res = outputs
        .iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"));
    assert_eq!(
        res.map(String::as_str),
        Some("unsat"),
        "a LIVE trigger must still instantiate and prove unsat, got {outputs:?}"
    );
}

/// SOUNDNESS GUARD: a satisfiable problem carrying a dead-trigger forall must
/// NEVER be reported `unsat`. The negated-goal direction here is satisfiable
/// (no contradiction), so the only acceptable answers are `sat` or `unknown`.
#[test]
#[timeout(60_000)]
fn vacuous_trigger_satisfiable_never_unsat() {
    let smt = r#"
        (set-logic UF)
        (declare-sort Option 0)
        (declare-fun Some (Int) Option)
        (declare-fun logic_Some (Int) Option)
        (declare-fun is_opt (Option) Bool)
        (declare-const a Option)
        (declare-const b Option)
        (assert (= a (Some 10)))
        (assert (is_opt (Some 10)))
        ; b is unconstrained; goal direction stays satisfiable.
        (assert (not (= a b)))
        (assert (forall ((v Int)) (! (is_opt (logic_Some v)) :pattern ((logic_Some v)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    let res = outputs
        .iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"));
    assert_ne!(
        res.map(String::as_str),
        Some("unsat"),
        "a satisfiable dead-trigger problem must never be reported unsat, got {outputs:?}"
    );
}
