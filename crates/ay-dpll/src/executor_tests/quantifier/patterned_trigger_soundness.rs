// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for user-`:pattern`-annotated universal quantifiers
//! (P0 patterned-forall wrong-sat).
//!
//! A user `:pattern` must only ever RESTRICT which ground terms E-matching
//! instantiates a `forall` at — it may NEVER be trusted as a proof that the
//! quantifier is fully covered (a "vacuous" / trigger-complete SAT). The
//! confirmed wrong-sat:
//!
//! ```smtlib
//! (declare-fun f (Int) Int)
//! (assert (forall ((x Int)) (! (>= (f (+ x 1)) 0) :pattern ((f (+ x 1))))))
//! (assert (= (f 0) (- 0 1)))     ; f(0) = -1
//! (check-sat)                     ; TRUTH: unsat  (x = -1 ⇒ f(0) >= 0 clashes)
//! ```
//!
//! The trigger `f(+ x 1)` never SYNTACTICALLY matches the ground `f 0`, so
//! E-matching creates zero instances. The engine used to read the missing
//! interpreted symbol `+` (no ground occurrence) as proof that the `forall`
//! was vacuously E-match-complete and emitted the ground SAT — a wrong-sat,
//! because `+` is INTERPRETED and the trigger term `(+ x 1)` semantically
//! ranges over the whole integer domain (`x := -1` gives `f 0`). The fix
//! routes such a `forall` through the MBQI/CEGQI counter-check instead: it
//! must NEVER come back SAT.

use super::*;

fn solve_one(input: &str) -> String {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    outputs.last().cloned().unwrap_or_default()
}

/// REPRO 1 (unary, patterned): `forall x. [f(x+1)] f(x+1) >= 0` with
/// `f(0) = -1`. UNSAT (instantiate x = -1). The user pattern must never let
/// this be reported SAT; refutation to `unsat` is ideal, `unknown` acceptable.
#[test]
fn patterned_shifted_trigger_unary_never_sat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (>= (f (+ x 1)) 0) :pattern ((f (+ x 1))))))
        (assert (= (f 0) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "patterned forall f(x+1)>=0 with f(0)=-1 is UNSAT; a user :pattern must \
         never certify a trigger-vacuous SAT"
    );
}

/// REPRO 2 (curried, patterned): the same wrong-sat shape through a
/// two-argument `f(a, x+1)`, pinning that the fix is not unary-specific.
#[test]
fn patterned_shifted_trigger_curried_never_sat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int Int) Int)
        (declare-const a Int)
        (assert (forall ((x Int)) (! (>= (f a (+ x 1)) 0) :pattern ((f a (+ x 1))))))
        (assert (= (f a 0) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "curried patterned forall f(a,x+1)>=0 with f(a,0)=-1 is UNSAT; a user \
         :pattern must never certify a trigger-vacuous SAT"
    );
}

/// The ideal outcome for REPRO 1: the MBQI counter-check has the falsifying
/// witness (`-1` is a ground term, from `f(0) = -1`), so the engine should
/// DECIDE `unsat`, exactly like the no-pattern control below.
#[test]
fn patterned_shifted_trigger_unary_is_unsat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (>= (f (+ x 1)) 0) :pattern ((f (+ x 1))))))
        (assert (= (f 0) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unsat",
        "the counter-check has the witness x=-1 and must refute to unsat"
    );
}

/// CONTROL: the SAME formula WITHOUT the `:pattern` annotation. It already
/// went through MBQI/CEGQI and answered `unsat`; the fix must not perturb it.
#[test]
fn shifted_trigger_no_pattern_control_stays_unsat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f (+ x 1)) 0)))
        (assert (= (f 0) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "unsat", "no-pattern control must stay unsat");
}

/// A patterned UNSAT case where the MBQI counter-check CANNOT reach the
/// falsifying witness by ground candidates alone (`f(3) = -5` is falsified at
/// `x = 2`, but `2` is not a ground term). The fix must still fail CLOSED —
/// never SAT. `unknown` is the sound outcome here; the wrong answer would be
/// `sat` (the pre-fix MBQI-"no counterexample found" pass-through).
#[test]
fn patterned_shifted_trigger_witness_not_ground_never_sat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (>= (f (+ x 1)) 0) :pattern ((f (+ x 1))))))
        (assert (= (f 3) (- 0 5)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "patterned forall f(x+1)>=0 with f(3)=-5 is UNSAT; MBQI failing to find \
         the ground witness must degrade to unknown, never trust a SAT"
    );
}

/// A patterned GENUINELY-SAT case (`f(3) = 5`): the model
/// `f := λk. if k=3 then 5 else 0` satisfies `forall x. f(x+1) >= 0`. The fix
/// fails CLOSED (the incomplete MBQI ground-candidate check is not trusted to
/// certify SAT for a trigger-uninstantiated `forall`), so this is `unknown` —
/// but it must NEVER be reported `unsat` (that would be a wrong-unsat on a
/// satisfiable problem).
#[test]
fn patterned_shifted_trigger_genuinely_sat_never_unsat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (>= (f (+ x 1)) 0) :pattern ((f (+ x 1))))))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "unsat",
        "patterned forall f(x+1)>=0 with f(3)=5 is SATISFIABLE; the fail-closed \
         fix must never report unsat"
    );
}
