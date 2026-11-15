// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The quantifier preprocessing pipeline (`ay_dpll::simplifier`) at the
//! quantified `check-sat` entry.
//!
//! # What it decides
//!
//! Shapes z3 5.1.0 decides with zero search (roadmap 2026-09-29, critic A):
//! a Skolemized goal whose premises contradict (AUFNIRA nasa), a universal
//! solved by qe-lite (LIA tptp `NUM917=1`), a DER chain over bit-vectors that
//! grounds a fixpoint check (UFBV wintersteiger), and a macro whose expansion
//! refutes a ground fact. Each is refuted in the `--z3-mode` posture
//! (`set_competition_mode(true)`), the only one in which the pipeline's
//! unjustified passes may run.
//!
//! # What must never happen
//!
//! Each elimination is checked against the capture and occurs conditions that
//! keep it an equivalence (or, for macros, satisfiability with a model
//! converter). The twins below are the shapes a wrong implementation gets
//! wrong: a DER substitution captured by an inner binder, a macro body
//! captured at an expansion site, qe-lite solving a non-unit integer
//! coefficient, and a refuted scoped window leaking past its `pop`. Every
//! twin runs in all four postures; z3 5.1.0 answers as stated on each.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

use super::hunt_quantifier_wrong_verdicts::{assert_never, solve, verdicts, Posture};

const BUDGET: Duration = Duration::from_secs(5);

/// AUFNIRA nasa shape: the negated goal's premises pin `a` to both 0 and 3.
const NASA_GOAL: &str = r#"
(set-logic AUFNIRA)
(declare-fun sigma () (Array Int (Array Int Real)))
(declare-fun f (Int Int) Real)
(assert (forall ((i Int) (j Int)) (= (f i j) (select (select sigma i) j))))
(assert (not (forall ((a Int) (b Int))
  (=> (and (= 0 a) (= 0 b))
      (=> (and (= 3 a) (= 4 b)) (= (f a b) 0.0))))))
(check-sat)
"#;

/// LIA tptp `NUM917=1`: qe-lite solves `u - w = v` for `w`.
const NUM917: &str = r#"
(set-logic LIA)
(assert (not (forall ((u Int) (v Int)) (exists ((w Int)) (= (- u w) v)))))
(check-sat)
"#;

/// UFBV fixpoint shape: DER walks the definitional chain to a ground check.
const BV_CHAIN: &str = r#"
(set-logic UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
  (=> (and (= a0 #x01)
           (= a1 (ite (bvult a0 #x64) (bvadd a0 a0) a0))
           (= a2 (ite (bvult a1 #x64) (bvadd a1 a0) a1)))
      (= (g a2) #x03))))
(assert (not (= (g #x03) #x03)))
(check-sat)
"#;

/// A macro whose expansion refutes a ground fact.
const MACRO_REFUTES: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (forall ((x Int)) (= (f x) (+ x 1))))
(assert (<= (f c) c))
(check-sat)
"#;

#[test]
fn z3_mode_refutes_the_zero_search_shapes() {
    for (name, smt) in [
        ("nasa goal", NASA_GOAL),
        ("NUM917=1", NUM917),
        ("bv chain", BV_CHAIN),
        ("macro", MACRO_REFUTES),
    ] {
        let results = solve(smt, Posture::Z3Mode, Some(BUDGET));
        assert_eq!(
            verdicts(&results),
            ["unsat"],
            "{name}: decided by the pipeline (a refutation, or a ground window); got {results:?}"
        );
        assert_never(name, smt, "sat");
    }
}

#[test]
fn the_refutation_is_the_pipelines_and_the_default_posture_skips_it() {
    let commands = parse(NUM917).expect("parse");
    let mut shed = Executor::new();
    shed.set_timeout(Some(BUDGET));
    shed.set_competition_mode(true);
    let got = shed.execute_all(&commands).expect("execute");
    assert_eq!(verdicts(&got), ["unsat"], "{got:?}");
    assert_eq!(shed.statistics().get_int("simplifier.refuted"), Some(1));

    let mut default = Executor::new();
    default.set_timeout(Some(BUDGET));
    let _ = default.execute_all(&commands).expect("execute");
    assert_eq!(default.statistics().get_int("simplifier.refuted"), None);
    assert_eq!(
        default.statistics().get_int("simplifier.qe-lite.skipped"),
        Some(1),
        "the default posture must refuse every unjustified pass"
    );
}

/// DER under a capturing inner binder: `x := y` substituted into `∀y. x = y`
/// must rename the inner `y`. Correct: `∀y'. y = y'`, false. Captured:
/// `∀y. y = y`, true. z3 5.1.0: `unsat`.
const DER_CAPTURE: &str = r#"
(set-logic UFLIA)
(declare-fun y () Int)
(assert (forall ((x Int)) (or (not (= x y)) (forall ((y Int)) (= x y)))))
(check-sat)
"#;

/// A macro expanded under a binder named like its free constant `k`.
/// Correct: `∀k'. k' + k > k'`, i.e. `k > 0`, sat. Captured: `∀k. k + k > k`,
/// false. z3 5.1.0: `sat`.
const MACRO_CAPTURE: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun k () Int)
(assert (forall ((x Int)) (= (f x) (+ x k))))
(assert (forall ((k Int)) (> (f k) k)))
(check-sat)
"#;

/// qe-lite must not solve `2w = v` over `Int` (v odd has no witness).
/// z3 5.1.0: `sat`.
const NON_UNIT_INT: &str = r#"
(set-logic LIA)
(assert (not (forall ((v Int)) (exists ((w Int)) (= (* 2 w) v)))))
(check-sat)
"#;

/// Over `Real` the same literal is solvable for every `v`. z3 5.1.0: `unsat`.
const NON_UNIT_REAL: &str = r#"
(set-logic LRA)
(assert (not (forall ((v Real)) (exists ((w Real)) (= (* 2.0 w) v)))))
(check-sat)
"#;

/// DER's satisfiable control: the axiom pins `p` only at `a`.
/// z3 5.1.0: `sat`.
const DER_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun p (Int) Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (forall ((x Int)) (or (not (= x a)) (p x))))
(assert (not (p b)))
(check-sat)
"#;

#[test]
fn capture_and_coefficient_twins_are_never_wrong() {
    assert_never("DER capture", DER_CAPTURE, "sat");
    assert_never("macro capture", MACRO_CAPTURE, "unsat");
    assert_never("non-unit Int coefficient", NON_UNIT_INT, "unsat");
    assert_never("non-unit Real coefficient", NON_UNIT_REAL, "sat");
    assert_never("DER satisfiable control", DER_SAT, "unsat");
    let got = solve(NON_UNIT_REAL, Posture::Z3Mode, Some(BUDGET));
    assert_eq!(verdicts(&got), ["unsat"], "qe-lite over Real: {got:?}");
}

/// A refuted scoped window is restored at `pop`: the second query is sat.
/// z3 5.1.0: `unsat`, `sat`.
const SCOPED_MACRO: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 5))
(push 1)
(assert (forall ((x Int)) (= (f x) (+ x 1))))
(check-sat)
(pop 1)
(check-sat)
"#;

#[test]
fn a_scoped_refutation_does_not_outlive_its_pop() {
    let got = solve(SCOPED_MACRO, Posture::Z3Mode, Some(BUDGET));
    assert_eq!(verdicts(&got), ["unsat", "sat"], "{got:?}");
    for posture in [Posture::Plain, Posture::Authored, Posture::SelfCheck] {
        let got = solve(SCOPED_MACRO, posture, Some(BUDGET));
        let v = verdicts(&got);
        assert!(
            v.len() == 2 && v[0] != "sat" && v[1] != "unsat",
            "{posture:?}: {got:?}"
        );
    }
}

/// qe-lite grounds the existential and value propagation rewrites
/// `g(3(b + c))` to `g(3c)`; the rewritten window is satisfiable, but its
/// model has no value for the authored application `g(3b + 3c)`, so no gate
/// confirms that SAT against the authored assertions. The unrewritten
/// route decides it (#simplifier-sat-fallback). z3 5.1.0: `sat`.
const REWRITTEN_SAT_UNCONFIRMED: &str = r#"
(set-logic UFNRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-fun h (Real) Real)
(declare-fun g (Real) Real)
(assert (> (g (* 3.0 (+ b c))) 1.0))
(assert (= b 0.0))
(assert (exists ((x Real)) (and (= (- b x) (h a)) (or (= b (+ b x)) (< 0.0 x)))))
(check-sat)
"#;

#[test]
fn an_unconfirmed_rewritten_sat_falls_back_to_the_unrewritten_route() {
    let commands = parse(REWRITTEN_SAT_UNCONFIRMED).expect("parse");
    let mut shed = Executor::new();
    shed.set_timeout(Some(BUDGET));
    shed.set_competition_mode(true);
    let got = shed.execute_all(&commands).expect("execute");
    assert_eq!(verdicts(&got), ["sat"], "{got:?}");
    assert_eq!(
        shed.statistics().get_int("simplifier.fallback"),
        Some(1),
        "the rewritten window's SAT is not confirmable; the fallback decides"
    );
    assert_never("rewritten SAT fallback", REWRITTEN_SAT_UNCONFIRMED, "unsat");
}

/// The same rewrite under a Boolean UF `p`: the authored `p(3b + 3c)` has no
/// literal of its own, but the committed `p(3c)` is congruent to it (equal
/// argument values), and the evaluator reads that literal
/// (`find_congruent_bool_app`). This was the fallback fixture until the
/// congruence read landed (2026-10-02 LNH repair, audit V1): the rewritten
/// window's SAT is now confirmed directly. z3 5.1.0: `sat`.
const REWRITTEN_SAT_CONFIRMED_BY_CONGRUENCE: &str = r#"
(set-logic UFNRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-fun h (Real) Real)
(declare-fun p (Real) Bool)
(assert (p (* 3.0 (+ b c))))
(assert (= b 0.0))
(assert (exists ((x Real)) (and (= (- b x) (h a)) (or (= b (+ b x)) (< 0.0 x)))))
(check-sat)
"#;

#[test]
fn a_rewritten_sat_over_a_congruent_predicate_is_confirmed_directly() {
    let commands = parse(REWRITTEN_SAT_CONFIRMED_BY_CONGRUENCE).expect("parse");
    let mut shed = Executor::new();
    shed.set_timeout(Some(BUDGET));
    shed.set_competition_mode(true);
    let got = shed.execute_all(&commands).expect("execute");
    assert_eq!(verdicts(&got), ["sat"], "{got:?}");
    assert_eq!(
        shed.statistics().get_int("simplifier.fallback"),
        None,
        "the congruent literal confirms the rewritten window's SAT"
    );
    assert_never(
        "rewritten SAT over a congruent predicate",
        REWRITTEN_SAT_CONFIRMED_BY_CONGRUENCE,
        "unsat",
    );
}
