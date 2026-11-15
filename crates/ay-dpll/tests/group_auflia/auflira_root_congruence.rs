// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Root equalities of the AUFLIRA window make one atom of two.
//!
//! The query is ground and has the shape a program verifier's axioms leave
//! behind once they are instantiated: a boxed sort with its round trip
//! `x = unbox(box(x))`, an `add` function defined by `+`, a `clip` function
//! with its range and its identity on the range, and a chain of values each
//! the clipped successor of the one before. Every value is also compared
//! through its box round trip, `(or (< (unbox (box x)) c) (<= c x))`: a
//! tautology once the two terms are read as one, and two free atoms per
//! clause until then.
//!
//! The lazy split loop hands the theory a complete assignment and learns one
//! lemma per round. Without the rewrite the refutation of the six-step chain
//! took 427 round trips and the model of its twin 476; with the window
//! written over class representatives they take 2 and 39 (measured in the
//! posture that publishes no proof, where the rewrite applies). The tests
//! pin the round trips, not the time.
//!
//! The twin differs in one constant and is satisfiable (z3 4.12.5: `unsat`
//! and `sat`). Its model is validated against the assertions as written, so
//! the twin also pins that the rewritten window keeps their models.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"))
}

/// `steps` clipped increments from `v0`, none of which can wrap, so the last
/// value is `v0 + steps`. The goal denies that it is `v0 + claimed`.
fn boxed_chain_query(steps: usize, windows: usize, claimed: usize) -> String {
    let mut script = String::from(
        "(declare-sort Box 0)
         (declare-fun box (Int) Box)
         (declare-fun unbox (Box) Int)
         (declare-fun hi (Int) Int)
         (declare-fun clip (Int Int) Int)
         (declare-fun add (Int Int) Int)
         (declare-fun weight (Box) Real)
         (assert (= (hi 8) 256))\n",
    );
    for value in 0..=steps {
        script.push_str(&format!("(declare-const v{value} Box)\n"));
    }
    script.push_str("(assert (<= 0.0 (weight v0)))\n(assert (<= 0 (unbox v0)))\n");
    for value in 0..=steps {
        let x = format!("(unbox v{value})");
        script.push_str(&format!("(assert (= {x} (unbox (box {x}))))\n"));
        for window in 0..windows {
            let bound = 3 + 7 * window + value;
            script.push_str(&format!(
                "(assert (or (< (unbox (box {x})) {bound}) (<= {bound} {x})))\n"
            ));
        }
    }
    for value in 0..steps {
        let x = format!("(unbox v{value})");
        let next = format!("(add {x} 1)");
        script.push_str(&format!(
            "(assert (= {next} (+ {x} 1)))
             (assert (and (<= 0 (clip 8 {next})) (< (clip 8 {next}) (hi 8))))
             (assert (=> (and (<= 0 {next}) (< {next} (hi 8))) (= {next} (clip 8 {next}))))
             (assert (= (unbox v{}) (clip 8 {next})))
             (assert (< {x} 200))\n",
            value + 1
        ));
    }
    script.push_str(&format!(
        "(assert (not (= (unbox v{steps}) (+ (unbox v0) {claimed}))))\n(check-sat)\n"
    ));
    script
}

/// The posture of a z3-compatible client: no proof is published, so the
/// window is rewritten.
fn client_executor() -> Executor {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec
}

fn round_trips(exec: &Executor) -> u64 {
    exec.statistics()
        .get_int("dpll.round_trips")
        .unwrap_or_else(|| panic!("the split loop records its round trips"))
}

/// The goal denies `v6 = v0 + 6`, which the chain entails.
#[test]
#[timeout(120_000)]
fn a_boxed_chain_is_refuted_in_a_handful_of_round_trips() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &boxed_chain_query(6, 12, 6));
    assert_eq!(outputs, vec!["unsat"]);
    let trips = round_trips(&exec);
    assert!(
        trips <= 40,
        "the refutation took {trips} round trips; it took 427 before the window \
         was written over class representatives and 2 after"
    );
}

/// The twin, one constant different: the goal denies `v6 = v0 + 7`, which is
/// false in every model of the chain, so the query is satisfiable.
#[test]
#[timeout(120_000)]
fn the_twin_whose_goal_is_true_keeps_its_model() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &boxed_chain_query(6, 12, 7));
    assert_eq!(outputs, vec!["sat"]);
    let trips = round_trips(&exec);
    assert!(
        trips <= 160,
        "the model took {trips} round trips; it took 476 before the rewrite and 39 after"
    );
}

/// The posture that checks its refutations does not rewrite the window; the
/// verdicts are the same.
#[test]
#[timeout(120_000)]
fn the_checked_posture_gives_the_same_two_verdicts() {
    let mut exec = Executor::new();
    assert!(
        !run(&mut exec, &boxed_chain_query(3, 4, 3))
            .iter()
            .any(|answer| answer == "sat"),
        "the entailed goal is never satisfiable"
    );
    let mut exec = Executor::new();
    assert!(
        !run(&mut exec, &boxed_chain_query(3, 4, 4))
            .iter()
            .any(|answer| answer == "unsat"),
        "the twin is never refuted"
    );
}

/// A query whose rewritten window has a model the evaluator cannot read the
/// assertions as written from: `(h u2)` is not a term of the rewritten
/// window (`u2` is read as `u0`), so `(Q (h u2))` has no value there.
/// `last` is the one line the twins differ in.
fn renamed_argument_query(last: &str) -> String {
    format!(
        "(declare-sort U 0)
         (declare-fun f (Int) Int)
         (declare-fun g (Int Int) Int)
         (declare-fun h (U) U)
         (declare-fun P (Int) Bool)
         (declare-fun Q (U) Bool)
         (declare-fun r (U) Real)
         (declare-const x0 Int)
         (declare-const u0 U)
         (declare-const u2 U)
         (assert (<= 0.0 (r u0)))
         (assert (= x0 0))
         (assert (= u0 u2))
         (assert (= (f 0) (- (f x0) (g x0 x0))))
         (assert (not (P (- (f x0) (g x0 x0)))))
         (assert (or (Q (h u2)) (P (f 0))))
         (assert {last})
         (check-sat)"
    )
}

/// `Q (h u2)` must hold and nothing forbids it (z3 4.12.5: `sat`). The model
/// of the rewritten window does not validate against the assertions as
/// written, so the query is solved on them and keeps its `sat`.
#[test]
#[timeout(120_000)]
fn a_model_the_rewrite_cannot_name_is_found_on_the_window_as_written() {
    let mut exec = client_executor();
    let outputs = run(
        &mut exec,
        &renamed_argument_query("(or (Q (h u0)) (< x0 (f x0)))"),
    );
    assert_eq!(outputs, vec!["sat"]);
}

/// The twin denies `Q (h u0)`, which the window entails (z3: `unsat`).
#[test]
#[timeout(120_000)]
fn the_twin_that_denies_the_renamed_atom_is_refuted() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &renamed_argument_query("(not (Q (h u0)))"));
    assert_eq!(outputs, vec!["unsat"]);
}
