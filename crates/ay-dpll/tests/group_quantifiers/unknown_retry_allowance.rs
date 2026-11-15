// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The retries that follow an `unknown` first pass keep the verdicts they
//! exist for, and leave the first pass's answer when they find none.
//!
//! After a pass that ends `unknown` the solver re-solves the query: with the
//! deep-QE pre-pass armed, and, when the proof recorder is shed (competition
//! posture), with the recorder armed. A re-solve of an unchanged problem now
//! runs under a work allowance taken from the pass before it, with a floor.
//! These tests pin the two things that allowance must not change on small
//! queries: a refutation only the armed retry can publish is still published,
//! and an `unknown` still carries the candidate model of the search.

use ay_dpll::{CandidateModelPolicy, Executor};
use ay_frontend::parse;
use ntest::timeout;

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"))
}

/// `f` is positive on positive arguments; `goal` speaks about `f a`.
fn positive_function_query(goal: &str) -> String {
    format!(
        "(set-logic UFLRA)
         (declare-fun f (Real) Real)
         (declare-fun a () Real)
         (assert (< 0.0 a))
         {goal}
         (assert (forall ((x Real)) (=> (< 0.0 x) (< 0.0 (f x)))))
         (check-sat)"
    )
}

/// The shed first pass ends `unknown` on this instantiation-driven
/// refutation; only the trace-armed retry publishes it. Its allowance must
/// let it.
#[test]
#[timeout(60_000)]
fn the_armed_retry_still_publishes_an_instantiation_driven_refutation() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = run(
        &mut exec,
        &positive_function_query("(assert (not (< 0.0 (f a))))"),
    );
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
}

/// The twin, one line different: `f a` positive is what the axiom says, so
/// the query is satisfiable and no retry may refute it.
#[test]
#[timeout(60_000)]
fn the_satisfiable_twin_is_not_refuted_by_any_retry() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = run(
        &mut exec,
        &positive_function_query("(assert (< 0.0 (f a)))"),
    );
    let answer = outputs.last().map(String::as_str);
    assert!(
        matches!(answer, Some("sat" | "unknown")),
        "a satisfiable query must never answer unsat: {outputs:?}"
    );
}

/// A boxed-integer prelude, two labels and a goal, as a program verifier
/// sends them. `bound` is the one assertion that differs between the twins.
fn labelled_query(bound: &str) -> String {
    format!(
        "(declare-sort Poly 0)
         (declare-fun I (Int) Poly)
         (declare-fun %I (Poly) Int)
         (declare-fun tr (Poly Poly) Bool)
         (assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)))))
         (assert (forall ((p Poly) (q Poly)) (! true :pattern ((tr p q)))))
         (push)
         (declare-const a Int)
         (declare-const L0 Bool)
         (declare-const L1 Bool)
         {bound}
         (assert (not (and (=> L1 (< (%I (I a)) 1)) (=> L0 (> (%I (I a)) 0)))))
         (check-sat)"
    )
}

/// The posture of a z3-compatible client: recorder shed, candidate model
/// published after `unknown`.
fn client_executor() -> Executor {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_candidate_model_policy(CandidateModelPolicy::PublishAfterUnknown);
    exec
}

/// The injectivity of `I` makes `Poly` infinite, which the ground search does
/// not see, so every pass ends `unknown`. The vacuous `tr` declaration makes
/// the deep-QE retry run although it eliminates nothing, and the shed posture
/// makes the armed retry run after it: two re-solves of the same problem.
/// The answer and its candidate model must be the ones a client reads the
/// failing assertion from: `L0` true, `L1` false.
#[test]
#[timeout(60_000)]
fn an_unknown_after_both_retries_still_names_the_failing_assertion() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &labelled_query("(assert (<= (%I (I a)) 0))"));
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "{outputs:?}"
    );
    let model = run(&mut exec, "(get-model)").pop().unwrap_or_default();
    assert!(model.contains("(define-fun L0 () Bool true)"), "{model}");
    assert!(model.contains("(define-fun L1 () Bool false)"), "{model}");
}

/// The twin, one line different: no integer lies strictly between 0 and 1,
/// so the query is unsatisfiable and is refuted on the first pass.
#[test]
#[timeout(60_000)]
fn the_unsatisfiable_twin_of_the_labelled_query_is_refuted() {
    let mut exec = client_executor();
    let outputs = run(
        &mut exec,
        &labelled_query("(assert (and (< 0 (%I (I a))) (< (%I (I a)) 1)))"),
    );
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
}
