// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A Boolean variable under an uninterpreted function reaches the E-graph of
//! the lazy AUFLIRA split loop.
//!
//! `t = (wrap g)` with `g` forced false by two clauses, and the goal denies
//! `t = (wrap false)`. The refutation is one congruence step once the theory
//! knows that `g` is false. `g` is a SAT variable but not a theory atom by
//! shape, and the loop handed the theory theory atoms only: the theory
//! accepted the assignment, the model gate rejected the model, and the
//! answer was `unknown` (z3 4.12.5: `unsat`).
//!
//! The twin denies `t = (wrap true)` instead and is satisfiable.
//!
//! `weight` and `tag` only route the query: a Real-valued function and an
//! Int term put it in the Int and Real lane, which runs the lazy split loop.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"))
}

fn wrapped_flag_query(denied: bool) -> String {
    format!(
        "(declare-sort U 0)
         (declare-fun wrap (Bool) U)
         (declare-fun weight (U) Real)
         (declare-fun tag (Int) U)
         (declare-fun same (U U U) Bool)
         (declare-const t U)
         (declare-const g Bool)
         (declare-const h Bool)
         (assert (or (not g) h))
         (assert (or (not g) (not h)))
         (assert (= t (wrap g)))
         (assert (same (tag 32) t t))
         (assert (not (= t (wrap {denied}))))
         (check-sat)"
    )
}

/// The posture of a z3-compatible client: no proof is published.
fn client_executor() -> Executor {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec
}

#[test]
#[timeout(60_000)]
fn a_flag_the_clauses_force_false_is_false_under_the_function() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &wrapped_flag_query(false));
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn the_twin_that_denies_the_other_value_has_a_model() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &wrapped_flag_query(true));
    assert_eq!(outputs, vec!["sat"]);
}

/// The checked posture is not handed the values. It may not know the answer,
/// and it does not call the refutable query satisfiable.
#[test]
#[timeout(60_000)]
fn the_checked_posture_never_calls_the_refutable_query_satisfiable() {
    let mut exec = Executor::new();
    let outputs = run(&mut exec, &wrapped_flag_query(false));
    assert_ne!(outputs, vec!["sat"]);
    let mut exec = Executor::new();
    let outputs = run(&mut exec, &wrapped_flag_query(true));
    assert_ne!(outputs, vec!["unsat"]);
}
