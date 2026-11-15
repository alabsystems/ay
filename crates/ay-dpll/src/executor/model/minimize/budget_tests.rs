// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The minimization budget ends minimization; it never rolls it back.

use ay_core::TermId;
use num_bigint::BigInt;

use super::MinimizationBudget;
use crate::executor::Executor;

fn unlimited() -> MinimizationBudget {
    MinimizationBudget::with_checks(usize::MAX)
}

/// `x` inflated to 1,000,000 in a model of `(>= x 0)`: shrinkable.
fn inflated_lia_model() -> (Executor, TermId, BigInt) {
    let commands = ay_frontend::parse(
        "(set-option :produce-models true)\
         (declare-const x Int)(assert (>= x 0))(check-sat)",
    )
    .expect("valid SMT-LIB");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs[0], "sat");
    let x = exec
        .ctx
        .symbol_info("x")
        .and_then(|info| info.term)
        .expect("declared x term");
    let inflated = BigInt::from(1_000_000);
    let lia = exec
        .last_model
        .as_mut()
        .and_then(|model| model.lia_model.as_mut())
        .expect("lia model present");
    lia.values.retain(|term, _| *term == x);
    lia.values.insert(x, inflated.clone());
    (exec, x, inflated)
}

fn lia_value(exec: &Executor, x: TermId) -> BigInt {
    exec.last_model
        .as_ref()
        .and_then(|model| model.lia_model.as_ref())
        .and_then(|lia| lia.values.get(&x))
        .cloned()
        .expect("x in the model")
}

/// Minimization is cosmetic, so its work is budgeted: a spent budget ENDS it
/// (keeping what the gate confirms) and never waits for the solve deadline.
/// With `-model`, QF_BV Sage2 `bench_12061` minimized until the deadline and
/// lost its `sat`.
#[test]
fn a_spent_minimization_budget_ends_minimization_and_keeps_the_valid_model() {
    // No check allowed: nothing is tried, the model is the solver's.
    let (mut exec, x, inflated) = inflated_lia_model();
    exec.minimize_model_sat_preserving_with_stop(&mut MinimizationBudget::with_checks(0), |_| {
        false
    });
    assert_eq!(lia_value(&exec, x), inflated);

    // One check: the first candidate is tried and, being valid, kept -- the
    // budget's end is not a stop that rolls the pass back.
    let (mut exec, x, inflated) = inflated_lia_model();
    let mut one = MinimizationBudget::with_checks(1);
    exec.minimize_model_sat_preserving_with_stop(&mut one, |_| false);
    assert!(one.exhausted());
    let shrunk = lia_value(&exec, x);
    assert!(shrunk < inflated, "the one allowed candidate is kept");

    // The unlimited control shrinks at least as far.
    let (mut exec, x, _) = inflated_lia_model();
    exec.minimize_model_sat_preserving_with_stop(&mut unlimited(), |_| false);
    assert!(lia_value(&exec, x) <= shrunk);
}
