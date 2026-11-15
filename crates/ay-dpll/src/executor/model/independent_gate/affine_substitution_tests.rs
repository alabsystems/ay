// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified model gate on universals whose body is nonlinear as written
//! but linear once the model's value is substituted for the free constant
//! (#qmv-affine-route). Controlled candidates isolate the gate from search:
//! the same authored root gets a model that satisfies it and one that does
//! not, and a body that stays nonlinear in its binder must never confirm on a
//! model that falsifies it.

#![cfg(test)]

use ay_frontend::parse;
use ay_lia::LiaModel;
use num_bigint::BigInt;

use super::*;

/// t1: `∀v. c·v − v = 0`, true exactly at `c = 1`.
const T1: &str = "(set-logic ALL)(declare-const c Int)\
    (assert (forall ((v Int)) (= (+ (* c v) (* (- 1) v)) 0)))";

/// t6: `∀v. 0·v = c·v`, true exactly at `c = 0`.
const T6: &str = "(set-logic ALL)(declare-const c Int)\
    (assert (forall ((v Int)) (= (* 0 v) (* c v))))";

/// Nonlinear in the binder after substitution: `v = 0` falsifies it at every
/// `c`.
const SQUARE_POSITIVE: &str = "(set-logic ALL)(declare-const c Int)\
    (assert (forall ((v Int)) (> (* c v v) 0)))";

/// Nonlinear in two binders after substitution: at `c = 1`, `x² − 2y² = 1`
/// has the solution `(3, 2)`, so the universal is false.
const PELL: &str = "(set-logic ALL)(declare-const c Int)\
    (assert (forall ((x Int) (y Int)) (not (= (- (* c x x) (* 2 y y)) 1))))";

fn candidate(source: &str, value: i64) -> Executor {
    let mut exec = Executor::new();
    let commands = parse(source).expect("valid source");
    let outputs = exec.execute_all(&commands).expect("load without solving");
    assert!(outputs.is_empty(), "fixtures must not run a query");
    exec.begin_external_decision_query(false);
    let mut values = DetHashMap::default();
    let c = exec.ctx.terms.mk_var("c", Sort::Int);
    values.insert(c, BigInt::from(value));
    let mut model = Model::empty();
    model.lia_model = Some(LiaModel { values });
    exec.last_model = Some(model);
    exec
}

fn check(source: &str, value: i64) -> QuantifiedModelCheck {
    let mut exec = candidate(source, value);
    let root = *exec.ctx.assertions.last().expect("quantified root");
    assert!(matches!(exec.ctx.terms.get(root), TermData::Forall(..)));
    exec.check_quantified_conjunct_against_model(root)
}

#[test]
fn substituted_affine_body_confirms_at_its_solution_and_refutes_elsewhere() {
    for (name, source, good, bad) in [("t1", T1, 1, 2), ("t6", T6, 0, 3)] {
        assert!(
            matches!(check(source, good), QuantifiedModelCheck::Confirmed),
            "{name}: c = {good} satisfies the universal"
        );
        assert!(
            matches!(check(source, bad), QuantifiedModelCheck::Refuted { .. }),
            "{name}: c = {bad} must be refuted, not merely left undecided"
        );
    }
}

#[test]
fn affine_confirmation_survives_the_public_funnel_and_refutation_fails_closed() {
    let mut exec = candidate(T1, 1);
    assert_eq!(
        exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    assert_eq!(
        exec.last_statistics
            .get_string("model_check_gate.quantified"),
        Some("confirmed")
    );
    let mut exec = candidate(T1, 2);
    assert_eq!(
        exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Unknown
    );
}

#[test]
fn body_nonlinear_after_substitution_never_confirms_a_falsifying_model() {
    // Pell at `c = 0` is `−2y² ≠ 1`, which holds: only `c = 1` falsifies it.
    for (name, source, falsifying) in [
        ("square", SQUARE_POSITIVE, &[0, 1][..]),
        ("pell", PELL, &[1][..]),
    ] {
        for &value in falsifying {
            let checked = check(source, value);
            assert!(
                !matches!(checked, QuantifiedModelCheck::Confirmed),
                "{name}: c = {value} falsifies the universal"
            );
        }
    }
}
