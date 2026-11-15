// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A counterexample's steps agree with its validated ground derivation: the
//! verifier restates steps that claim another trace, and the exporter refuses
//! a trace-validity obligation they contradict.
//!
//! Measured on ae8cb6ed5: for a problem whose abort location preprocessing
//! inlines into the query, the back-translated counterexample carried 7 steps
//! and a ground derivation of 8 states that validates on the original clauses.
//! `ay --stats` exported `trace-validity-depth-6` (`expected-result: sat`)
//! read off the 7 steps, z3 answered `unsat`, and `--strict-proofs` shipped
//! `unsat` because STEP D confirmed the derivation.

use super::super::{Counterexample, CounterexampleStep};
use crate::ground_derivation::{GroundDerivation, GroundDerivationStep};
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::smt::SmtValue;
use crate::{ActionId, ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar};
use crate::{ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;

fn var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

/// `P(0).  P(x) /\ y = x + 1 => P(y) [action Step].  P(x) /\ x >= 2 => false.`
/// UNSAFE: `P(0), P(1), P(2)`, then the query.
fn counting_problem() -> (ChcProblem, ActionId) {
    counting_problem_from(ChcExpr::eq(var("x"), ChcExpr::Int(0)))
}

/// [`counting_problem`] with the initial states `P(x) <= init`.
fn counting_problem_from(init: ChcExpr) -> (ChcProblem, ActionId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let step = problem.declare_action("Step");
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    problem.add_clause_with_action(
        HornClause::new(
            ClauseBody::new(
                vec![(p, vec![var("x")])],
                Some(ChcExpr::eq(
                    var("y"),
                    ChcExpr::add(var("x"), ChcExpr::Int(1)),
                )),
            ),
            ClauseHead::Predicate(p, vec![var("y")]),
        ),
        step,
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("x")])],
            Some(ChcExpr::ge(var("x"), ChcExpr::Int(2))),
        ),
        ClauseHead::False,
    ));
    (problem, step)
}

fn env(pairs: &[(&str, i128)]) -> FxHashMap<String, SmtValue> {
    pairs
        .iter()
        .map(|(name, value)| ((*name).to_string(), SmtValue::Int(*value)))
        .collect()
}

/// The ground derivation of `false` through `P(0), P(1), ..., P(last)`.
fn counting_derivation(last: i128) -> GroundDerivation {
    let mut steps = vec![GroundDerivationStep {
        clause_index: 0,
        env: env(&[("x", 0)]),
        premises: vec![],
    }];
    for x in 0..last {
        steps.push(GroundDerivationStep {
            clause_index: 1,
            env: env(&[("x", x), ("y", x + 1)]),
            premises: vec![steps.len() - 1],
        });
    }
    steps.push(GroundDerivationStep {
        clause_index: 2,
        env: env(&[("x", last)]),
        premises: vec![steps.len() - 1],
    });
    let query_step = steps.len() - 1;
    GroundDerivation { steps, query_step }
}

/// A counterexample whose steps claim `P(values[0]), P(values[1]), ...`.
fn claimed(problem: &ChcProblem, values: &[i64], derivation: GroundDerivation) -> Counterexample {
    let predicate = problem.predicates()[0].id;
    let name = crate::lemma_hints::canonical_var_name(predicate, 0);
    let steps = values
        .iter()
        .map(|value| {
            CounterexampleStep::new(predicate, [(name.clone(), *value)].into_iter().collect())
        })
        .collect();
    Counterexample::new(steps).with_ground_derivation(derivation)
}

fn values(cex: &Counterexample) -> Vec<Option<i64>> {
    cex.steps
        .iter()
        .map(|step| step.assignments.get("__p0_a0").copied())
        .collect()
}

fn exported(problem: &ChcProblem, cex: &Counterexample) -> Result<String, String> {
    match cex.trace_validity_replay_obligations(problem) {
        Ok(obligations) => Ok(obligations
            .iter()
            .map(|obligation| obligation.name.clone())
            .collect::<Vec<_>>()
            .join(",")),
        Err(error) => Err(error.to_string()),
    }
}

/// A counterexample built from a derivation alone publishes the derivation's
/// trace: restating needs claimed steps to compare with, and there are none.
#[test]
fn a_derivation_alone_is_traced_as_the_states_it_derives() {
    let (problem, step) = counting_problem();
    let derivation = counting_derivation(2);
    crate::ground_derivation::validate_ground_derivation(&problem, &derivation)
        .expect("setup: the derivation validates");
    assert!(
        Counterexample::new(Vec::new())
            .restated_by_derivation(&problem, &derivation)
            .is_none(),
        "no steps, nothing to restate"
    );

    let traced = Counterexample::traced_by_derivation(&problem, &derivation)
        .expect("a linear derivation derives a trace");
    assert_eq!(values(&traced), vec![Some(0), Some(1), Some(2)]);
    assert_eq!(
        traced
            .steps
            .iter()
            .map(|step| step.clause_index)
            .collect::<Vec<_>>(),
        vec![Some(0), Some(1), Some(1)]
    );
    assert_eq!(traced.steps[1].action_id, Some(step));
    assert!(traced.ground_derivation.is_some());
}

/// The bug's shape: steps that stop one state short of the derivation are
/// restated as the derivation's trace, with its clauses and action tags.
#[test]
fn steps_short_of_the_validated_derivation_are_restated_as_its_trace() {
    let (problem, step) = counting_problem();
    let derivation = counting_derivation(2);
    crate::ground_derivation::validate_ground_derivation(&problem, &derivation)
        .expect("setup: the derivation validates");
    let short = claimed(&problem, &[0, 1], derivation.clone());

    let restated = short
        .restated_by_derivation(&problem, &derivation)
        .expect("steps that claim another trace are restated");
    assert_eq!(values(&restated), vec![Some(0), Some(1), Some(2)]);
    assert_eq!(
        restated
            .steps
            .iter()
            .map(|step| (step.clause_index, step.action_id))
            .collect::<Vec<_>>(),
        vec![
            (Some(0), None),
            (Some(1), Some(step)),
            (Some(1), Some(step))
        ]
    );
    assert!(restated.witness.is_none());
    assert!(restated.has_ground_derivation());
    assert_eq!(
        exported(&problem, &restated).as_deref(),
        Ok("trace-validity-depth-2")
    );
}

/// Defense in depth at the exporter: whichever path built it, a trace that
/// contradicts the counterexample's own validated derivation is not exported
/// as `expected-result: sat` evidence (its own pins decide nothing here).
#[test]
fn the_exporter_refuses_steps_short_of_the_validated_derivation() {
    let (problem, _) = counting_problem();
    let short = claimed(&problem, &[0, 1], counting_derivation(2));
    let error = exported(&problem, &short).expect_err("a one-short trace must not export");
    assert!(error.contains("derivation derives 3 states"), "{error}");
}

/// A pin the obligation's own evaluation refutes is refused first, with the
/// message the 069f4e5f4 guard gave (time 0 claims `P(5)`, init pins 0).
#[test]
fn a_pin_the_obligation_refutes_is_refused_as_before() {
    let (problem, _) = counting_problem();
    let wrong = claimed(&problem, &[5, 1, 2], counting_derivation(2));
    let error = exported(&problem, &wrong).expect_err("a refuted pin must not export");
    assert!(
        error.contains("ground-evaluate the depth-2 obligation to false"),
        "{error}"
    );
}

/// A pin the evaluation cannot decide (init admits `P(0)` and `P(1)`) but the
/// validated derivation does not derive (it starts at `P(0)`) is refused too:
/// the steps are not the trace that was verified.
#[test]
fn the_exporter_refuses_a_pin_the_validated_derivation_does_not_derive() {
    let (problem, _) = counting_problem_from(ChcExpr::and(
        ChcExpr::ge(var("x"), ChcExpr::Int(0)),
        ChcExpr::le(var("x"), ChcExpr::Int(1)),
    ));
    let derivation = counting_derivation(2);
    crate::ground_derivation::validate_ground_derivation(&problem, &derivation)
        .expect("setup: the derivation validates");
    let other = claimed(&problem, &[1, 2, 3], derivation);
    let error = exported(&problem, &other).expect_err("an unbacked pin must not export");
    assert!(
        error.contains("but the counterexample's validated ground derivation derives Int(0)"),
        "{error}"
    );
}

/// Negative twin: steps that agree with the derivation are published and
/// exported unchanged.
#[test]
fn agreeing_steps_are_kept_and_exported() {
    let (problem, _) = counting_problem();
    let derivation = counting_derivation(2);
    let agreeing = claimed(&problem, &[0, 1, 2], derivation.clone());
    assert!(agreeing
        .restated_by_derivation(&problem, &derivation)
        .is_none());
    assert_eq!(
        exported(&problem, &agreeing).as_deref(),
        Ok("trace-validity-depth-2")
    );
}

/// Negative twin: a counterexample that claims no trace keeps claiming none
/// (the exporter already refuses an empty trace).
#[test]
fn a_counterexample_without_steps_is_not_restated() {
    let (problem, _) = counting_problem();
    let derivation = counting_derivation(2);
    let empty = Counterexample::new(Vec::new()).with_ground_derivation(derivation.clone());
    assert!(empty
        .restated_by_derivation(&problem, &derivation)
        .is_none());
}

/// Negative twin: a derivation that does not validate is no evidence either
/// way; it cannot make the exporter refuse a trace it disagrees with.
#[test]
fn a_derivation_that_does_not_validate_is_not_compared() {
    let (problem, _) = counting_problem();
    let mut invalid = counting_derivation(3);
    invalid.steps[2].env = env(&[("x", 1), ("y", 7)]);
    assert!(crate::ground_derivation::validate_ground_derivation(&problem, &invalid).is_err());
    let agreeing = claimed(&problem, &[0, 1, 2], invalid);
    assert_eq!(
        exported(&problem, &agreeing).as_deref(),
        Ok("trace-validity-depth-2")
    );
}

/// The witness form STEP D accepts on backs the check too: PDR's genuine
/// counterexample exports, and with its last step dropped it does not.
#[test]
fn the_exporter_compares_with_the_derivation_the_witness_names() {
    let problem = ChcParser::parse(
        "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
",
    )
    .expect("fixture parses");
    let PdrResult::Unsafe(mut cex) = PdrSolver::new(problem.clone(), PdrConfig::default()).solve()
    else {
        panic!("setup: PDR finds the depth-6 counterexample");
    };
    assert!(cex.witness_ground_derivation_validates(&problem));
    assert_eq!(
        exported(&problem, &cex).as_deref(),
        Ok("trace-validity-depth-6")
    );
    cex.steps.pop();
    let error = exported(&problem, &cex).expect_err("a one-short trace must not export");
    assert!(error.contains("derivation derives 7 states"), "{error}");
}
