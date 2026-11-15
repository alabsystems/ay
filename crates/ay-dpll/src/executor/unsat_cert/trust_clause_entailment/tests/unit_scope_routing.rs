// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit arithmetic keeps step (4)'s exact whole-problem re-decision.

use super::*;

fn integer_scope(bounds: &str) -> (Executor, Vec<TermId>, TermId) {
    let mut exec = elaborated(&format!(
        "(set-logic QF_NIA)
         (declare-const x Int)
         {bounds}"
    ));
    let scope = exec.ctx.assertions.clone();
    let fresh = exec.ctx.terms.mk_var("unit_scope_fresh", Sort::Bool);
    exec.last_proof = Some(trust_only_proof());
    (exec, scope, fresh)
}

#[test]
fn integer_units_use_whole_problem_redecision_and_keep_tighter_limits() {
    let (mut exec, scope, fresh) = integer_scope("(assert (> x 0)) (assert (< x 0))");
    assert!(ay_nia::is_integer_unit_conjunction(&exec.ctx.terms, &scope));
    let clauses = deferred(&[vec![fresh]]);
    assert!(!entails(&exec, &scope, &clauses));
    assert_eq!(
        exec.fresh_executor_corroboration(
            &scope,
            &scope,
            &clauses,
            &exec.certification_discharge_controls(),
        )
        .map(UnsatCorroboration::method),
        Some(CorroborationMethod::Resolve)
    );
    assert_eq!(exec.ctx.assertions, scope);

    exec.set_resource_limit(Some(0));
    assert_eq!(
        exec.fresh_executor_corroboration(
            &scope,
            &scope,
            &clauses,
            &exec.certification_discharge_controls(),
        ),
        None,
        "routing cannot widen a caller's zero conflict limit"
    );
}

#[test]
fn satisfiable_integer_units_cannot_grant_a_corroboration() {
    let (mut exec, scope, fresh) = integer_scope("(assert (> x 0)) (assert (< x 2))");
    let clauses = deferred(&[vec![fresh]]);
    assert!(!entails(&exec, &scope, &clauses));
    assert_eq!(
        exec.fresh_executor_corroboration(
            &scope,
            &scope,
            &clauses,
            &exec.certification_discharge_controls(),
        ),
        None
    );
    assert_eq!(exec.ctx.assertions, scope);
    assert!(exec.take_unsat_certificate().is_none());
}

#[test]
fn real_arithmetic_retains_the_entailment_question() {
    let mut exec = elaborated(
        "(set-logic QF_LRA)
         (declare-const x Real)
         (assert (> x 0))
         (assert (< x 0))",
    );
    let scope = exec.ctx.assertions.clone();
    let fresh = exec.ctx.terms.mk_var("real_scope_fresh", Sort::Bool);
    exec.last_proof = Some(trust_only_proof());
    assert!(!ay_nia::is_integer_unit_conjunction(
        &exec.ctx.terms,
        &scope
    ));
    assert!(entails(&exec, &scope, &deferred(&[vec![fresh]])));
}

#[test]
fn an_incomplete_integer_scope_retains_the_entailment_question() {
    let (exec, scope, fresh) = integer_scope("(assert (> x 0)) (assert (< x 0))");
    let mut wide = vec![scope[0]; 4_097];
    wide.push(scope[1]);
    assert!(!ay_nia::is_integer_unit_conjunction(&exec.ctx.terms, &wide));
    assert!(entails(&exec, &wide, &deferred(&[vec![fresh]])));
}
