// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::*;

#[test]
fn arithmetic_application_above_arity_cap_fails_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("arity_x", Sort::Int);
    let y = terms.mk_var("arity_y", Sort::Int);
    let assumption = raw_eq(&mut terms, x, y);
    let definitions = Definition::decode(&terms, assumption);
    let left = terms.mk_app(Symbol::named("+"), vec![x; MAX_APP_ARITY + 1], Sort::Int);
    let right = terms.mk_app(Symbol::named("+"), vec![y; MAX_APP_ARITY + 1], Sort::Int);
    let mut budget = EqBudget::new(1_000);
    assert!(plan_numeric_equality(&mut terms, left, right, &definitions, &mut budget).is_none());
    assert!(budget.work < 1_000);
}

#[test]
fn shared_dag_plan_growth_stays_inside_node_and_work_caps() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("dag_x", Sort::Int);
    let y = terms.mk_var("dag_y", Sort::Int);
    let assumption = raw_eq(&mut terms, x, y);
    let definitions = Definition::decode(&terms, assumption);
    let (mut left, mut right) = (x, y);
    for _ in 0..16 {
        left = terms.mk_app(Symbol::named("+"), [left, left], Sort::Int);
        right = terms.mk_app(Symbol::named("+"), [right, right], Sort::Int);
    }
    let mut budget = EqBudget::new(100_000);
    assert!(plan_numeric_equality(&mut terms, left, right, &definitions, &mut budget).is_none());
    assert!(budget.work < 100_000);
}

#[test]
fn polynomial_recognizer_attempts_are_charged_fail_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("poly_budget_x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let left = terms.mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let mut budget =
        EqBudget::new(u32::try_from(POLY_ATTEMPT_WORK - 1).expect("constant fits u32"));
    assert!(plan_numeric_equality(&mut terms, left, x, &[], &mut budget).is_none());
}

#[test]
fn polynomial_recognizer_attempt_count_is_a_separate_hard_cap() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("poly_attempt_x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let left = terms.mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let mut budget = EqBudget::new(100_000);
    budget.poly_attempts = 0;
    assert!(plan_numeric_equality(&mut terms, left, x, &[], &mut budget).is_none());
    assert_eq!(budget.poly_attempts, 0);
    assert!(
        budget.work > 100_000 - u32::try_from(POLY_ATTEMPT_WORK).expect("constant fits u32"),
        "non-polynomial planning may spend work, but no recognizer charge is allowed"
    );
}

#[test]
fn reversed_assumption_step_upper_bound_is_exact() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("step_bound_x", Sort::Int);
    let y = terms.mk_var("step_bound_y", Sort::Int);
    let authored = raw_eq(&mut terms, y, x);
    let definition = Definition::decode(&terms, authored)
        .into_iter()
        .find(|definition| definition.variable == x)
        .expect("reverse orientation must be decoded");
    assert!(definition.reversed);
    let plan = EqPlan::assumed(&mut terms, &definition);
    assert_eq!(plan.emitted_step_upper_bound(), Some(2));

    let mut proof = ay_core::Proof::new();
    let mut assumptions = ay_core::kani_compat::DetHashMap::default();
    emit_eq_plan(&mut proof, &plan, &mut assumptions).expect("plan emits");
    assert_eq!(proof.steps.len(), 2);
}
