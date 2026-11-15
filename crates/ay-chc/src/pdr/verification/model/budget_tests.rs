// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::{safe_boundary_per_rule_budget, SAFE_BOUNDARY_PER_RULE_FLOOR, VERIFY_RETRY_TIMEOUT};
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::{ChcExpr, ChcParser, ChcProblem};
use ay_core::time::Instant;
use std::time::Duration;

#[test]
fn safe_boundary_budget_is_the_remaining_deadline_within_floor_and_cap() {
    // No deadline: the cap.
    assert_eq!(safe_boundary_per_rule_budget(None), VERIFY_RETRY_TIMEOUT);
    // More time left than the cap: the cap.
    let generous = Instant::now() + Duration::from_secs(120);
    assert_eq!(
        safe_boundary_per_rule_budget(Some(generous)),
        VERIFY_RETRY_TIMEOUT
    );
    // In between: what remains of the caller's budget, not a fixed two seconds.
    let ten_seconds = Instant::now() + Duration::from_secs(10);
    let budget = safe_boundary_per_rule_budget(Some(ten_seconds));
    assert!(
        budget > Duration::from_secs(8) && budget <= Duration::from_secs(10),
        "{budget:?}"
    );
    // Nearly or fully spent: never below the historical fixed value.
    let nearly_spent = Instant::now() + Duration::from_millis(100);
    assert_eq!(
        safe_boundary_per_rule_budget(Some(nearly_spent)),
        SAFE_BOUNDARY_PER_RULE_FLOOR
    );
    assert_eq!(
        safe_boundary_per_rule_budget(Some(Instant::now())),
        SAFE_BOUNDARY_PER_RULE_FLOOR
    );
}

const COUNTER: &str = r#"(set-logic HORN)
(declare-var x Int)
(declare-var x2 Int)
(declare-rel inv (Int))
(rule (=> (= x 0) (inv x)))
(rule (=> (and (inv x) (= x2 (+ x 1))) (inv x2)))
(rule (=> (and (inv x) (< x 0)) false))"#;

fn solved_counter() -> (ChcProblem, InvariantModel) {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let PdrResult::Safe(model) = PdrSolver::solve_problem(&problem, PdrConfig::default()) else {
        panic!("the counter is safe");
    };
    (problem, model)
}

fn at_safe_boundary(problem: &ChcProblem, model: &InvariantModel) -> bool {
    let deadline = Some(Instant::now() + Duration::from_secs(60));
    let mut verifier = PdrSolver::new(problem.clone(), PdrConfig::default());
    verifier.verify_model_at_safe_boundary(model, deadline)
}

#[test]
fn a_generous_deadline_admits_a_valid_model() {
    let (problem, model) = solved_counter();
    assert!(at_safe_boundary(&problem, &model));
}

#[test]
fn a_generous_deadline_still_refuses_a_non_inductive_model() {
    // Soundness control: the budget only buys the clause check time; a model
    // the check refutes (x <= 5 is not preserved by x' = x + 1) stays refused.
    let (problem, model) = solved_counter();
    let inv = problem.lookup_predicate("inv").unwrap();
    let vars = model.get(&inv).unwrap().vars.clone();
    let bound = ChcExpr::le(ChcExpr::var(vars[0].clone()), ChcExpr::int(5));
    let mut wrong = InvariantModel::new();
    wrong.set(inv, PredicateInterpretation::new(vars, bound));
    assert!(!at_safe_boundary(&problem, &wrong));
}
