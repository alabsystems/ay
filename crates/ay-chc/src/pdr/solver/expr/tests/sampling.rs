// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sample_reachable_models_extracts_point_from_must_summary() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int Int ) Bool)

(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (= x 0) (= y 0))
  (P x y)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse P must-summary fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();

    solver.reachability.must_summaries.add(
        1,
        pred,
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::int(5)),
            ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::int(-7)),
        ),
    );

    let models = solver.sample_reachable_models(pred, 1, 3);
    assert!(
        models
            .iter()
            .any(|m| { m.get(&vars[0].name) == Some(&5) && m.get(&vars[1].name) == Some(&-7) }),
        "expected a reachable sample model for P at level 1"
    );
}

#[test]
fn sample_reachable_models_returns_complete_int_assignments() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int Int ) Bool)

(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (= x 0) (= y 0))
  (P x y)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse P must-summary fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();

    // Only constrain one canonical var; sampling should still return a complete assignment.
    solver.reachability.must_summaries.add(
        1,
        pred,
        ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::int(5)),
    );

    let models = solver.sample_reachable_models(pred, 1, 1);
    assert_eq!(
        models.len(),
        1,
        "expected at least one reachable sample model"
    );
    assert_eq!(
        models[0].get(&vars[0].name),
        Some(&5),
        "expected sampled model to satisfy the must-summary equality"
    );
    assert!(
        models[0].contains_key(&vars[1].name),
        "expected sampling to return a complete int assignment"
    );
}

#[test]
fn sample_init_models_respects_head_arg_expressions() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int Int ) Bool)

; Fact: x = 0 ==> P(x, x+1)
(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x (+ x 1))
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse P init sampling fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();

    let models = solver.sample_init_models(pred, 3);
    assert!(
        models
            .iter()
            .any(|m| { m.get(&vars[0].name) == Some(&0) && m.get(&vars[1].name) == Some(&1) }),
        "expected init sampling to respect head args (P(0, 1))"
    );
}

#[test]
fn sample_init_models_unconstrained_returns_assignments() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int Int ) Bool)

; Fact: true ==> P(x, y)
(assert
  (forall ( (x Int) (y Int) )
(=>
  true
  (P x y)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse unconstrained P init fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for P")
        .to_vec();

    let models = solver.sample_init_models(pred, 1);
    assert!(!models.is_empty(), "expected at least one init model");
    let m = &models[0];
    assert!(
        m.contains_key(&vars[0].name) && m.contains_key(&vars[1].name),
        "expected init model to include integer assignments for all canonical vars"
    );
}
