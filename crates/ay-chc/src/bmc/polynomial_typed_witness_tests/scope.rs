// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn scoped_fixture() -> BmcSolver {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let unused = problem.declare_predicate("Unused", Vec::new());
    let x = variable("x", &ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(x.clone(), ChcExpr::Int(7)))),
        ClauseHead::Predicate(p, vec![ChcExpr::Int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), None),
        ClauseHead::Predicate(unused, Vec::new()),
    ));
    // A literal-false body would be discarded by add_clause. P(1) remains
    // a real first query, but cannot match the only reachable fact P(0).
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![ChcExpr::Int(1)],
    )])));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::Int(0)])],
        Some(ChcExpr::eq(x, ChcExpr::Int(13))),
    )));
    BmcSolver::new(problem, BmcConfig::default())
}

fn scoped_model(solver: &BmcSolver, names: &mut AcyclicNames<'_>) -> FxHashMap<String, SmtValue> {
    let p = PredicateId::new(0);
    let local = solver
        .mk_dag_clause_vars(&solver.problem.clauses()[0], p, 0, names)
        .unwrap();
    let query = solver
        .mk_dag_query_vars(&solver.problem.clauses()[3], 1, names)
        .unwrap();
    FxHashMap::from_iter([
        (
            name(solver.dag_predicate(p, names).unwrap()),
            SmtValue::Bool(true),
        ),
        (
            name(solver.dag_rule_indicator(p, 0, names).unwrap()),
            SmtValue::Bool(true),
        ),
        (name(solver.dag_arg(p, 0, names).unwrap()), SmtValue::Int(0)),
        (name(local["x"].clone()), SmtValue::Int(7)),
        (name(query["x"].clone()), SmtValue::Int(13)),
    ])
}

#[test]
fn query_ordinal_and_source_local_scope_are_independent_of_the_root_clause() {
    let solver = scoped_fixture();
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let model = scoped_model(&solver, &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    assert_eq!(witness.query_clause, Some(3));
    assert_eq!(
        witness.entries[witness.root].instances["x"],
        SmtValue::Int(7)
    );
    let ground = ground(&solver, &witness, &model, &mut names).unwrap();
    assert_eq!(ground.steps[0].clause_index, 0);
    assert_eq!(ground.steps[0].env["x"], SmtValue::Int(7));
    assert_eq!(ground.steps[1].clause_index, 3);
    assert_eq!(ground.steps[1].env["x"], SmtValue::Int(13));
    assert_eq!(ground.steps[1].premises, vec![0]);
}

#[test]
fn missing_query_locals_cannot_be_filled_from_the_root_or_wrong_query_namespace() {
    let solver = scoped_fixture();
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let model = scoped_model(&solver, &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    let query = &solver.problem.clauses()[3];
    let query_vars = solver.mk_dag_query_vars(query, 1, &mut names).unwrap();
    let mut missing = model.clone();
    missing.remove(&name(query_vars["x"].clone()));
    // Neither root.instances["x"] nor the original source model key is evidence.
    missing.insert("x".to_owned(), SmtValue::Int(13));
    assert!(ground(&solver, &witness, &missing, &mut names).is_none());
    let wrong_order = [&solver.problem.clauses()[3], &solver.problem.clauses()[2]];
    assert!(solver
        .ground_derivation_from_polynomial_witness(
            &witness,
            &model,
            &wrong_order,
            &mut names,
            deadline(),
        )
        .is_none());
    let cloned_query = query.clone();
    assert!(solver
        .ground_derivation_from_polynomial_witness(
            &witness,
            &model,
            &[&cloned_query],
            &mut names,
            deadline(),
        )
        .is_none());
    assert!(!names.stopped());
    assert!(ground(&solver, &witness, &model, &mut names).is_some());
}

#[test]
fn malformed_derivation_candidates_cannot_bypass_original_source_validation() {
    let solver = scoped_fixture();
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let model = scoped_model(&solver, &mut names);
    let original = witness(&solver, &model, &mut names).unwrap();
    for mutation in 0..6 {
        let mut candidate = original.clone();
        let root = candidate.root;
        match mutation {
            0 => {
                candidate.entries[root]
                    .instances
                    .insert("x".to_owned(), SmtValue::Int(8));
            }
            1 => candidate.entries[root].incoming_clause = Some(1),
            2 => candidate.entries[root].premises = vec![root],
            3 => candidate.query_clause = Some(2),
            4 => candidate.query_clause = Some(usize::MAX),
            _ => candidate.root = usize::MAX,
        }
        assert!(
            ground(&solver, &candidate, &model, &mut names).is_none(),
            "mutation {mutation}"
        );
        assert!(!names.stopped());
    }
    assert!(ground(&solver, &original, &model, &mut names).is_some());
}
