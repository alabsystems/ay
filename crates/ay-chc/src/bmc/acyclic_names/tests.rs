// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::bmc::{AcyclicBranchEnumeration, BmcConfig, BmcSolver};
use crate::expr::evaluate::evaluate_expr;
use crate::smt::SmtValue;
use crate::{ChcOp, ChcSort, ClauseBody, ClauseHead, PredicateId};
use std::sync::Arc;

mod boundaries;
mod routes;

fn variable(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn collision_problem(query_name: &str) -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(variable("x"), ChcExpr::Int(0))),
        ClauseHead::Predicate(pred, vec![ChcExpr::Int(1)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![variable(query_name)])],
            Some(ChcExpr::eq(variable(query_name), ChcExpr::Int(1))),
        ),
        ClauseHead::False,
    ));
    (problem, pred)
}

fn assert_reachable(expression: &ChcExpr, query_name: &str) {
    let mut model: DetHashMap<_, _> = expression
        .vars()
        .into_iter()
        .map(|var| (var.name, SmtValue::Int(0)))
        .collect();
    model.insert(query_name.to_owned(), SmtValue::Int(1));
    assert_eq!(
        evaluate_expr(expression, &model),
        Some(SmtValue::Bool(true))
    );
}

#[test]
fn ordinary_source_preserves_legacy_generated_spelling_and_order() {
    let (problem, pred) = collision_problem("z");
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    assert_eq!(names.suffix, "");
    let clause = &solver.problem.clauses()[0];
    assert_eq!(
        names
            .variables(clause)
            .unwrap()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>(),
        clause.vars()
    );
    let map = solver
        .mk_fresh_rule_vars(clause, pred, 0, 0, &mut names)
        .unwrap();
    assert_eq!(map["x"], variable("__bmc_dag_p0_r0_i0_x"));
    assert_eq!(
        solver.reach_arg(pred, 0, &mut names).unwrap(),
        variable("__bmc_reach_p0_a0")
    );
    let direct = names.instance_vars(clause).unwrap();
    assert_eq!(direct["x"], variable("__bmc_dag_e0_v0"));
    assert_eq!(
        BmcSolver::fresh_expansion_id("__bmc_dag_e42_v7__ay_exact_0"),
        Some(42)
    );
}

#[test]
fn generated_families_are_disjoint_from_all_source_symbol_endings() {
    let (mut problem, _) = collision_problem("__bmc_reach_p0_a0");
    problem.declare_predicate("P__ay_exact_0", Vec::new());
    let global = ChcExpr::FuncApp("g__ay_exact_1".to_owned(), ChcSort::Int, Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(global, ChcExpr::Int(0))),
        ClauseHead::False,
    ));
    let mut live = || true;
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    assert_eq!(names.suffix, "__ay_exact_2");
    for stem in [
        "__bmc_dag_e0_v0",
        "__bmc_dag_p0_r0_i0_x",
        "__bmc_reach_p0_a0",
    ] {
        assert_eq!(
            names.name(stem.to_owned()).unwrap(),
            format!("{stem}__ay_exact_2")
        );
    }
}

#[test]
fn complete_clause_variables_keep_first_occurrence_and_reject_sort_aliases() {
    let (problem, pred) = collision_problem("z");
    let clause = HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![variable("b"), variable("a")])],
            Some(ChcExpr::eq(variable("c"), variable("b"))),
        ),
        ClauseHead::Predicate(pred, vec![variable("d"), variable("a")]),
    );
    let mut live = || true;
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    assert_eq!(
        names
            .variables(&clause)
            .unwrap()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>(),
        clause.vars()
    );
    let bad = HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            variable("x"),
            ChcExpr::Var(ChcVar::new("x", ChcSort::Bool)),
        )),
        ClauseHead::False,
    );
    assert!(names.variables(&bad).is_none());
    assert!(names.stopped());
}
