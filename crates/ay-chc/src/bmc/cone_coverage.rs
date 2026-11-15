// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regressions for level coverage, separate from shared-ancestry admission.

use super::*;
use crate::{ClauseBody, HornClause};

mod execution;
mod oracle;

fn nullary_rule(problem: &mut ChcProblem, head: PredicateId, body: &[PredicateId]) {
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(body.iter().map(|id| (*id, Vec::new())).collect()),
        ClauseHead::Predicate(head, Vec::new()),
    ));
}

fn uneven_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", Vec::new());
    let s = problem.declare_predicate("S", Vec::new());
    let q = problem.declare_predicate("Q", Vec::new());
    nullary_rule(&mut problem, p, &[]);
    nullary_rule(&mut problem, s, &[]);
    nullary_rule(&mut problem, q, &[s]);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, Vec::new()), (q, Vec::new())]),
        ClauseHead::False,
    ));
    problem
}

fn all_true_model(conjuncts: &[ChcExpr]) -> FxHashMap<String, SmtValue> {
    conjuncts
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|var| {
            assert_eq!(var.sort, ChcSort::Bool);
            (var.name, SmtValue::Bool(true))
        })
        .collect()
}

fn assert_true_under_boolean_model(conjuncts: Vec<ChcExpr>) {
    let model = all_true_model(&conjuncts);
    assert_eq!(
        crate::expr::evaluate::evaluate_expr(&ChcExpr::and_all(conjuncts), &model),
        Some(SmtValue::Bool(true)),
    );
}

#[test]
fn cone_coverage_uneven_premises_have_a_common_level_and_live_formula() {
    let solver = BmcSolver::new(uneven_problem(), BmcConfig::default());
    let queries: Vec<_> = solver.problem.queries().collect();
    let defs = solver.defs_by_head();
    let cone = solver.query_dependency_cone(&queries, &defs);
    let reachable = solver.reachable_levels_by_pred(3, &cone, &defs);
    let query = queries[0];
    assert!(query.body.predicates.iter().all(|(pred, _)| {
        reachable
            .get(pred)
            .is_some_and(|levels| levels.contains(&1))
    }));
    assert_eq!(solver.level_flat_may_alias_ancestry(), Some(false));
    let mut conjuncts = Vec::new();
    for level in 0..=1 {
        solver.compile_level_flat_cone(level, &cone, &reachable, &defs, &mut conjuncts);
    }
    solver.compile_query(query, 1, &mut conjuncts);
    // Independent concrete satisfying assignment, no SAT solver involved.
    assert_true_under_boolean_model(conjuncts);
}

#[test]
fn cone_coverage_nullary_fact_empty_body_matches_explicit_true() {
    for constraint in [None, Some(ChcExpr::Bool(true))] {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", Vec::new());
        problem.add_clause(HornClause::new(
            ClauseBody::new(Vec::new(), constraint),
            ClauseHead::Predicate(p, Vec::new()),
        ));
        let solver = BmcSolver::new(problem, BmcConfig::default());
        let defs = solver.defs_by_head();
        let cone = FxHashSet::from_iter([p]);
        let reachable = solver.reachable_levels_by_pred(2, &cone, &defs);
        assert_eq!(reachable[&p], FxHashSet::from_iter([0, 1, 2]));
        for level in 0..=2 {
            let mut ordinary = vec![solver.level_predicate(p, level)];
            solver.compile_level_flat(level, &mut ordinary);
            assert_true_under_boolean_model(ordinary);
            let mut limited = vec![solver.level_predicate(p, level)];
            solver.compile_level_flat_cone(level, &cone, &reachable, &defs, &mut limited);
            assert_true_under_boolean_model(limited);
        }
    }
}

#[test]
fn cone_coverage_fact_constraint_survives_structural_admission() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::not(ChcExpr::var(ChcVar::new("b", ChcSort::Bool)))),
        ClauseHead::Predicate(p, Vec::new()),
    ));
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let defs = solver.defs_by_head();
    let cone = FxHashSet::from_iter([p]);
    let reachable = solver.reachable_levels_by_pred(2, &cone, &defs);
    assert_eq!(reachable[&p], FxHashSet::from_iter([0, 1, 2]));
    for level in 0..=2 {
        let mut conjuncts = vec![solver.level_predicate(p, level)];
        solver.compile_level_flat_cone(level, &cone, &reachable, &defs, &mut conjuncts);
        let model = all_true_model(&conjuncts);
        assert_eq!(
            crate::expr::evaluate::evaluate_expr(&ChcExpr::and_all(conjuncts), &model),
            Some(SmtValue::Bool(false)),
        );
    }
}

#[test]
fn cone_coverage_bodyless_query_is_not_an_absent_group() {
    let solver = BmcSolver::new(ChcProblem::new(), BmcConfig::default());
    for constraint in [None, Some(ChcExpr::Bool(true)), Some(ChcExpr::Bool(false))] {
        let expected = constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let query = HornClause::new(ClauseBody::new(Vec::new(), constraint), ClauseHead::False);
        let mut conjuncts = Vec::new();
        solver.compile_query(&query, 0, &mut conjuncts);
        assert!(
            !conjuncts.is_empty(),
            "empty query groups are skipped by callers"
        );
        assert_eq!(ChcExpr::and_all(conjuncts), expected);
    }
}
