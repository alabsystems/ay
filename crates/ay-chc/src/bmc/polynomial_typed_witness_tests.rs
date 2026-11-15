// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Solver-free model recovery and original-source replay regressions.

use super::*;
use crate::ClauseBody;
use std::cell::Cell;
use std::time::Duration;

mod progress;
mod scope;
mod uf;
mod values;

fn deadline() -> ay_core::time::Instant {
    ay_core::time::Instant::now() + Duration::from_secs(600)
}

fn variable(name: &str, sort: &ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort.clone()))
}

fn fixture(sort: ChcSort) -> BmcSolver {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![sort.clone()]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), None),
        ClauseHead::Predicate(p, vec![variable("x", &sort)]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![variable("z", &sort)],
    )])));
    BmcSolver::new(problem, BmcConfig::default())
}

fn name(expression: ChcExpr) -> String {
    let ChcExpr::Var(ref var) = expression else {
        panic!("expected generated variable")
    };
    var.name.clone()
}

fn model(
    solver: &BmcSolver,
    value: &SmtValue,
    names: &mut AcyclicNames<'_>,
) -> FxHashMap<String, SmtValue> {
    let p = PredicateId::new(0);
    let clauses = solver.problem.clauses();
    let locals = solver.mk_dag_clause_vars(&clauses[0], p, 0, names).unwrap();
    let query = solver.mk_dag_query_vars(&clauses[1], 0, names).unwrap();
    FxHashMap::from_iter([
        (
            name(solver.dag_predicate(p, names).unwrap()),
            SmtValue::Bool(true),
        ),
        (
            name(solver.dag_rule_indicator(p, 0, names).unwrap()),
            SmtValue::Bool(true),
        ),
        (name(solver.dag_arg(p, 0, names).unwrap()), value.clone()),
        (name(locals["x"].clone()), value.clone()),
        (name(query["z"].clone()), value.clone()),
    ])
}

fn witness(
    solver: &BmcSolver,
    model: &FxHashMap<String, SmtValue>,
    names: &mut AcyclicNames<'_>,
) -> Option<DerivationWitness> {
    solver.acyclic_dag_model_derivation_witness(
        model,
        &solver.problem.queries().collect::<Vec<_>>(),
        &solver.defs_by_head(),
        &FxHashMap::default(),
        names,
    )
}

fn ground(
    solver: &BmcSolver,
    witness: &DerivationWitness,
    model: &FxHashMap<String, SmtValue>,
    names: &mut AcyclicNames<'_>,
) -> Option<GroundDerivation> {
    solver.ground_derivation_from_polynomial_witness(
        witness,
        model,
        &solver.problem.queries().collect::<Vec<_>>(),
        names,
        deadline(),
    )
}
