// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

pub(super) const STEMS: [&str; 5] = [
    "__bmc_poly_p0_reach",
    "__bmc_poly_p0_r0",
    "__bmc_poly_p0_a0",
    "__bmc_poly_p0_c0_v0",
    "__bmc_poly_q0_v0",
];

pub(super) fn variable(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

pub(super) fn global(name: &str) -> ChcExpr {
    ChcExpr::FuncApp(name.to_owned(), ChcSort::Int, Vec::new())
}

pub(super) fn fixture(source: Option<&str>) -> BmcSolver {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let constraint = source.map(|name| {
        // An integer tautology retaining the source FuncApp surface through
        // constant simplification; P's argument remains nonconstant.
        ChcExpr::or_all(vec![
            ChcExpr::le(global(name), ChcExpr::Int(0)),
            ChcExpr::ge(global(name), ChcExpr::Int(1)),
        ])
    });
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), constraint),
        ClauseHead::Predicate(p, vec![variable("x")]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![variable("z")],
    )])));
    BmcSolver::new(problem, BmcConfig::default())
}

pub(super) fn var_name(expression: ChcExpr) -> String {
    let ChcExpr::Var(ref var) = expression else {
        panic!("generated variable")
    };
    var.name.clone()
}

pub(super) fn generated(solver: &BmcSolver, names: &mut AcyclicNames<'_>) -> [String; 5] {
    let p = PredicateId::new(0);
    let clause = &solver.problem.clauses()[0];
    let query = &solver.problem.clauses()[1];
    [
        var_name(solver.dag_predicate(p, names).unwrap()),
        var_name(solver.dag_rule_indicator(p, 0, names).unwrap()),
        var_name(solver.dag_arg(p, 0, names).unwrap()),
        var_name(solver.mk_dag_clause_vars(clause, p, 0, names).unwrap()["x"].clone()),
        var_name(solver.mk_dag_query_vars(query, 0, names).unwrap()["z"].clone()),
    ]
}

pub(super) fn compile(solver: &BmcSolver, names: &mut AcyclicNames<'_>) -> Option<ChcExpr> {
    let deadline = ay_core::time::Instant::now() + Duration::from_secs(600);
    let definitions = solver.defs_by_head();
    let constants = FxHashMap::default();
    let bounds = FxHashMap::default();
    let mut squares = 0;
    let mut simplified = 0;
    let mut conjuncts = Vec::new();
    solver.compile_acyclic_dag_definition(
        PredicateId::new(0),
        &definitions,
        &constants,
        &bounds,
        &mut squares,
        &mut simplified,
        &mut conjuncts,
        deadline,
        names,
    )?;
    conjuncts.push(solver.compile_acyclic_dag_query(
        &solver.problem.clauses()[1],
        0,
        &constants,
        &bounds,
        &mut squares,
        &mut simplified,
        deadline,
        names,
    )?);
    names.poll()?;
    Some(ChcExpr::and_all(conjuncts))
}

pub(super) fn contains_global(expression: &ChcExpr, source: &str) -> bool {
    let mut pending = vec![expression];
    while let Some(expr) = pending.pop() {
        match expr {
            ChcExpr::FuncApp(name, _, _) if name == source => return true,
            ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) => {
                pending.extend(args.iter().map(AsRef::as_ref));
            }
            _ => {}
        }
    }
    false
}

pub(super) fn model(
    solver: &BmcSolver,
    names: &mut AcyclicNames<'_>,
) -> FxHashMap<String, SmtValue> {
    generated(solver, names)
        .into_iter()
        .enumerate()
        .map(|(index, name)| {
            (
                name,
                if index < 2 {
                    SmtValue::Bool(true)
                } else {
                    SmtValue::Int(7)
                },
            )
        })
        .collect()
}

pub(super) fn witness(
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
