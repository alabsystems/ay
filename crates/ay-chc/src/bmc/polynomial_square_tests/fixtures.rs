// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

#[derive(Clone, Copy)]
pub(super) enum SecondSquare {
    Rule,
    Query,
}

pub(super) struct Compiled {
    pub expression: ChcExpr,
    pub squares: usize,
}

pub(super) fn variable(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

pub(super) fn constraint(name: &str, lower: i128, residue: i128) -> ChcExpr {
    let input = variable(name);
    ChcExpr::and_all(vec![
        ChcExpr::ge(input.clone(), ChcExpr::Int(lower)),
        ChcExpr::le(input.clone(), ChcExpr::Int(lower + 1)),
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::mul(input.clone(), input), ChcExpr::Int(5)),
            ChcExpr::Int(residue),
        ),
    ])
}

pub(super) fn fixture(site: SecondSquare, residue: i128) -> BmcSolver {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint("x", 0, 0)),
        ClauseHead::Predicate(p, vec![variable("x")]),
    ));
    match site {
        SecondSquare::Rule => {
            let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
            problem.add_clause(HornClause::new(
                ClauseBody::new(
                    vec![(p, vec![variable("x")])],
                    Some(constraint("y", 2, residue)),
                ),
                ClauseHead::Predicate(q, vec![variable("y")]),
            ));
            problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
                q,
                vec![variable("z")],
            )])));
        }
        SecondSquare::Query => {
            problem.add_clause(HornClause::query(ClauseBody::new(
                vec![(p, vec![variable("x")])],
                Some(constraint("y", 2, residue)),
            )));
        }
    }
    BmcSolver::new(problem, BmcConfig::default())
}

pub(super) fn compile(solver: &BmcSolver, names: &mut AcyclicNames<'_>) -> Option<Compiled> {
    let deadline = ay_core::time::Instant::now() + Duration::from_secs(600);
    let definitions = solver.defs_by_head();
    let queries: Vec<_> = solver.problem.queries().collect();
    let cone = solver.query_dependency_cone(&queries, &definitions);
    assert!(solver.acyclic_dag_encoding_applicable(&queries, &cone, &definitions));
    let mut ordered: Vec<_> = cone.into_iter().collect();
    ordered.sort_by_key(|pred| pred.index());
    let constants = solver
        .infer_acyclic_dag_arg_constants(&ordered, &definitions, deadline)
        .unwrap();
    let bounds = solver
        .infer_acyclic_dag_arg_bounds(&ordered, &definitions, &constants, deadline)
        .unwrap();
    let mut conjuncts = Vec::new();
    solver.push_acyclic_dag_arg_bound_conjuncts(
        &ordered,
        &bounds,
        &constants,
        &mut conjuncts,
        names,
    )?;
    let mut squares = 0;
    let mut simplified = 0;
    for pred in ordered {
        solver.compile_acyclic_dag_definition(
            pred,
            &definitions,
            &constants,
            &bounds,
            &mut squares,
            &mut simplified,
            &mut conjuncts,
            deadline,
            names,
        )?;
    }
    let mut alternatives = Vec::new();
    for (index, query) in queries.into_iter().enumerate() {
        alternatives.push(solver.compile_acyclic_dag_query(
            query,
            index,
            &constants,
            &bounds,
            &mut squares,
            &mut simplified,
            deadline,
            names,
        )?);
    }
    conjuncts.push(ChcExpr::or_all(alternatives));
    names.poll()?;
    Some(Compiled {
        expression: ChcExpr::and_all(conjuncts),
        squares,
    })
}

pub(super) fn aux(ordinal: usize) -> String {
    format!("__bmc_square_lia_aux_{ordinal}")
}

pub(super) fn auxiliary_names(expression: &ChcExpr) -> Vec<String> {
    let mut result: Vec<_> = expression
        .vars()
        .into_iter()
        .filter(|variable| variable.name.starts_with("__bmc_square_lia_aux_"))
        .map(|variable| variable.name)
        .collect();
    result.sort();
    result
}

pub(super) fn satisfying_model(
    solver: &BmcSolver,
    expression: &ChcExpr,
    y: i128,
    auxiliaries: &[String],
) -> FxHashMap<String, SmtValue> {
    let mut model: FxHashMap<_, _> = expression
        .vars()
        .into_iter()
        .map(|variable| {
            let value = match variable.sort {
                ChcSort::Int => SmtValue::Int(0),
                ChcSort::Bool => SmtValue::Bool(true),
                _ => panic!("integer fixture"),
            };
            (variable.name, value)
        })
        .collect();
    let mut query_index = 0;
    let mut live = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    for (index, clause) in solver.problem.clauses().iter().enumerate() {
        let substitutions = match &clause.head {
            ClauseHead::Predicate(pred, _) => {
                solver.mk_dag_clause_vars(clause, *pred, index, &mut names)
            }
            ClauseHead::False => {
                let map = solver.mk_dag_query_vars(clause, query_index, &mut names);
                query_index += 1;
                map
            }
        }
        .unwrap();
        for (source, expression) in substitutions {
            let ChcExpr::Var(ref variable) = expression else {
                panic!("variable substitution")
            };
            model.insert(
                variable.name.clone(),
                SmtValue::Int(if source == "x" { 0 } else { y }),
            );
        }
    }
    model.insert("__bmc_poly_p0_a0".to_owned(), SmtValue::Int(0));
    model.insert("__bmc_poly_p1_a0".to_owned(), SmtValue::Int(y));
    for (index, name) in auxiliaries.iter().enumerate() {
        model.insert(
            name.clone(),
            SmtValue::Int(if index == 0 { 0 } else { y * y }),
        );
    }
    model
}

pub(super) fn assert_true(expression: &ChcExpr, model: &FxHashMap<String, SmtValue>) {
    assert_eq!(evaluate_expr(expression, model), Some(SmtValue::Bool(true)));
}

pub(super) fn derivation(site: SecondSquare, y: i128) -> GroundDerivation {
    let env = |pairs: &[(&str, i128)]| {
        pairs
            .iter()
            .map(|(name, value)| ((*name).to_owned(), SmtValue::Int(*value)))
            .collect()
    };
    let mut steps = vec![GroundDerivationStep {
        clause_index: 0,
        env: env(&[("x", 0)]),
        premises: Vec::new(),
    }];
    match site {
        SecondSquare::Rule => {
            steps.push(GroundDerivationStep {
                clause_index: 1,
                env: env(&[("x", 0), ("y", y)]),
                premises: vec![0],
            });
            steps.push(GroundDerivationStep {
                clause_index: 2,
                env: env(&[("z", y)]),
                premises: vec![1],
            });
        }
        SecondSquare::Query => steps.push(GroundDerivationStep {
            clause_index: 1,
            env: env(&[("x", 0), ("y", y)]),
            premises: vec![0],
        }),
    }
    GroundDerivation {
        query_step: steps.len() - 1,
        steps,
    }
}
