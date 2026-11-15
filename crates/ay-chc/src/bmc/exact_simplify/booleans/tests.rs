// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::{ChcOp, ChcProblem, ChcSort, ChcVar};
use std::sync::Arc;

mod progress;

fn boolean(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Bool))
}

fn integer(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn local_scope() -> DetHashSet<String> {
    ["b", "c", "d"].into_iter().map(str::to_owned).collect()
}

fn compare_legacy(input: Vec<ChcExpr>, initial_env: DetHashMap<String, IntInterval>) {
    let mut expected = input.clone();
    let mut expected_env = initial_env.clone();
    BmcSolver::simplify_conjuncts_with_intervals_and_bools(
        &mut expected,
        &mut expected_env,
        &local_scope(),
        None,
    );
    let mut actual = input;
    let mut actual_env = initial_env;
    let mut progress = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    assert_eq!(
        simplify(&mut actual, &mut actual_env, &local_scope(), &mut names),
        Some(())
    );
    assert_eq!(actual, expected);
    assert_eq!(actual_env, expected_env);
}

#[test]
fn ordinary_boolean_interval_rounds_keep_legacy_results_and_scope() {
    for input in [
        vec![],
        vec![ChcExpr::Bool(true)],
        vec![ChcExpr::Bool(false)],
        vec![boolean("b"), ChcExpr::not(boolean("b"))],
        vec![
            boolean("b"),
            ChcExpr::eq(boolean("c"), boolean("b")),
            ChcExpr::eq(boolean("d"), boolean("c")),
        ],
        vec![
            ChcExpr::eq(boolean("b"), ChcExpr::Bool(false)),
            ChcExpr::eq(ChcExpr::Bool(false), boolean("c")),
            ChcExpr::or(boolean("b"), boolean("c")),
        ],
        vec![boolean("outside"), ChcExpr::not(boolean("outside"))],
        vec![
            ChcExpr::ge(integer("x"), ChcExpr::Int(1)),
            ChcExpr::le(integer("x"), ChcExpr::Int(1)),
            ChcExpr::eq(boolean("b"), ChcExpr::eq(integer("x"), ChcExpr::Int(1))),
        ],
        vec![ChcExpr::ne(integer("x"), integer("y"))],
    ] {
        compare_legacy(input, DetHashMap::default());
    }
    compare_legacy(
        vec![ChcExpr::eq(
            boolean("b"),
            ChcExpr::le(integer("x"), ChcExpr::Int(3)),
        )],
        [(
            "x".to_owned(),
            IntInterval {
                lower: Some(0),
                upper: Some(2),
            },
        )]
        .into_iter()
        .collect(),
    );
}

#[test]
fn variables_outside_the_exact_boolean_scope_are_not_assumed_literals() {
    let mut conjuncts = vec![boolean("outside")];
    let mut env = DetHashMap::default();
    let mut progress = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    assert_eq!(
        simplify(&mut conjuncts, &mut env, &local_scope(), &mut names),
        Some(())
    );
    assert_eq!(conjuncts, vec![boolean("outside")]);
}

fn growing_equality() -> ChcExpr {
    let mut expression = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Ite,
                vec![
                    Arc::new(boolean("b")),
                    Arc::new(integer("x")),
                    Arc::new(integer("y")),
                ],
            )),
            Arc::new(ChcExpr::Op(
                ChcOp::Ite,
                vec![
                    Arc::new(boolean("c")),
                    Arc::new(integer("z")),
                    Arc::new(integer("w")),
                ],
            )),
        ],
    );
    for _ in 0..(crate::expr::MAX_EXPR_RECURSION_DEPTH - 4) {
        expression = ChcExpr::FuncApp("wrap".to_owned(), ChcSort::Bool, vec![Arc::new(expression)]);
    }
    expression
}

#[test]
fn equality_ite_growth_refuses_before_committing_vector_or_environment() {
    let mut conjuncts = vec![growing_equality()];
    let original = conjuncts.clone();
    let mut env: DetHashMap<_, _> = [("seed".to_owned(), IntInterval::exact(7))]
        .into_iter()
        .collect();
    let original_env = env.clone();
    let mut progress = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
    assert!(names.check_all(&conjuncts).is_some());
    assert!(simplify(&mut conjuncts, &mut env, &local_scope(), &mut names).is_none());
    assert!(names.stopped());
    assert_eq!(conjuncts, original);
    assert_eq!(env, original_env);
    for expression in conjuncts.into_iter().chain(original) {
        ChcExpr::iterative_drop(expression);
    }
}
