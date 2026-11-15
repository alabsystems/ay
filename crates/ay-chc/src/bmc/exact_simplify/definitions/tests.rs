// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::{ChcProblem, ChcSort, ChcVar};
use std::sync::Arc;

mod boundaries;
mod oracle;

fn var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn call(name: &str, argument: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp(name.to_owned(), ChcSort::Int, vec![Arc::new(argument)])
}

fn nested_f(mut expression: ChcExpr, depth: usize) -> ChcExpr {
    for _ in 0..depth {
        expression = call("f", expression);
    }
    expression
}

fn live_substitute(conjuncts: &mut Vec<ChcExpr>) -> Option<usize> {
    let problem = ChcProblem::new();
    let mut progress = || true;
    let mut names = AcyclicNames::new(&problem, &mut progress).unwrap();
    substitute(conjuncts, &mut names)
}

fn compare_original(input: Vec<ChcExpr>) {
    let mut expected = input.clone();
    let expected_count = oracle::substitute(&mut expected);
    let mut actual = input;
    assert_eq!(live_substitute(&mut actual), Some(expected_count));
    assert_eq!(actual, expected);
}

#[test]
fn ordinary_results_counts_and_conjunct_order_match_frozen_rounds() {
    for input in [
        vec![],
        vec![ChcExpr::Bool(true)],
        vec![ChcExpr::Bool(false)],
        vec![ChcExpr::eq(var("x"), ChcExpr::Int(1))],
        vec![
            ChcExpr::eq(var("x"), ChcExpr::Int(1)),
            ChcExpr::ne(var("x"), ChcExpr::Int(2)),
        ],
        vec![
            ChcExpr::eq(var("x"), ChcExpr::Int(1)),
            ChcExpr::ne(var("x"), ChcExpr::Int(1)),
        ],
        vec![
            ChcExpr::eq(var("x"), call("f", var("y"))),
            ChcExpr::eq(var("y"), call("f", var("z"))),
            ChcExpr::ge(var("x"), ChcExpr::Int(0)),
        ],
        vec![
            ChcExpr::eq(var("__bmc_dag_e1_v0"), var("__bmc_dag_e0_v0")),
            ChcExpr::ne(var("__bmc_dag_e1_v0"), ChcExpr::Int(0)),
        ],
    ] {
        compare_original(input);
    }
}

#[test]
fn identical_and_conflicting_definitions_match_frozen_candidate_pruning() {
    for rhs in [call("f", var("a")), call("f", var("b"))] {
        let input = vec![
            ChcExpr::eq(var("x"), call("f", var("a"))),
            ChcExpr::eq(var("x"), rhs),
            ChcExpr::ge(var("x"), ChcExpr::Int(0)),
        ];
        let mut progress = || true;
        let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
        assert_eq!(
            candidates::collect(&input, &mut names),
            Some(oracle::collect(&input))
        );
        compare_original(input);
    }
}

#[test]
fn cyclic_and_self_definitions_preserve_legacy_removal_order() {
    for input in [
        vec![ChcExpr::eq(var("x"), call("f", var("x")))],
        vec![
            ChcExpr::eq(var("x"), call("f", var("y"))),
            ChcExpr::eq(var("y"), call("g", var("x"))),
        ],
        vec![
            ChcExpr::eq(var("a"), call("f", var("b"))),
            ChcExpr::eq(var("b"), call("f", var("c"))),
            ChcExpr::eq(var("c"), call("f", var("a"))),
            ChcExpr::eq(var("outside"), call("f", var("b"))),
        ],
    ] {
        let mut progress = || true;
        let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
        assert_eq!(
            candidates::collect(&input, &mut names),
            Some(oracle::collect(&input))
        );
        compare_original(input);
    }
}

#[test]
fn shared_expression_edges_keep_exact_repeated_conjuncts() {
    let repeated = Arc::new(call("f", var("y")));
    let expression = ChcExpr::FuncApp(
        "g".to_owned(),
        ChcSort::Int,
        vec![Arc::clone(&repeated), Arc::clone(&repeated), repeated],
    );
    compare_original(vec![
        ChcExpr::eq(var("x"), expression.clone()),
        ChcExpr::eq(var("y"), ChcExpr::Int(2)),
        ChcExpr::ge(expression.clone(), ChcExpr::Int(0)),
        ChcExpr::ge(expression, ChcExpr::Int(0)),
    ]);
}

#[test]
fn candidate_size_boundary_retains_legacy_4096_cap() {
    for width in [4094usize, 4095] {
        let expression = ChcExpr::FuncApp(
            "wide".to_owned(),
            ChcSort::Int,
            (0..width).map(|_| Arc::new(ChcExpr::Int(0))).collect(),
        );
        let input = vec![ChcExpr::eq(var("x"), expression)];
        let mut progress = || true;
        let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
        let actual = candidates::collect(&input, &mut names).unwrap();
        assert_eq!(actual.contains_key("x"), width == 4094);
        assert_eq!(actual, oracle::collect(&input));
    }
}
