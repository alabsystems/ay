// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::PdrSolver;
use super::{with_blocking_clauses, with_int_presence_tautologies};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

fn top_level_and_arity(expr: &ChcExpr) -> Option<usize> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => Some(args.len()),
        _ => None,
    }
}

#[test]
fn test_with_blocking_clauses_high_arity_flat_and_drop_safe() {
    // #2508: large blocking sets must stay n-ary and drop without leak workarounds.
    const ARITY: usize = 4_096;

    let base = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("base", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let blockers: Vec<ChcExpr> = (0..ARITY)
        .map(|i| {
            ChcExpr::ge(
                ChcExpr::var(ChcVar::new(format!("b{i}"), ChcSort::Int)),
                ChcExpr::int(i as i128),
            )
        })
        .collect();

    let query = with_blocking_clauses(base, &blockers);
    assert_eq!(top_level_and_arity(&query), Some(ARITY + 1));
    drop(query);
}

#[test]
fn test_with_int_presence_tautologies_high_arity_flat_and_drop_safe() {
    // #2508: tautology injection must not build deep binary And chains.
    const ARITY: usize = 4_096;

    let vars: Vec<ChcVar> = (0..ARITY)
        .map(|i| ChcVar::new(format!("v{i}"), ChcSort::Int))
        .collect();
    let query = with_int_presence_tautologies(ChcExpr::Bool(true), &vars);

    assert_eq!(top_level_and_arity(&query), Some(ARITY));
    drop(query);
}

// Direct tests for try_algebraic_forward_eval constraint checking (#2927)

#[test]
fn algebraic_forward_eval_rejects_unsatisfied_inequality_constraint() {
    // Constraint: (and (= x 5) (< x 3)) — x=5 violates x<3.
    // Even though equalities resolve, the constraint is false.
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3)),
    );
    let head_var_info = vec![("x_canon".to_string(), "x_next".to_string(), ChcExpr::var(x))];
    let int_vars = vec![ChcVar::new("x_canon".to_string(), ChcSort::Int)];

    let result = PdrSolver::try_algebraic_forward_eval(&constraint, &head_var_info, &int_vars);
    assert!(
        result.is_none(),
        "expected None for unsatisfied inequality constraint, got {result:?}"
    );
}

#[test]
fn algebraic_forward_eval_accepts_satisfied_constraint() {
    // Constraint: (and (= x 5) (> x 3)) — x=5, 5>3 is true.
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(3)),
    );
    let head_var_info = vec![("x_canon".to_string(), "x_next".to_string(), ChcExpr::var(x))];
    let int_vars = vec![ChcVar::new("x_canon".to_string(), ChcSort::Int)];

    let result = PdrSolver::try_algebraic_forward_eval(&constraint, &head_var_info, &int_vars);
    assert!(result.is_some(), "expected Some for satisfied constraint");
    let map = result.unwrap();
    assert_eq!(map.get("x_canon"), Some(&5), "expected x_canon=5");
}

#[test]
fn algebraic_forward_eval_rejects_mixed_equality_and_unsatisfied_inequality() {
    // Constraint: (and (= x 10) (= y (+ x 1)) (le x 5)) — x=10, y=11, but x<=5 is false.
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let y = ChcVar::new("y".to_string(), ChcSort::Int);
    let constraint = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            Arc::new(ChcExpr::eq(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
            Arc::new(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ],
    );
    let head_var_info = vec![
        ("x_canon".to_string(), "x_next".to_string(), ChcExpr::var(x)),
        ("y_canon".to_string(), "y_next".to_string(), ChcExpr::var(y)),
    ];
    let int_vars = vec![
        ChcVar::new("x_canon".to_string(), ChcSort::Int),
        ChcVar::new("y_canon".to_string(), ChcSort::Int),
    ];

    let result = PdrSolver::try_algebraic_forward_eval(&constraint, &head_var_info, &int_vars);
    assert!(
        result.is_none(),
        "expected None for mixed equalities with unsatisfied inequality, got {result:?}"
    );
}

#[test]
fn algebraic_forward_eval_or_branch_selects_satisfied_branch() {
    // Constraint: (or (and (= x 1) (< x 0)) (and (= x 2) (> x 1)))
    // Branch 1: x=1, x<0 is false → skip
    // Branch 2: x=2, x>1 is true → return x=2
    let x = ChcVar::new("x".to_string(), ChcSort::Int);
    let branch1 = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
    );
    let branch2 = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );
    let constraint = ChcExpr::or(branch1, branch2);

    let head_var_info = vec![("x_canon".to_string(), "x_next".to_string(), ChcExpr::var(x))];
    let int_vars = vec![ChcVar::new("x_canon".to_string(), ChcSort::Int)];

    let result = PdrSolver::try_algebraic_forward_eval(&constraint, &head_var_info, &int_vars);
    assert!(result.is_some(), "expected Some from second OR branch");
    let map = result.unwrap();
    assert_eq!(
        map.get("x_canon"),
        Some(&2),
        "expected x_canon=2 from second (satisfied) OR branch"
    );
}
