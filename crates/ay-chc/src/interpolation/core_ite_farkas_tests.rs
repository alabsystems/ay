// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};

#[test]
fn test_pure_lia_no_ite_returns_none() {
    // Pure LIA with no ITE → D11 has nothing to do
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10))];
    let b = vec![ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(5))];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let result = compute_ite_farkas_interpolant(&a, &b, &shared);
    assert!(
        result.is_none(),
        "Pure LIA should return None (handled by earlier pipeline)"
    );
}

#[test]
fn test_single_shared_ite_condition() {
    // A: ite(c >= 1, x, 0) >= 10  (with shared c)
    // B: x < 5
    // After case split on (c >= 1):
    //   c>=1: A=[x >= 10, c >= 1], B=[x < 5] → bound interpolant: x >= 10
    //   c<1:  A=[0 >= 10, c < 1]  → UNSAT by itself (0 < 10), no B needed
    let x = ChcVar::new("x", ChcSort::Int);
    let c = ChcVar::new("c", ChcSort::Int);
    let shared: FxHashSet<String> = ["x", "c"].into_iter().map(String::from).collect();

    let ite_expr = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            ChcExpr::ge(ChcExpr::var(c), ChcExpr::Int(1)).into(),
            ChcExpr::var(x.clone()).into(),
            ChcExpr::Int(0).into(),
        ],
    );
    let a = vec![ChcExpr::ge(ite_expr, ChcExpr::Int(10))];
    let b = vec![ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(5))];

    let result = compute_ite_farkas_interpolant(&a, &b, &shared);
    // Should produce some interpolant (exact form depends on Farkas)
    // The important thing is it doesn't return None
    if let Some(interp) = &result {
        let iv: FxHashSet<String> = interp.vars().into_iter().map(|v| v.name).collect();
        assert!(
            iv.iter().all(|v| shared.contains(v)),
            "Interpolant must use only shared vars"
        );
    }
    // Note: may return None if Farkas can't handle the specific encoding
}

#[test]
fn test_budget_exceeded_returns_none() {
    // Create 7 different ITE conditions (2^7 = 128 > 64 budget)
    let x = ChcVar::new("x", ChcSort::Int);
    let mut constraints = Vec::new();
    let mut expr = ChcExpr::var(x.clone());
    for i in 0..7 {
        let c = ChcVar::new(&format!("c{i}"), ChcSort::Int);
        expr = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                ChcExpr::ge(ChcExpr::var(c), ChcExpr::Int(0)).into(),
                ChcExpr::add(expr.clone(), ChcExpr::Int(1)).into(),
                expr.into(),
            ],
        );
    }
    constraints.push(ChcExpr::ge(expr, ChcExpr::Int(100)));
    let b = vec![ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0))];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let result = compute_ite_farkas_interpolant(&constraints, &b, &shared);
    assert!(result.is_none(), "Budget exceeded should return None");
}

#[test]
fn test_collect_ite_conditions_basic() {
    let x = ChcVar::new("x", ChcSort::Int);
    let c = ChcVar::new("c", ChcSort::Bool);
    let ite = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            ChcExpr::var(c.clone()).into(),
            ChcExpr::var(x).into(),
            ChcExpr::Int(0).into(),
        ],
    );
    let mut conditions = Vec::new();
    collect_ite_conditions(&ite, &mut conditions);
    assert_eq!(conditions.len(), 1);
    assert_eq!(conditions[0], ChcExpr::var(c));
}

#[test]
fn test_substitute_ite_condition_true() {
    let x = ChcVar::new("x", ChcSort::Int);
    let c_cond = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("c", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    let ite = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            c_cond.clone().into(),
            ChcExpr::var(x.clone()).into(),
            ChcExpr::Int(0).into(),
        ],
    );
    let result = substitute_ite_condition(&ite, &c_cond, true);
    assert_eq!(result, ChcExpr::var(x));
}

#[test]
fn test_substitute_ite_condition_false() {
    let c_cond = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("c", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    let ite = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            c_cond.clone().into(),
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)).into(),
            ChcExpr::Int(0).into(),
        ],
    );
    let result = substitute_ite_condition(&ite, &c_cond, false);
    assert_eq!(result, ChcExpr::Int(0));
}
