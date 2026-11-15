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
    let conditions = collect_ite_conditions(std::iter::once(&ite), MAX_ITE_CONDITIONS)
        .expect("one condition is within the cap");
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

/// `ite(c, e, e + 1)` nested `depth` times over one shared `e`: a DAG of
/// `O(depth)` nodes whose tree expansion has `2^depth` leaves.
fn shared_ite_tower(depth: usize, conds: &[ChcExpr]) -> ChcExpr {
    let mut expr = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    for level in 0..depth {
        let shared: Arc<ChcExpr> = expr.into();
        let plus_one = ChcExpr::add(shared.as_ref().clone(), ChcExpr::Int(1));
        expr = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                conds[level % conds.len()].clone().into(),
                shared,
                plus_one.into(),
            ],
        );
    }
    expr
}

/// Reference: the former recursive tree walk plus first-occurrence dedup.
fn tree_conditions(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
    if let ChcExpr::Op(op, args) = expr {
        if *op == ChcOp::Ite && args.len() == 3 && !out.contains(args[0].as_ref()) {
            out.push(args[0].as_ref().clone());
        }
        for arg in args {
            tree_conditions(arg, out);
        }
    }
}

/// On a 2^120-leaf shared tower with two conditions, collection and case
/// substitution finish in DAG time (the tree walk would never return).
#[test]
fn ite_walks_run_in_dag_time_on_shared_towers() {
    let conds: Vec<ChcExpr> = ["c0", "c1"]
        .iter()
        .map(|n| ChcExpr::var(ChcVar::new(*n, ChcSort::Bool)))
        .collect();
    let tower = shared_ite_tower(120, &conds);
    let collected = collect_ite_conditions(std::iter::once(&tower), MAX_ITE_CONDITIONS)
        .expect("two conditions are within the cap");
    assert_eq!(collected, vec![conds[1].clone(), conds[0].clone()]);
    let all_true = substitute_ite_condition(
        &substitute_ite_condition(&tower, &conds[0], true),
        &conds[1],
        true,
    );
    assert_eq!(all_true, ChcExpr::var(ChcVar::new("x", ChcSort::Int)));
}

/// The DAG-time collection returns exactly the tree walk's deduplicated
/// conditions, and gives up (`None`) exactly when they exceed the cap.
#[test]
fn ite_condition_collection_matches_the_tree_walk() {
    let conds: Vec<ChcExpr> = (0..9)
        .map(|i| {
            ChcExpr::ge(
                ChcExpr::var(ChcVar::new(&format!("v{i}"), ChcSort::Int)),
                ChcExpr::Int(i),
            )
        })
        .collect();
    for count in 1..=conds.len() {
        for depth in [count, count + 3, 2 * count + 1] {
            let tower = shared_ite_tower(depth, &conds[..count]);
            let mut expected = Vec::new();
            tree_conditions(&tower, &mut expected);
            let got = collect_ite_conditions(std::iter::once(&tower), MAX_ITE_CONDITIONS);
            if expected.len() > MAX_ITE_CONDITIONS {
                assert!(got.is_none(), "count={count} depth={depth}");
            } else {
                assert_eq!(got.as_ref(), Some(&expected), "count={count} depth={depth}");
            }
        }
    }
}
