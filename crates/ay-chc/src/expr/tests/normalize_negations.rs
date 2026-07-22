// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;

#[test]
fn test_normalize_negations_small_expression() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::not(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)));
    let normalized = expr.normalize_negations();
    assert_eq!(normalized, ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5)));
}

#[test]
fn test_normalize_negations_budget_does_not_crash() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut expr = ChcExpr::not(ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)));
    for _ in 0..21 {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    let _result = expr.normalize_negations();
}

#[test]
fn test_normalize_negations_depth_guard_keeps_deep_suffix_unmodified() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let mut expr = ChcExpr::not(ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5)));
    let depth = MAX_EXPR_RECURSION_DEPTH + 16;
    for _ in 0..depth {
        expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0))),
                Arc::new(expr),
            ],
        );
    }
    let normalized = expr.normalize_negations();
    let deep_leaf = right_leaf_of_left_associated_and_chain(&normalized, depth);
    assert!(
        matches!(
            deep_leaf,
            ChcExpr::Op(ChcOp::Not, args)
                if args.len() == 1
                    && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Le, le_args) if le_args.len() == 2)
        ),
        "deep suffix should stay unnormalized once depth guard triggers: {deep_leaf:?}"
    );
}
