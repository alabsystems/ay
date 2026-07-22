// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_collect_conjuncts_single() {
    let expr = ChcExpr::Bool(true);
    let conjuncts = expr.collect_conjuncts();
    assert_eq!(conjuncts.len(), 1);
}

#[test]
fn test_collect_conjuncts_nested() {
    let a = ChcExpr::Bool(true);
    let b = ChcExpr::Bool(false);
    let c = ChcExpr::eq(ChcExpr::Int(0), ChcExpr::Int(1));
    let inner = ChcExpr::Op(ChcOp::And, vec![Arc::new(a), Arc::new(b)]);
    let outer = ChcExpr::Op(ChcOp::And, vec![Arc::new(inner), Arc::new(c)]);
    let conjuncts = outer.collect_conjuncts();
    assert_eq!(conjuncts.len(), 3);
}

#[test]
fn test_build_conjunction_empty() {
    let result = build_conjunction(&[]);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

#[test]
fn test_build_conjunction_single() {
    let conjuncts = vec![ChcExpr::Bool(false)];
    let result = build_conjunction(&conjuncts);
    assert!(matches!(result, ChcExpr::Bool(false)));
}

#[test]
fn test_build_conjunction_multiple() {
    let a = ChcExpr::Bool(true);
    let b = ChcExpr::Bool(false);
    let conjuncts = vec![a, b];
    let result = build_conjunction(&conjuncts);
    assert!(matches!(result, ChcExpr::Op(ChcOp::And, _)));
}

#[test]
fn test_extract_equality_var_const() {
    use crate::ChcSort;
    let var = ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Int,
    };
    // (= x 42)
    let eq = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Var(var)), Arc::new(ChcExpr::Int(42))],
    );
    let result = extract_equality(&eq);
    assert!(result.is_some());
    let (v, n) = result.unwrap();
    assert_eq!(v.name, "x");
    assert_eq!(n, 42);
}

#[test]
fn test_extract_equality_const_var() {
    use crate::ChcSort;
    let var = ChcVar {
        name: "y".to_string(),
        sort: ChcSort::Int,
    };
    // (= 100 y)
    let eq = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Int(100)), Arc::new(ChcExpr::Var(var))],
    );
    let result = extract_equality(&eq);
    assert!(result.is_some());
    let (v, n) = result.unwrap();
    assert_eq!(v.name, "y");
    assert_eq!(n, 100);
}

#[test]
fn test_extract_equality_non_equality() {
    // (> x 42) should return None
    use crate::ChcSort;
    let var = ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Int,
    };
    let gt = ChcExpr::Op(
        ChcOp::Gt,
        vec![Arc::new(ChcExpr::Var(var)), Arc::new(ChcExpr::Int(42))],
    );
    assert!(extract_equality(&gt).is_none());
}

#[test]
fn test_extract_equality_or_not_distinct_equality() {
    use crate::ChcSort;
    let var = ChcVar {
        name: "z".to_string(),
        sort: ChcSort::Int,
    };
    // (= z 5)
    let eq = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Var(var)), Arc::new(ChcExpr::Int(5))],
    );
    let result = extract_equality_or_not_distinct(&eq);
    assert!(result.is_some());
    let (v, n) = result.unwrap();
    assert_eq!(v.name, "z");
    assert_eq!(n, 5);
}

#[test]
fn test_extract_equality_or_not_distinct_not_ne() {
    use crate::ChcSort;
    let var = ChcVar {
        name: "w".to_string(),
        sort: ChcSort::Int,
    };
    // (not (distinct w 10)) = (not (ne w 10))
    let ne = ChcExpr::Op(
        ChcOp::Ne,
        vec![Arc::new(ChcExpr::Var(var)), Arc::new(ChcExpr::Int(10))],
    );
    let not_ne = ChcExpr::Op(ChcOp::Not, vec![Arc::new(ne)]);
    let result = extract_equality_or_not_distinct(&not_ne);
    assert!(result.is_some());
    let (v, n) = result.unwrap();
    assert_eq!(v.name, "w");
    assert_eq!(n, 10);
}

#[test]
fn test_collect_or_branches_flattens_nested_or() {
    let a = ChcExpr::Bool(true);
    let b = ChcExpr::Bool(false);
    let c = ChcExpr::eq(ChcExpr::Int(0), ChcExpr::Int(1));
    let inner = ChcExpr::Op(ChcOp::Or, vec![Arc::new(b.clone()), Arc::new(c.clone())]);
    let outer = ChcExpr::Op(ChcOp::Or, vec![Arc::new(a.clone()), Arc::new(inner)]);

    let ChcExpr::Op(ChcOp::Or, ref args) = outer else {
        panic!("expected OR");
    };

    let mut branches = Vec::new();
    collect_or_branches(args, &mut branches);
    assert_eq!(branches, vec![a, b, c]);
}

#[test]
fn test_extract_disequalities_collects_from_and_or() {
    use crate::ChcSort;

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // (and
    //   (not (= x 1))
    //   (or (not (= y 2)) (= z 3)))
    let not_x = ChcExpr::not(ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Var(x.clone())), Arc::new(ChcExpr::Int(1))],
    ));
    let not_y = ChcExpr::not(ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Var(y.clone())), Arc::new(ChcExpr::Int(2))],
    ));
    let eq_z = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::Var(z)), Arc::new(ChcExpr::Int(3))],
    );
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(not_x),
            Arc::new(ChcExpr::Op(
                ChcOp::Or,
                vec![Arc::new(not_y), Arc::new(eq_z)],
            )),
        ],
    );

    let diseqs = extract_disequalities(&expr);
    assert_eq!(diseqs.len(), 2);

    assert!(diseqs.contains(&(ChcExpr::Var(x), ChcExpr::Int(1))));
    assert!(diseqs.contains(&(ChcExpr::Var(y), ChcExpr::Int(2))));
}
