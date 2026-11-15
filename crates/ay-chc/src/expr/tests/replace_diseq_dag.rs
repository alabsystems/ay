// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `replace_diseq` rewrites each distinct node of a DAG once and keeps its
//! sharing; its result is the tree rewrite's formula.

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;

fn diseq(var: &str, value: i64) -> ChcExpr {
    ChcExpr::not(ChcExpr::eq(
        ChcExpr::var(ChcVar::new(var, ChcSort::Int)),
        ChcExpr::int(value),
    ))
}

#[test]
fn replace_diseq_rewrites_every_occurrence_and_only_the_target() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let one = ChcExpr::int(1);
    // An explicit `not` over the target (the constructor would cancel it).
    let negated = ChcExpr::Op(ChcOp::Not, vec![Arc::new(diseq("x", 1))]);
    let expr = ChcExpr::and(diseq("x", 1), ChcExpr::or(diseq("y", 2), negated));
    let replaced = expr.replace_diseq(&x, &one, ChcExpr::lt(x.clone(), one.clone()));
    let expected = ChcExpr::and(
        ChcExpr::lt(x.clone(), one.clone()),
        ChcExpr::or(
            diseq("y", 2),
            ChcExpr::not(ChcExpr::lt(x.clone(), one.clone())),
        ),
    );
    assert_eq!(replaced, expected);
    // Sides match in either order.
    let swapped = expr.replace_diseq(&one, &x, ChcExpr::lt(x.clone(), one.clone()));
    assert_eq!(swapped, expected);
    // No target: the expression is unchanged.
    let untouched = expr.replace_diseq(&x, &ChcExpr::int(7), ChcExpr::Bool(false));
    assert_eq!(untouched, expr);
}

#[test]
fn replace_diseq_keeps_dag_sharing() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let one = ChcExpr::int(1);
    let mut shared = Arc::new(ChcExpr::and(diseq("x", 1), diseq("y", 2)));
    for _ in 0..60 {
        shared = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&shared), Arc::clone(&shared)],
        ));
    }
    // 2^60 tree occurrences: only a DAG rewrite finishes.
    let replaced = shared.replace_diseq(&x, &one, ChcExpr::lt(x.clone(), one.clone()));
    let mut node = &replaced;
    for _ in 0..60 {
        let ChcExpr::Op(ChcOp::And, args) = node else {
            panic!("the and spine is kept");
        };
        assert!(Arc::ptr_eq(&args[0], &args[1]), "sharing is kept");
        node = args[0].as_ref();
    }
    assert_eq!(
        *node,
        ChcExpr::and(ChcExpr::lt(x.clone(), one.clone()), diseq("y", 2))
    );
}

/// Flattening a shared `and`/`or` spine expands each shared node once: the
/// result is the tree flattening's (first-occurrence order, deduplicated).
#[test]
fn and_all_and_or_all_flatten_a_shared_spine_once() {
    let atom = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Bool));
    let mut and_spine = Arc::new(ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(atom("a")), Arc::new(atom("b"))],
    ));
    let mut or_spine = Arc::new(ChcExpr::Op(
        ChcOp::Or,
        vec![Arc::new(atom("a")), Arc::new(atom("b"))],
    ));
    for _ in 0..60 {
        and_spine = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&and_spine), Arc::clone(&and_spine)],
        ));
        or_spine = Arc::new(ChcExpr::Op(
            ChcOp::Or,
            vec![Arc::clone(&or_spine), Arc::clone(&or_spine)],
        ));
    }
    assert_eq!(
        ChcExpr::and_all([and_spine.as_ref().clone(), atom("c"), atom("a")]),
        ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(atom("a")),
                Arc::new(atom("b")),
                Arc::new(atom("c"))
            ]
        )
    );
    assert_eq!(
        ChcExpr::or_all([atom("c"), or_spine.as_ref().clone()]),
        ChcExpr::Op(
            ChcOp::Or,
            vec![
                Arc::new(atom("c")),
                Arc::new(atom("a")),
                Arc::new(atom("b"))
            ]
        )
    );
    // A `false` under a shared spine still decides the conjunction.
    let with_false = Arc::new(ChcExpr::Op(
        ChcOp::And,
        vec![Arc::clone(&and_spine), Arc::new(ChcExpr::Bool(false))],
    ));
    assert_eq!(
        ChcExpr::and_all([with_false.as_ref().clone()]),
        ChcExpr::Bool(false)
    );
}
