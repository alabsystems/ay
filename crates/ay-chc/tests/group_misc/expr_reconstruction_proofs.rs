// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

// Author: Andrew Yates
//
// Regression tests for #3665: no-op expression traversal preserves sharing.
//
// These tests keep no-op substitution behavior explicit for expressions with
// shared Arc subtrees.

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

/// Proves that `substitute` with a non-matching substitution preserves Arc
/// sharing for unchanged subtrees.
///
/// The substitution targets variable "nonexistent" which doesn't appear in
/// the expression, so nothing should change.
#[test]
fn substitute_nonmatching_preserves_arc_sharing() {
    // Build: (+ x (+ y z))
    let x = Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::Int)));
    let y = Arc::new(ChcExpr::var(ChcVar::new("y", ChcSort::Int)));
    let z = Arc::new(ChcExpr::var(ChcVar::new("z", ChcSort::Int)));
    let inner = Arc::new(ChcExpr::Op(ChcOp::Add, vec![y, z]));
    let root = ChcExpr::Op(ChcOp::Add, vec![x, inner.clone()]);

    // Substitute a variable that doesn't exist in the expression
    let nonexistent = ChcVar::new("nonexistent", ChcSort::Int);
    let replacement = ChcExpr::Int(999);
    let result = root.substitute(&[(nonexistent, replacement)]);

    // Structural equality holds (same tree shape):
    assert_eq!(root, result);

    // Arc sharing should be preserved for unchanged inner nodes.
    match &result {
        ChcExpr::Op(ChcOp::Add, args) => {
            assert!(
                Arc::ptr_eq(&args[1], &inner),
                "substitute with non-matching var should preserve shared inner nodes"
            );
        }
        _ => panic!("expected Op(Add, _)"),
    }
}

/// Checks that a no-op substitution over an already-flat conjunction preserves
/// semantics while exercising a non-trivial expression tree.
#[test]
fn and_reconstruction_on_already_flat_conjunction() {
    // Build: (and (>= x 0) (>= y 0)) — already flat, no nested And
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let geq_x = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(x), Arc::new(ChcExpr::Int(0))]);
    let geq_y = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(y), Arc::new(ChcExpr::Int(0))]);
    let conj = ChcExpr::and(geq_x, geq_y);

    // substitute with non-matching var makes no semantic change.
    let nonexistent = ChcVar::new("nonexistent", ChcSort::Int);
    let replacement = ChcExpr::Int(0);
    let result = conj.substitute(&[(nonexistent, replacement)]);

    // Semantically identical
    assert_eq!(
        conj, result,
        "non-matching substitute should preserve semantics"
    );

    // Count nodes to keep the regression input non-trivial.
    let node_count = count_nodes(&conj);
    assert!(
        node_count >= 5,
        "conjunction should have at least 5 nodes (and, 2 x ge, 2 x int), got {node_count}"
    );
}

/// Count nodes in an expression tree (for test assertions only).
fn count_nodes(expr: &ChcExpr) -> usize {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::Var(_) => 1,
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            1 + args.iter().map(|a| count_nodes(a)).sum::<usize>()
        }
        _ => 1,
    }
}
