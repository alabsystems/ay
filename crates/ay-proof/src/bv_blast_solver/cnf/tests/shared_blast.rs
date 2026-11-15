// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The encoder blasts each DISTINCT node once, and that changes nothing but
//! the work: the CNF of a heavily repeated expression is the one the
//! per-occurrence encoder builds.

use super::*;

/// `mul(add(a, b), xor(a, b))`, then `depth` times `or(e, e)` of two separate
/// copies: `7 * 2^depth + 2^depth - 1` occurrences of `5 + depth` nodes.
fn doubled(depth: usize) -> BvExpr {
    let a = BvExpr::leaf("a", 16);
    let b = BvExpr::leaf("b", 16);
    let mut expression = BvExpr::mul(BvExpr::add(a.clone(), b.clone()), BvExpr::xor(a, b));
    for _ in 0..depth {
        expression = BvExpr::or(expression.clone(), expression);
    }
    expression
}

fn blast_both(
    lhs: &BvExpr,
    rhs: &BvExpr,
    shared: std::collections::HashMap<usize, u32>,
) -> (usize, Vec<u32>, Vec<u32>) {
    let mut keep_going = || true;
    let mut blaster = ExprBlaster::new(None, &mut keep_going);
    blaster.shared = shared;
    let (mut vars, mut lemmas, mut clauses) = (VarTable::default(), Vec::new(), Vec::new());
    let left = blaster
        .blast(lhs, &mut vars, &mut lemmas, &mut clauses)
        .unwrap();
    let right = blaster
        .blast(rhs, &mut vars, &mut lemmas, &mut clauses)
        .unwrap();
    (blaster.node_blasts, left, right)
}

#[test]
fn a_repeated_subtree_is_blasted_once_and_encodes_as_every_occurrence() {
    let depth = 8;
    let lhs = doubled(depth);
    let rhs = BvExpr::leaf("c", 16);
    let mut preflight = preflight_bv_equality(&lhs, &rhs, &limits(), &mut || true).unwrap();
    let occurrences = 8 * (1 << depth) - 1 + 1;
    let distinct = 5 + depth + 1;
    assert_eq!(
        (preflight.occurrences, preflight.nodes),
        (occurrences, distinct)
    );

    // Work: every distinct node once with the preflight's table, every
    // occurrence without it.
    let (shared_blasts, shared_lhs, shared_rhs) =
        blast_both(&lhs, &rhs, preflight.sharing.take_occurrences());
    let (every_blasts, every_lhs, every_rhs) =
        blast_both(&lhs, &rhs, std::collections::HashMap::new());
    assert_eq!(shared_blasts, distinct);
    assert_eq!(every_blasts, occurrences);
    assert_eq!((shared_lhs, shared_rhs), (every_lhs, every_rhs));

    // Encoding: the bounded (memoized) CNF is the per-occurrence one.
    let preflight = preflight_bv_equality(&lhs, &rhs, &limits(), &mut || true).unwrap();
    let memoized = build(&lhs, &rhs, Some((&limits(), preflight)), &mut || true).unwrap();
    let unshared = build(&lhs, &rhs, None, &mut || true).unwrap();
    assert_eq!(memoized, unshared);
}

#[test]
fn the_node_cap_counts_distinct_nodes_and_the_occurrence_cap_counts_the_tree() {
    let lhs = doubled(10);
    let rhs = BvExpr::leaf("c", 16);
    let census = preflight_bv_equality(&lhs, &rhs, &limits(), &mut || true).unwrap();
    assert!(census.occurrences > 4 * census.nodes);

    let mut exact = limits();
    exact.max_expr_nodes = census.nodes;
    exact.max_expr_occurrences = census.occurrences;
    assert!(preflight_bv_equality(&lhs, &rhs, &exact, &mut || true).is_ok());

    let mut short = exact.clone();
    short.max_expr_nodes -= 1;
    assert!(matches!(
        preflight_bv_equality(&lhs, &rhs, &short, &mut || true),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression nodes",
            ..
        })
    ));
    let mut short = exact;
    short.max_expr_occurrences -= 1;
    assert!(matches!(
        preflight_bv_equality(&lhs, &rhs, &short, &mut || true),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression occurrences",
            ..
        })
    ));
}
