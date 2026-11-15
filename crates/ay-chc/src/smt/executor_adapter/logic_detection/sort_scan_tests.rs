// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `detect_logic`'s sort scans on shared DAGs whose tree is exponential: the
//! scan must switch to its DAG walk (one visit per distinct node) and give
//! the tree walk's answer. The `2^64`-occurrence inputs make any regression to
//! a pure tree walk hang instead of merely running slower.

use super::*;
use crate::ChcOp;

/// `t(0) = leaf`, `t(i+1) = t(i) + (t(i) ^ 1)`: `2^depth` tree occurrences
/// of `leaf`, `depth + 1` distinct nodes.
fn shared_bv_chain(depth: usize, leaf: ChcExpr) -> ChcExpr {
    let mut t = Arc::new(leaf);
    for _ in 0..depth {
        let mixed = Arc::new(ChcExpr::Op(
            ChcOp::BvXor,
            vec![Arc::clone(&t), Arc::new(ChcExpr::BitVec(1, 8))],
        ));
        t = Arc::new(ChcExpr::Op(ChcOp::BvAdd, vec![Arc::clone(&t), mixed]));
    }
    Arc::unwrap_or_clone(t)
}

/// A pure-BV query over a `2^64`-occurrence DAG: every Int/Real/array/DT
/// scan finds nothing, so it spends the plain walk's visit budget and must
/// finish on the DAG walk.
#[test]
#[ntest::timeout(60_000)]
fn a_pure_bv_shared_dag_is_scanned_once_per_node() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let expr = ChcExpr::Op(
        ChcOp::BvULe,
        vec![
            Arc::new(shared_bv_chain(64, ChcExpr::var(x.clone()))),
            Arc::new(ChcExpr::BitVec(9, 8)),
        ],
    );

    assert!(!expr_sort_has(&expr, sort_contains_int));
    assert!(expr_sort_has(&expr, sort_contains_bv));
    assert_eq!(detect_logic(&[x], &expr), "QF_UFBV");
}

/// Negative twin: the only Int is `int2bv i`, a sibling of the shared chain
/// that only the expression, not the variable list, reveals. With the chain
/// on either side, one order makes the plain walk spend its visit budget
/// inside the chain before it reaches `i`; the DAG walk it falls back to must
/// still find `i`, and the logic widens to `ALL`.
#[test]
#[ntest::timeout(60_000)]
fn an_int_beside_the_shared_chain_is_still_found() {
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
    let int_leaf = Arc::new(ChcExpr::Op(ChcOp::Int2Bv(8), vec![Arc::new(i)]));
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let chain = Arc::new(shared_bv_chain(64, x));
    for args in [
        vec![Arc::clone(&int_leaf), Arc::clone(&chain)],
        vec![Arc::clone(&chain), Arc::clone(&int_leaf)],
    ] {
        let expr = ChcExpr::Op(ChcOp::BvULe, args);
        assert!(expr_sort_has(&expr, sort_contains_int));
        assert_eq!(detect_logic(&[], &expr), "ALL");
    }
}
