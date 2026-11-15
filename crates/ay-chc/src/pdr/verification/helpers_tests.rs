// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The verification case-split surface scan on shared DAGs.

use super::*;

fn x() -> ChcExpr {
    ChcExpr::var(ChcVar::new("x", ChcSort::Int))
}

fn op(op: ChcOp, args: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Op(op, args))
}

/// `c(0) = bottom`, `c(i+1) = (c(i) and x <= i) and (c(i) and x >= -i)`: no
/// surface above `bottom`, `2^depth` tree copies of it, height `2*depth`.
fn shared_conjunction_chain(depth: i64, bottom: ChcExpr) -> Arc<ChcExpr> {
    let mut c = Arc::new(bottom);
    for i in 0..depth {
        let left = op(
            ChcOp::And,
            vec![Arc::clone(&c), Arc::new(ChcExpr::le(x(), ChcExpr::int(i)))],
        );
        let right = op(
            ChcOp::And,
            vec![Arc::clone(&c), Arc::new(ChcExpr::ge(x(), ChcExpr::int(-i)))],
        );
        c = op(ChcOp::And, vec![left, right]);
    }
    c
}

fn not_eq_one() -> ChcExpr {
    ChcExpr::Op(
        ChcOp::Not,
        vec![Arc::new(ChcExpr::eq(x(), ChcExpr::int(1)))],
    )
}

/// Every path is shorter than the depth cap, so the scan runs on the
/// distinct nodes: it finds the surface at the bottom of a `2^50`-copy DAG,
/// and answers `false` without one (where the tree walk never returned).
#[test]
#[ntest::timeout(60_000)]
fn the_surface_scan_is_linear_on_a_shared_dag() {
    let with_surface = shared_conjunction_chain(50, not_eq_one());
    let without = shared_conjunction_chain(50, ChcExpr::le(x(), ChcExpr::int(0)));

    assert!(PdrSolver::has_verification_case_split_surface(
        &with_surface
    ));
    assert!(!PdrSolver::has_verification_case_split_surface(&without));
}

/// Negative twin: a path that reaches the depth cap keeps the tree walk and
/// its answer. The walk pops the deep `not` chain first and gives up at depth
/// 128, before it reaches the surface in the shared DAG (or the `or` at the
/// bottom of the chain); a plain distinct-node scan would answer `true`.
#[test]
#[ntest::timeout(60_000)]
fn a_path_past_the_depth_cap_keeps_the_tree_walks_answer() {
    let mut deep = op(
        ChcOp::Or,
        vec![
            Arc::new(ChcExpr::le(x(), ChcExpr::int(0))),
            Arc::new(ChcExpr::ge(x(), ChcExpr::int(1))),
        ],
    );
    for _ in 0..130 {
        deep = op(ChcOp::Not, vec![deep]);
    }
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![shared_conjunction_chain(50, not_eq_one()), deep],
    );

    assert!(!PdrSolver::has_verification_case_split_surface(&expr));
}
