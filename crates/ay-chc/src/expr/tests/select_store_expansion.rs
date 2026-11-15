// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `expand_select_store_symbolic` on shared DAGs: an array-free query skips
//! the tree rewrite, and a `select` next to the DAG is still expanded.

use super::*;

fn int_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn node(op: ChcOp, args: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Op(op, args))
}

/// `c(0) = (x <= 5)`, `c(i+1) = (c(i) and x <= i) or (c(i) and y >= i)`:
/// `2^depth` tree copies of `c(0)`, about `5 * depth` distinct nodes, no
/// array op (the self-inductiveness query shape of a shared `let` chain).
fn shared_int_chain(depth: i64) -> Arc<ChcExpr> {
    let mut c = Arc::new(ChcExpr::le(int_var("x"), ChcExpr::int(5)));
    for i in 0..depth {
        let left = node(
            ChcOp::And,
            vec![
                Arc::clone(&c),
                Arc::new(ChcExpr::le(int_var("x"), ChcExpr::int(i))),
            ],
        );
        let right = node(
            ChcOp::And,
            vec![
                Arc::clone(&c),
                Arc::new(ChcExpr::ge(int_var("y"), ChcExpr::int(i))),
            ],
        );
        c = node(ChcOp::Or, vec![left, right]);
    }
    c
}

/// Without a `select` the rewrite is the identity, so the input comes back
/// (its own child `Arc`s) after one DAG-linear scan. The tree rewrite spent
/// its whole `MAX_PREPROCESSING_NODES` visit and allocation budget on every
/// call; the PDR self-inductiveness check calls this once per query, and on
/// a 5 s bounded solve over a shared chain that was the work left running
/// past the deadline.
#[test]
#[ntest::timeout(60_000)]
fn an_array_free_shared_dag_is_returned_without_a_tree_rewrite() {
    let chain = shared_int_chain(64);
    let ChcExpr::Op(ChcOp::Or, inputs) = chain.as_ref() else {
        panic!("the chain root is an Or");
    };
    for _ in 0..10_000 {
        let out = chain.expand_select_store_symbolic();
        let ChcExpr::Op(ChcOp::Or, outputs) = &out else {
            panic!("the result must be the input Or");
        };
        assert!(inputs
            .iter()
            .zip(outputs.iter())
            .all(|(input, output)| Arc::ptr_eq(input, output)));
    }
}

/// Negative twin: a `select` beside the same shared DAG makes the query an
/// array query, and read-over-write still rewrites it.
#[test]
#[ntest::timeout(60_000)]
fn a_select_beside_the_shared_dag_is_still_expanded() {
    let array = ChcExpr::var(ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    ));
    let read = ChcExpr::select(
        ChcExpr::store(array, ChcExpr::int(1), ChcExpr::int(5)),
        ChcExpr::int(1),
    );
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(read, int_var("z"))),
            shared_int_chain(64),
        ],
    );
    assert!(expr.contains_array_ops());

    let out = expr.expand_select_store_symbolic();
    assert!(
        !out.contains_array_ops(),
        "select(store(a, 1, 5), 1) must read 5"
    );
}
