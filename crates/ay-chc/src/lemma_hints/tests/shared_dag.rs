// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular hint extraction on a shared DAG: one visit per distinct sub-term.

use super::*;
use std::sync::Arc;

/// `c(0) = ((y mod 4) = 1 and z = 3 * x)`, `c(i+1) = (c(i) and x <= i) or
/// (c(i) and y >= i)`: `2^depth` tree copies of `c(0)`.
fn shared_mod_chain(depth: usize) -> ChcExpr {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let mut c = Arc::new(ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(
                ChcExpr::mod_op(y.clone(), ChcExpr::int(4)),
                ChcExpr::int(1),
            )),
            Arc::new(ChcExpr::eq(z, ChcExpr::mul(ChcExpr::int(3), x.clone()))),
        ],
    ));
    for i in 0..depth {
        let bound = ChcExpr::int(i as i64);
        let left = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::clone(&c),
                Arc::new(ChcExpr::le(x.clone(), bound.clone())),
            ],
        );
        let right = ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&c), Arc::new(ChcExpr::ge(y.clone(), bound))],
        );
        c = Arc::new(ChcExpr::Op(
            ChcOp::Or,
            vec![Arc::new(left), Arc::new(right)],
        ));
    }
    Arc::unwrap_or_clone(c)
}

/// The tree walks never returned on this `2^60`-copy DAG; the distinct walks
/// visit the one `mod` and the one `*` node a bounded number of times.
#[test]
#[ntest::timeout(60_000)]
fn mod_and_divisibility_terms_of_a_shared_dag_are_collected_once() {
    let expr = shared_mod_chain(60);
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    // The distinct walk skips repeats only after its first 512 pops; the
    // caller sorts and deduplicates.
    let mut divisibility = ModResidueHintProvider::extract_divisibility_terms(&expr);
    assert!(divisibility.len() < 600, "{} visits", divisibility.len());
    divisibility.dedup();
    assert_eq!(divisibility, vec![(x, 3)]);
    assert_eq!(
        ModResidueHintProvider::extract_mod_terms(&expr),
        vec![(y, 4)]
    );
}
