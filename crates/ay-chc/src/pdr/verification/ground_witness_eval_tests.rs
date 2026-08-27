// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground-witness evaluation regressions for array counterexample verification.

#![cfg(test)]

use super::*;

/// Fully-ground swaparray-shaped query: div + const-array/store
/// disequality must evaluate to true (the FM2b override witness).
#[test]
fn ground_query_decides_fully_ground_array_diseq_with_div() {
    let div = ChcExpr::Op(
        ChcOp::Div,
        vec![
            ChcExpr::add(
                ChcExpr::Int(4),
                ChcExpr::mul(ChcExpr::Int(-1), ChcExpr::Int(0)),
            )
            .into(),
            ChcExpr::Int(4).into(),
        ],
    );
    let arr1 = ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(1));
    let arr2 = ChcExpr::store(
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
        ChcExpr::Int(5),
        ChcExpr::Int(1),
    );
    let query = ChcExpr::and_all([
        ChcExpr::le(ChcExpr::Int(1), div),
        ChcExpr::le(ChcExpr::Int(0), ChcExpr::Int(0)),
        ChcExpr::not(ChcExpr::eq(arr1, arr2)),
    ]);
    assert!(
        ground_query_witness_evaluates_true(&query),
        "fully ground array+div query must evaluate to true"
    );
}

/// Bindings-based query: `I = const-array(1) ∧ J = store(...) ∧ I ≠ J`
/// must evaluate to true after substitution.
#[test]
fn ground_query_decides_bound_array_diseq() {
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let i = ChcVar::new("I", arr_sort.clone());
    let j = ChcVar::new("J", arr_sort);
    let arr1 = ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(1));
    let arr2 = ChcExpr::store(
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
        ChcExpr::Int(5),
        ChcExpr::Int(1),
    );
    let query = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(i.clone()), arr1),
        ChcExpr::eq(ChcExpr::var(j.clone()), arr2),
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(i), ChcExpr::var(j))),
    ]);
    assert!(
        ground_query_witness_evaluates_true(&query),
        "bound array disequality query must evaluate to true"
    );
}

/// A genuinely false ground query must NOT be overridden.
#[test]
fn ground_query_rejects_false_ground_query() {
    let query = ChcExpr::and_all([
        ChcExpr::le(ChcExpr::Int(1), ChcExpr::Int(0)),
        ChcExpr::Bool(true),
    ]);
    assert!(
        !ground_query_witness_evaluates_true(&query),
        "false ground query must not be overridden"
    );
}

/// Conflicting duplicate bindings degrade to false (no override).
#[test]
fn ground_query_rejects_conflicting_bindings() {
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(2)),
    ]);
    assert!(
        !ground_query_witness_evaluates_true(&query),
        "conflicting bindings must not be overridden"
    );
}
