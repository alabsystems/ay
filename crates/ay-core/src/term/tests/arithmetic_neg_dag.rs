// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The former recursive addition branch, retained here only for small-tree
/// constructor/footprint comparison.
fn recursive_neg_reference(store: &mut TermStore, arg: TermId) -> TermId {
    if let TermData::App(Symbol::Named(name), args) = store.get(arg).clone() {
        if name == "+" {
            let negated = args
                .into_iter()
                .map(|child| recursive_neg_reference(store, child))
                .collect();
            return store.mk_add(negated);
        }
    }
    store.mk_neg(arg)
}

#[test]
fn negating_raw_shared_addition_dag_visits_each_node_once() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let mut shared = x;
    for _ in 0..72 {
        shared = store.mk_app(Symbol::named("+"), [shared, shared], Sort::Int);
    }

    let negated = store.mk_neg(shared);
    let coefficient = store.mk_int(-(BigInt::from(1) << 72usize));
    let expected = store.mk_mul(vec![coefficient, x]);
    assert_eq!(negated, expected);
    assert!(
        store.len() < 300,
        "negation should not expand the shared DAG"
    );
}

#[test]
fn negating_deep_raw_unary_addition_does_not_use_the_call_stack() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let mut nested = x;
    for _ in 0..20_000 {
        nested = store.mk_app(Symbol::named("+"), [nested], Sort::Int);
    }

    let negated = store.mk_neg(nested);
    assert_eq!(negated, store.mk_neg(x));
}

#[test]
fn negating_small_addition_preserves_constructor_order_and_footprint() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let three = store.mk_int(BigInt::from(3));
    let left = store.mk_app(Symbol::named("+"), [x, three], Sort::Int);
    let right = store.mk_app(Symbol::named("+"), [left, y], Sort::Int);
    let root = store.mk_app(Symbol::named("+"), [left, right, left], Sort::Int);
    let mut reference = store.clone();

    let actual = store.mk_neg(root);
    let expected = recursive_neg_reference(&mut reference, root);
    assert_eq!(actual, expected);
    assert_eq!(store.len(), reference.len());
    for index in 0..store.len() {
        let id = TermId(index as u32);
        assert_eq!(store.get(id), reference.get(id), "term {index} differs");
        assert_eq!(store.sort(id), reference.sort(id), "sort {index} differs");
    }
}

#[test]
fn negating_small_real_addition_preserves_constructor_order_and_footprint() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let three_halves = store.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
    let left = store.mk_app(Symbol::named("+"), [x, three_halves], Sort::Real);
    let right = store.mk_app(Symbol::named("+"), [left, y], Sort::Real);
    let root = store.mk_app(Symbol::named("+"), [right, left, right], Sort::Real);
    let mut reference = store.clone();

    let actual = store.mk_neg(root);
    let expected = recursive_neg_reference(&mut reference, root);
    assert_eq!(actual, expected);
    assert_eq!(store.len(), reference.len());
    for index in 0..store.len() {
        let id = TermId(index as u32);
        assert_eq!(store.get(id), reference.get(id), "term {index} differs");
        assert_eq!(store.sort(id), reference.sort(id), "sort {index} differs");
    }
}
