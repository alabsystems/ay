// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn raw_plus(store: &mut TermStore, sort: &Sort, a: TermId, b: TermId) -> TermId {
    store.mk_app(Symbol::named("+"), [a, b], sort.clone())
}

/// The previous recursive distribution, for small-tree footprint comparison.
fn recursive_mul_reference(store: &mut TermStore, coefficient: TermId, term: TermId) -> TermId {
    if let TermData::App(Symbol::Named(name), args) = store.get(term).clone() {
        if name == "+" && args.len() >= 2 {
            let products = args
                .into_iter()
                .map(|child| recursive_mul_reference(store, coefficient, child))
                .collect();
            return store.mk_add(products);
        }
    }
    store.mk_mul(vec![coefficient, term])
}

#[test]
fn constant_times_shared_72_level_addition_dag_normalizes_exactly() {
    for sort in [Sort::Int, Sort::Real] {
        let mut store = TermStore::new();
        let x = store.mk_var("x", sort.clone());
        let mut shared = x;
        for _ in 0..72 {
            shared = raw_plus(&mut store, &sort, shared, shared);
        }
        let two = match &sort {
            Sort::Int => store.mk_int(BigInt::from(2)),
            _ => store.mk_rational(BigRational::from_integer(BigInt::from(2))),
        };
        let product = store.mk_mul(vec![two, shared]);
        let positive_coefficient = BigInt::from(1) << 73usize;
        let positive = match &sort {
            Sort::Int => store.mk_int(positive_coefficient),
            _ => store.mk_rational(BigRational::from_integer(positive_coefficient)),
        };
        let expected = store.mk_mul(vec![positive, x]);
        assert_eq!(product, expected, "shared DAG must fully normalize");
        let minus_one = match &sort {
            Sort::Int => store.mk_int(BigInt::from(-1)),
            _ => store.mk_rational(BigRational::from_integer(BigInt::from(-1))),
        };
        let negative = store.mk_mul(vec![minus_one, shared]);
        let negative_coefficient = -(BigInt::from(1) << 72usize);
        let coefficient = match &sort {
            Sort::Int => store.mk_int(negative_coefficient),
            _ => store.mk_rational(BigRational::from_integer(negative_coefficient)),
        };
        let expected = store.mk_mul(vec![coefficient, x]);
        assert_eq!(negative, expected, "negative shared DAG also normalizes");
        assert!(
            store.len() < 500,
            "both shared DAG constructors should use linear-size storage"
        );
    }
}

#[test]
fn constant_times_deep_addition_chain_does_not_recurse() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let two = store.mk_int(BigInt::from(2));
    let mut deep = x;
    for _ in 0..20_000 {
        deep = raw_plus(&mut store, &Sort::Int, deep, zero);
    }
    let before = store.len();
    let product = store.mk_mul(vec![two, deep]);
    assert_eq!(product, store.mk_mul(vec![two, x]));
    assert!(store.len() <= before + 1, "deep zero additions collapse");
}

#[test]
fn unequal_shared_coefficients_normalize_without_tree_expansion() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let three = store.mk_int(BigInt::from(3));
    let three_y = store.mk_mul(vec![three, y]);
    let mut shared = raw_plus(&mut store, &Sort::Int, x, three_y);
    for _ in 0..72 {
        shared = raw_plus(&mut store, &Sort::Int, shared, shared);
    }
    let two = store.mk_int(BigInt::from(2));
    let product = store.mk_mul(vec![two, shared]);
    let factor = BigInt::from(1) << 73usize;
    let x_coefficient = store.mk_int(factor.clone());
    let y_coefficient = store.mk_int(factor * BigInt::from(3));
    let x_term = store.mk_mul(vec![x_coefficient, x]);
    let y_term = store.mk_mul(vec![y_coefficient, y]);
    assert_eq!(product, store.mk_add(vec![x_term, y_term]));
    assert!(store.len() < 500);
}

#[test]
fn mk_add_duplicate_shared_rest_reaches_dag_safe_multiplication() {
    let mut store = TermStore::new();
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);
    let product = store.mk_mul(vec![v, w]);
    let mut free_rest = w;
    for _ in 0..72 {
        free_rest = raw_plus(&mut store, &Sort::Int, free_rest, free_rest);
    }
    // `mk_add` flattens the outer raw `+`, sees two identical level-71
    // children, and calls `mk_mul(2, child)` while combining coefficients.
    // This is the actual constructor route that stalled the D11 fixture.
    let combined = store.mk_add(vec![product, free_rest]);
    let coefficient = store.mk_int(BigInt::from(1) << 72usize);
    let scaled_w = store.mk_mul(vec![coefficient, w]);
    assert_eq!(combined, store.mk_add(vec![product, scaled_w]));
    assert!(store.len() < 500, "the shared tree stays compact");
}

#[test]
fn small_int_and_real_distribution_retains_exact_termstore_footprint() {
    for sort in [Sort::Int, Sort::Real] {
        let setup = || {
            let mut store = TermStore::new();
            let x = store.mk_var("x", sort.clone());
            let y = store.mk_var("y", sort.clone());
            let two = match &sort {
                Sort::Int => store.mk_int(BigInt::from(2)),
                _ => store.mk_rational(BigRational::from_integer(BigInt::from(2))),
            };
            let sum = store.mk_add(vec![x, y]);
            (store, x, y, two, sum)
        };
        let (mut actual, _, _, two, sum) = setup();
        let product = actual.mk_mul(vec![two, sum]);
        let (mut historical, x, y, two, _) = setup();
        let left = historical.mk_mul(vec![two, x]);
        let right = historical.mk_mul(vec![two, y]);
        let expected = historical.mk_add(vec![left, right]);
        assert_eq!(product, expected, "same result TermId for {sort:?}");
        assert_eq!(actual.len(), historical.len(), "same intern count");
        for (a, b) in actual.term_ids().zip(historical.term_ids()) {
            assert_eq!(actual.get(a), historical.get(b), "term {a:?}");
            assert_eq!(actual.sort(a), historical.sort(b), "sort {a:?}");
        }
    }
}

#[test]
fn small_nested_distribution_matches_recursive_order_and_footprint() {
    for sort in [Sort::Int, Sort::Real] {
        for shared_child in [false, true] {
            for (numerator, denominator) in [(0, 1), (1, 1), (-1, 1), (2, 1), (1, 2)] {
                if sort == Sort::Int && denominator != 1 {
                    continue;
                }
                let mut store = TermStore::new();
                let x = store.mk_var("x", sort.clone());
                let y = store.mk_var("y", sort.clone());
                let coefficient = match &sort {
                    Sort::Int => store.mk_int(BigInt::from(numerator)),
                    _ => store.mk_rational(BigRational::new(
                        BigInt::from(numerator),
                        BigInt::from(denominator),
                    )),
                };
                let child = raw_plus(&mut store, &sort, x, y);
                let root = raw_plus(
                    &mut store,
                    &sort,
                    child,
                    if shared_child { child } else { x },
                );
                let mut reference = store.clone();
                let actual = store.mk_mul(vec![coefficient, root]);
                let expected = match numerator {
                    0 => coefficient,
                    1 if denominator == 1 => root,
                    -1 => reference.mk_neg(root),
                    _ => recursive_mul_reference(&mut reference, coefficient, root),
                };
                assert_eq!(
                    actual, expected,
                    "{sort:?}, {numerator}/{denominator}, shared={shared_child}"
                );
                assert_eq!(store.len(), reference.len());
                for (a, b) in store.term_ids().zip(reference.term_ids()) {
                    assert_eq!(store.get(a), reference.get(b), "term {a:?}");
                    assert_eq!(store.sort(a), reference.sort(b), "sort {a:?}");
                }
            }
        }
    }
}

#[test]
fn alternating_raw_add_mul_chain_retains_exact_compact_product() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let mut alternating = x;
    for _ in 0..20_000 {
        let plus = raw_plus(&mut store, &Sort::Int, alternating, zero);
        alternating = store.mk_app(Symbol::named("*"), [one, plus], Sort::Int);
    }
    let before = store.len();
    let product = store.mk_mul(vec![two, alternating]);
    // The constructor flattens the outer raw `*`, then its bounded reentry
    // preflight retains the algebraically exact product without expanding the
    // alternating raw structure through thousands of recursive calls.
    assert!(
        matches!(store.get(product), TermData::App(Symbol::Named(name), args)
        if name == "*" && args.len() == 2 && args.contains(&two))
    );
    assert!(store.len() <= before + 1);
}
