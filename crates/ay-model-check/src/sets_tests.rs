// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the exact finite-set operations.

use num_bigint::BigInt;

use super::{card, eval, handles, subset, DomainSize};
use crate::{ArrayValue, ModelValue};

fn i(v: i64) -> ModelValue {
    ModelValue::Int(BigInt::from(v))
}

/// A set as its membership carrier: a default plus `index -> in/out`
/// overrides, oldest first.
fn set(default: bool, entries: &[(i64, bool)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Bool(default),
        store: entries
            .iter()
            .map(|&(k, v)| (i(k), ModelValue::Bool(v)))
            .collect(),
    }))
}

#[track_caller]
fn card_of(s: &ModelValue) -> i64 {
    match card(s, &DomainSize::Infinite).unwrap() {
        ModelValue::Int(n) => i64::try_from(n).unwrap(),
        other => panic!("expected an integer, got {other:?}"),
    }
}

#[track_caller]
fn is_subset(a: &ModelValue, b: &ModelValue) -> bool {
    match subset(a, b, &DomainSize::Infinite).unwrap() {
        ModelValue::Bool(v) => v,
        other => panic!("expected a boolean, got {other:?}"),
    }
}

#[test]
fn card_counts_members_not_overrides() {
    assert_eq!(card_of(&set(false, &[])), 0, "the empty set");
    assert_eq!(card_of(&set(false, &[(1, true), (2, true)])), 2);
    // An override to NON-membership is still an override; it must not be
    // counted, which a naive `store.len()` would do.
    assert_eq!(card_of(&set(false, &[(1, true), (2, false), (3, true)])), 2);
    assert_eq!(card_of(&set(false, &[(1, false), (2, false)])), 0);
}

/// The newest write at an index wins, so an index written twice is ONE element
/// — and its value is the later one.
#[test]
fn card_respects_shadowed_writes() {
    assert_eq!(
        card_of(&set(false, &[(1, true), (1, true)])),
        1,
        "counted once"
    );
    assert_eq!(
        card_of(&set(false, &[(1, true), (1, false)])),
        0,
        "the later write removes it"
    );
    assert_eq!(
        card_of(&set(false, &[(1, false), (1, true)])),
        1,
        "and can add it back"
    );
    assert_eq!(card_of(&set(false, &[(1, true), (2, true), (1, false)])), 1);
}

/// A set that defaults to membership has infinitely many elements, so its
/// cardinality is not a natural number. Counting the overrides would produce a
/// confidently wrong small answer.
#[test]
fn card_of_a_cofinite_set_is_refused() {
    assert!(card(&set(true, &[]), &DomainSize::Infinite).is_err());
    assert!(card(&set(true, &[(1, false)]), &DomainSize::Infinite).is_err());
    assert!(
        card(&ModelValue::Int(BigInt::from(3)), &DomainSize::Infinite).is_err(),
        "not a set at all"
    );
}

#[test]
fn subset_checks_every_member() {
    let empty = set(false, &[]);
    let one_two = set(false, &[(1, true), (2, true)]);
    let one_two_three = set(false, &[(1, true), (2, true), (3, true)]);

    assert!(
        is_subset(&empty, &one_two),
        "the empty set is a subset of everything"
    );
    assert!(is_subset(&empty, &empty));
    assert!(is_subset(&one_two, &one_two), "a set is a subset of itself");
    assert!(is_subset(&one_two, &one_two_three));
    assert!(!is_subset(&one_two_three, &one_two), "3 is missing");
    assert!(!is_subset(&one_two, &empty));
}

/// The witness to a failed subset can be an index that only the SUPERSET
/// candidate overrides — a check that walks only `a`'s store still finds it,
/// but one that compares store lengths or defaults alone does not.
#[test]
fn subset_looks_at_indices_from_both_stores() {
    let a = set(false, &[(1, true), (2, true)]);
    let b = set(false, &[(1, true), (2, false), (3, true)]);
    assert!(!is_subset(&a, &b), "2 is explicitly excluded from b");
    let c = set(false, &[(1, true), (2, true), (3, false)]);
    assert!(is_subset(&a, &c), "b's exclusion of 3 is irrelevant to a");
}

/// Outside both stores every index takes the defaults, so the defaults decide
/// that whole region at once.
#[test]
fn subset_reasons_about_the_indices_outside_both_stores() {
    // Both cofinite: outside the stores both contain everything, so only the
    // overrides matter.
    assert!(is_subset(&set(true, &[]), &set(true, &[])));
    assert!(
        !is_subset(&set(true, &[]), &set(true, &[(5, false)])),
        "b excludes 5 and a does not"
    );
    assert!(is_subset(&set(true, &[(5, false)]), &set(true, &[])));
    // A finite set inside a cofinite one.
    assert!(is_subset(&set(false, &[(1, true)]), &set(true, &[])));
    assert!(!is_subset(
        &set(false, &[(1, true)]),
        &set(true, &[(1, false)])
    ));
    // Cofinite inside finite turns on whether an uncovered index exists, which
    // is a fact about the ELEMENT SORT.
    assert!(
        !is_subset(&set(true, &[]), &set(false, &[])),
        "over an infinite domain there is always an uncovered index"
    );
    // Over a domain small enough for the stores to cover, there is not.
    let two = DomainSize::Finite(BigInt::from(2));
    assert_eq!(
        subset(
            &set(true, &[(0, true), (1, true)]),
            &set(false, &[(0, true), (1, true)]),
            &two
        )
        .unwrap()
        .as_bool(),
        Some(true),
        "both indices of a 2-element domain are covered and agree"
    );
    assert_eq!(
        subset(&set(true, &[(0, true)]), &set(false, &[(0, true)]), &two)
            .unwrap()
            .as_bool(),
        Some(false),
        "index 1 is uncovered, and it is in a but not b"
    );
    // An unknown domain is refused rather than assumed infinite.
    assert!(subset(&set(true, &[]), &set(false, &[]), &DomainSize::Unknown).is_err());
}

#[test]
fn dispatch_and_wrong_shapes() {
    assert!(handles("set.card", 1));
    assert!(handles("set.subset", 2));
    assert!(!handles("set.card", 2), "arity is part of the dispatch");
    assert!(!handles("set.union", 2), "not implemented, so not claimed");
    assert!(eval(
        "set.union",
        &[set(false, &[]), set(false, &[])],
        &DomainSize::Infinite
    )
    .is_err());
    assert!(eval(
        "set.card",
        &[set(false, &[]), set(false, &[])],
        &DomainSize::Infinite
    )
    .is_err());
    // A carrier whose entries are not boolean is malformed, not coerced.
    let bad = ModelValue::Array(Box::new(ArrayValue {
        default: i(0),
        store: Vec::new(),
    }));
    assert!(card(&bad, &DomainSize::Infinite).is_err());
}

/// Over a FINITE element sort a set that defaults to membership still has a
/// definite size: the domain less the exclusions.
#[test]
fn card_of_a_cofinite_set_over_a_finite_domain_is_counted() {
    let four = DomainSize::Finite(BigInt::from(4));
    let all = set(true, &[]);
    assert_eq!(card(&all, &four).unwrap().as_bool(), None);
    match card(&all, &four).unwrap() {
        ModelValue::Int(n) => assert_eq!(n, BigInt::from(4)),
        other => panic!("expected an integer, got {other:?}"),
    }
    match card(&set(true, &[(0, false), (1, false)]), &four).unwrap() {
        ModelValue::Int(n) => assert_eq!(n, BigInt::from(2), "two of four excluded"),
        other => panic!("expected an integer, got {other:?}"),
    }
    // An override back to membership is not an exclusion.
    match card(&set(true, &[(0, false), (0, true)]), &four).unwrap() {
        ModelValue::Int(n) => assert_eq!(n, BigInt::from(4)),
        other => panic!("expected an integer, got {other:?}"),
    }
    // Unknown or infinite domains still refuse.
    assert!(card(&all, &DomainSize::Unknown).is_err());
    assert!(card(&all, &DomainSize::Infinite).is_err());
}
