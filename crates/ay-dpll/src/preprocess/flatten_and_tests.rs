// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

#[test]
fn test_flatten_simple_and() {
    let mut terms = TermStore::new();

    // Create: (and a b)
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);

    let mut assertions = vec![and_ab];
    let mut pass = FlattenAnd::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);
    assert_eq!(assertions.len(), 2);
    assert!(assertions.contains(&a));
    assert!(assertions.contains(&b));
}

#[test]
fn test_flatten_nested_and() {
    let mut terms = TermStore::new();

    // Create: (and (and a b) (and c d))
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);
    let and_cd = terms.mk_and(vec![c, d]);
    let and_all = terms.mk_and(vec![and_ab, and_cd]);

    let mut assertions = vec![and_all];
    let mut pass = FlattenAnd::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);
    assert_eq!(assertions.len(), 4);
    assert!(assertions.contains(&a));
    assert!(assertions.contains(&b));
    assert!(assertions.contains(&c));
    assert!(assertions.contains(&d));
}

#[test]
fn test_flatten_no_change() {
    let mut terms = TermStore::new();

    // Create individual assertions (no ANDs)
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);

    let mut assertions = vec![a, b];
    let mut pass = FlattenAnd::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(!modified);
    assert_eq!(assertions.len(), 2);
}

// Note: No test for (and a a) because mk_and already deduplicates,
// so mk_and(vec![a, a]) returns just 'a', not an AND term.
