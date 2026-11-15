// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn int_fn(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Int)
}

fn same_class(closure: &mut Closure, a: TermId, b: TermId) -> bool {
    let (a, b) = (closure.node(a), closure.node(b));
    closure.find(a) == closure.find(b)
}

#[test]
fn an_equality_joins_the_applications_over_its_sides() {
    let mut terms = TermStore::new();
    let (a, b) = (terms.mk_var("a", Sort::Int), terms.mk_var("b", Sort::Int));
    let (fa, fb) = (
        int_fn(&mut terms, "f", vec![a]),
        int_fn(&mut terms, "f", vec![b]),
    );
    let (gfa, gfb) = (
        int_fn(&mut terms, "g", vec![fa, a]),
        int_fn(&mut terms, "g", vec![fb, b]),
    );
    let mut closure = Closure::new(&terms, &[gfa, gfb]);
    assert!(!same_class(&mut closure, fa, fb));

    let (na, nb) = (closure.node(a), closure.node(b));
    assert!(closure.assert_equal(na, nb));

    assert!(same_class(&mut closure, fa, fb));
    assert!(same_class(&mut closure, gfa, gfb));
    let class = closure.find(na);
    assert_eq!(closure.class_size(class), 2);
    assert!(!closure.assert_equal(na, nb), "already one class");
}

#[test]
fn a_different_function_symbol_is_not_joined() {
    let mut terms = TermStore::new();
    let (a, b) = (terms.mk_var("a", Sort::Int), terms.mk_var("b", Sort::Int));
    let (fa, hb) = (
        int_fn(&mut terms, "f", vec![a]),
        int_fn(&mut terms, "h", vec![b]),
    );
    let mut closure = Closure::new(&terms, &[fa, hb]);

    let (na, nb) = (closure.node(a), closure.node(b));
    assert!(closure.assert_equal(na, nb));

    assert!(!same_class(&mut closure, fa, hb));
}

#[test]
fn a_chain_of_equalities_reaches_through_nested_applications() {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = (0..4)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    let deep: Vec<TermId> = vars
        .iter()
        .map(|&x| {
            let inner = int_fn(&mut terms, "f", vec![x]);
            int_fn(&mut terms, "f", vec![inner])
        })
        .collect();
    let mut closure = Closure::new(&terms, &deep);

    for pair in vars.windows(2) {
        let (a, b) = (closure.node(pair[0]), closure.node(pair[1]));
        assert!(closure.assert_equal(a, b));
    }

    assert!(same_class(&mut closure, deep[0], deep[3]));
}

#[test]
fn two_values_are_never_joined() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let (one, two) = (terms.mk_int(BigInt::from(1)), terms.mk_int(BigInt::from(2)));
    let (f1, f2) = (
        int_fn(&mut terms, "f", vec![one]),
        int_fn(&mut terms, "f", vec![two]),
    );
    let mut closure = Closure::new(&terms, &[x, f1, f2]);
    let (nx, n1, n2) = (closure.node(x), closure.node(one), closure.node(two));

    assert!(closure.assert_equal(nx, n1));
    assert!(!closure.assert_equal(nx, n2), "the class already holds 1");

    assert!(!same_class(&mut closure, one, two));
    assert!(!same_class(&mut closure, f1, f2));
}

#[test]
fn the_body_of_a_quantifier_is_not_a_node() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let bound = terms.mk_var("k", Sort::Int);
    let fa = int_fn(&mut terms, "f", vec![a]);
    let body = terms.mk_le(bound, fa);
    let quantified = terms.mk_forall(vec![("k".to_string(), Sort::Int)], body);

    let closure = Closure::new(&terms, &[quantified]);

    assert_eq!(closure.len(), 1, "the quantified term is a leaf");
    assert!(closure.children(closure.node(quantified)).is_empty());
}
