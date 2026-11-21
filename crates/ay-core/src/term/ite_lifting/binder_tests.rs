// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fixture(terms: &mut TermStore) -> (TermId, TermId, Vec<TermId>) {
    let bound = terms.mk_var("bound", Sort::Int);
    let outer = terms.mk_var("outer", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let rem = terms.mk_mod(bound, two);
    let even = terms.mk_eq(rem, zero);
    let value = terms.mk_ite(even, one, zero);
    let lambda = terms.mk_lambda_array(bound, value);
    let nested = terms.mk_lambda_array(outer, lambda);
    let alias = terms.mk_var("array", terms.sort(lambda).clone());
    let equality = terms.mk_eq(alias, lambda);
    let predicate = terms.mk_eq(value, one);
    let forall = terms.mk_forall(vec![("bound".to_owned(), Sort::Int)], predicate);
    let exists = terms.mk_exists(vec![("bound".to_owned(), Sort::Int)], predicate);
    let let_term = terms.mk_let(vec![("bound".to_owned(), two)], value);
    (
        lambda,
        value,
        vec![lambda, nested, equality, forall, exists, let_term],
    )
}

#[test]
fn lambda_arithmetic_lifting_keeps_every_binder_and_alias_in_scope() {
    let mut terms = TermStore::new();
    let (_, _, roots) = fixture(&mut terms);
    assert_eq!(terms.lift_arithmetic_ite_all(&roots), roots);
    let mut definitions = Vec::new();
    assert_eq!(
        terms.name_non_bool_ites_all(&roots, &mut definitions),
        roots
    );
    assert!(definitions.is_empty());
}

#[test]
fn lambda_arithmetic_lifting_does_not_disable_ground_shared_ite_naming() {
    for lambda_first in [false, true] {
        let mut terms = TermStore::new();
        let (lambda, body, _) = fixture(&mut terms);
        let roots = if lambda_first {
            [lambda, body]
        } else {
            [body, lambda]
        };
        let mut definitions = Vec::new();
        let rebuilt = terms.name_non_bool_ites_all(&roots, &mut definitions);
        let lambda_index = usize::from(!lambda_first);
        assert_eq!(rebuilt[lambda_index], lambda);
        assert_ne!(rebuilt[1 - lambda_index], body);
        assert_eq!(definitions.len(), 2);
    }
}

#[test]
fn lambda_arithmetic_lifting_leaves_beta_reduced_ground_reads_eligible() {
    let mut terms = TermStore::new();
    let (lambda, _, _) = fixture(&mut terms);
    let x = terms.mk_var("free_x", Sort::Int);
    let one = terms.mk_int(1.into());
    let read = terms.mk_select(lambda, x);
    let predicate = terms.mk_app(Symbol::named("="), [read, one], Sort::Bool);
    let lifted = terms.lift_arithmetic_ite(predicate);
    let two = terms.mk_int(2.into());
    let zero = terms.mk_int(0.into());
    let remainder = terms.mk_mod(x, two);
    let expected = terms.mk_eq(remainder, zero);
    assert_ne!(lifted, predicate);
    assert_eq!(lifted, expected);
}
