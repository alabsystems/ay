// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structure of the negated Herbrand expansion (`qf_formula`). Semantics are
//! exercised end to end by the gate route's tests.

use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::qf_formula::{
    binder_chain, negated_expansion, ExpansionDecline, MAX_EXPANSION_INSTANCES,
};
use super::InstanceHints;
use crate::ematching::contains_quantifier;

fn real(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Real)
}

fn rat(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(n)))
}

fn bound(name: &str) -> Vec<(String, Sort)> {
    vec![(name.to_string(), Sort::Real)]
}

/// `∀x ∃y. y > x`.
fn forall_exists_gt(terms: &mut TermStore) -> (TermId, TermId) {
    let (x, y) = (real(terms, "x"), real(terms, "y"));
    let body = terms.mk_gt(y, x);
    let inner = terms.mk_exists(bound("y"), body);
    (terms.mk_forall(bound("x"), inner), inner)
}

fn mentions(terms: &TermStore, root: TermId, target: TermId) -> bool {
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if t == target {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    false
}

#[test]
fn universal_of_the_conjunct_is_skolemized_and_its_existential_expanded() {
    let mut terms = TermStore::new();
    let (root, inner) = forall_exists_gt(&mut terms);
    let (x, one) = (real(&mut terms, "x"), rat(&mut terms, 1));
    let witness = terms.mk_add(vec![x, one]);
    let mut hints = InstanceHints::default();
    hints.insert(inner, vec![vec![witness]]);
    let expansion = negated_expansion(&mut terms, root, &hints).expect("expands");
    assert!(!contains_quantifier(&terms, expansion.formula));
    assert_eq!(expansion.instances, 1);
    assert_eq!(expansion.skolems.len(), 1, "one Skolem for ∀x of R");
    let sk = expansion.skolems[0];
    assert!(mentions(&terms, expansion.formula, sk));
    assert!(
        !mentions(&terms, expansion.formula, x),
        "the enclosing binder name is replaced by its Skolem"
    );
}

#[test]
fn no_hint_expands_a_universal_of_the_negation_to_true() {
    let mut terms = TermStore::new();
    let (root, _) = forall_exists_gt(&mut terms);
    let expansion = negated_expansion(&mut terms, root, &InstanceHints::default()).expect("ok");
    assert_eq!(expansion.formula, terms.true_term());
    assert_eq!(expansion.instances, 0);
}

#[test]
fn ill_fitting_tuples_are_ignored() {
    let mut terms = TermStore::new();
    let (root, inner) = forall_exists_gt(&mut terms);
    let (zero, flag) = (rat(&mut terms, 0), terms.mk_bool(true));
    let mut hints = InstanceHints::default();
    hints.insert(inner, vec![vec![zero, zero], vec![flag], vec![]]);
    let expansion = negated_expansion(&mut terms, root, &hints).expect("ok");
    assert_eq!(
        expansion.instances, 0,
        "wrong arity or sort never instantiates"
    );
}

#[test]
fn chains_merge_and_shadowing_stops_them() {
    let mut terms = TermStore::new();
    let (x, y) = (real(&mut terms, "x"), real(&mut terms, "y"));
    let body = terms.mk_gt(y, x);
    let inner = terms.mk_forall(bound("y"), body);
    let chain = terms.mk_forall(bound("x"), inner);
    let (forall, binders, matrix) = binder_chain(&terms, chain).expect("quantifier");
    assert!(forall);
    assert_eq!(binders.len(), 2);
    assert_eq!(matrix, body);
    let again = terms.mk_forall(bound("y"), inner);
    let (_, binders, matrix) = binder_chain(&terms, again).expect("quantifier");
    assert_eq!(binders.len(), 1, "a repeated name ends the chain");
    assert_eq!(matrix, inner);
}

#[test]
fn iff_gives_every_occurrence_a_single_polarity() {
    let mut terms = TermStore::new();
    let (x, zero) = (real(&mut terms, "x"), rat(&mut terms, 0));
    let atom = terms.mk_gt(x, zero);
    let q = terms.mk_forall(bound("x"), atom);
    let p = terms.mk_var("p", Sort::Bool);
    let iff = terms.mk_app(ay_core::term::Symbol::named("="), vec![p, q], Sort::Bool);
    let mut hints = InstanceHints::default();
    let one = rat(&mut terms, 1);
    hints.insert(q, vec![vec![one]]);
    let expansion = negated_expansion(&mut terms, iff, &hints).expect("expands");
    assert!(!contains_quantifier(&terms, expansion.formula));
    assert_eq!(
        expansion.skolems.len(),
        1,
        "the negative occurrence is Skolemized"
    );
    assert_eq!(
        expansion.instances, 1,
        "the positive occurrence is expanded"
    );
}

#[test]
fn a_quantifier_under_a_non_connective_declines() {
    let mut terms = TermStore::new();
    let (root, _) = forall_exists_gt(&mut terms);
    let (one, two) = (rat(&mut terms, 1), rat(&mut terms, 2));
    let ite = terms.mk_ite_raw(root, one, two);
    let c = real(&mut terms, "c");
    let atom = terms.mk_gt(ite, c);
    assert_eq!(
        negated_expansion(&mut terms, atom, &InstanceHints::default()).err(),
        Some(ExpansionDecline::Shape)
    );
}

#[test]
fn the_instance_cap_declines() {
    let mut terms = TermStore::new();
    let (root, inner) = forall_exists_gt(&mut terms);
    let tuples: Vec<Vec<TermId>> = (0..=MAX_EXPANSION_INSTANCES as i64)
        .map(|n| vec![rat(&mut terms, n)])
        .collect();
    let mut hints = InstanceHints::default();
    hints.insert(inner, tuples);
    assert_eq!(
        negated_expansion(&mut terms, root, &hints).err(),
        Some(ExpansionDecline::Cap)
    );
}
