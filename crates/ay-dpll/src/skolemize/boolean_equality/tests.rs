// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit specs for the Boolean `=` arm of the NNF Skolemizer (#iff-split). The
//! verdict-level spec is
//! `crates/ay-dpll/tests/group_quantifiers/quantifier_under_boolean_equality.rs`.

use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};

use crate::skolemize::skolemize_deep;

/// Every `Exists` / `Forall` node reachable from `id` through Boolean
/// structure and quantifier bodies, as (is_exists, node) pairs.
fn quantifier_nodes(terms: &TermStore, id: TermId, out: &mut Vec<(bool, TermId)>) {
    match terms.get(id).clone() {
        TermData::Exists(_, body, _) => {
            out.push((true, id));
            quantifier_nodes(terms, body, out);
        }
        TermData::Forall(_, body, _) => {
            out.push((false, id));
            quantifier_nodes(terms, body, out);
        }
        TermData::App(_, args) => {
            for arg in args {
                quantifier_nodes(terms, arg, out);
            }
        }
        TermData::Not(inner) => quantifier_nodes(terms, inner, out),
        TermData::Ite(c, t, e) => {
            quantifier_nodes(terms, c, out);
            quantifier_nodes(terms, t, out);
            quantifier_nodes(terms, e, out);
        }
        _ => {}
    }
}

/// `true` when some subterm of `id` (through quantifier bodies too) satisfies
/// `pred`.
fn any_subterm(terms: &TermStore, id: TermId, pred: &dyn Fn(&TermStore, TermId) -> bool) -> bool {
    let mut stack = vec![id];
    while let Some(t) = stack.pop() {
        if pred(terms, t) {
            return true;
        }
        match terms.get(t).clone() {
            TermData::App(_, args) => stack.extend(args),
            TermData::Not(inner) => stack.push(inner),
            TermData::Ite(c, th, el) => stack.extend([c, th, el]),
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(b),
            _ => {}
        }
    }
    false
}

fn is_skolem_constant(terms: &TermStore, id: TermId) -> bool {
    matches!(terms.get(id), TermData::Var(name, _) if name.starts_with("sk!"))
}

fn is_skolem_function_app(terms: &TermStore, id: TermId) -> bool {
    matches!(terms.get(id), TermData::App(sym, _) if sym.name().starts_with("__ay_sk_"))
}

/// `(= b (exists x. P x))`, Verus's shape for an asserted quantified claim
/// (`tmp%k`), is split into its two implications: the positive copy of the
/// existential is Skolemized and the negative copy becomes a universal, so no
/// existential is left for E-matching to refuse.
#[test]
fn a_boolean_equality_splits_a_quantified_side() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let px = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], px);
    let iff = terms.mk_eq(b, exists);

    let rewritten = skolemize_deep(&mut terms, iff, true).expect("the equality must be rewritten");
    let TermData::App(sym, conjuncts) = terms.get(rewritten).clone() else {
        panic!("expected a conjunction of the two implications");
    };
    assert_eq!(sym.name(), "and");
    assert_eq!(conjuncts.len(), 2);
    let mut nodes = Vec::new();
    quantifier_nodes(&terms, rewritten, &mut nodes);
    assert!(
        nodes.iter().all(|&(is_exists, _)| !is_exists),
        "no existential may survive the split"
    );
    assert_eq!(
        nodes.len(),
        1,
        "the negative copy is the one universal left"
    );
    assert!(
        any_subterm(&terms, rewritten, &is_skolem_constant),
        "the positive copy must be Skolemized"
    );
}

/// Under negation the split is `(a ∧ ¬b) ∨ (¬a ∧ b)`: with `b` a universal,
/// its negative copy is Skolemized and its positive copy stays a universal.
#[test]
fn a_negated_boolean_equality_splits_a_quantified_side() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let px = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);
    let iff = terms.mk_eq(a, forall);
    let negated = terms.mk_not(iff);

    let rewritten =
        skolemize_deep(&mut terms, negated, true).expect("the equality must be rewritten");
    let TermData::App(sym, disjuncts) = terms.get(rewritten).clone() else {
        panic!("expected a disjunction");
    };
    assert_eq!(sym.name(), "or");
    assert_eq!(disjuncts.len(), 2);
    let mut nodes = Vec::new();
    quantifier_nodes(&terms, rewritten, &mut nodes);
    assert_eq!(
        nodes,
        vec![(false, forall)],
        "only the positive copy stays quantified"
    );
    assert!(any_subterm(&terms, rewritten, &is_skolem_constant));
}

/// Inside a universal, the negative copy of a nested universal is Skolemized
/// with a Skolem FUNCTION of the outer binder it mentions:
/// `∀s. (= c (∀i. P s i))`, whose `=` is not a definition of anything.
#[test]
fn a_boolean_equality_under_a_universal_uses_a_skolem_function() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let s = terms.mk_var("s", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let psi = terms.mk_app(Symbol::named("P"), vec![s, i], Sort::Bool);
    let inner = terms.mk_forall(vec![("i".to_string(), Sort::Int)], psi);
    let iff = terms.mk_eq(c, inner);
    let outer = terms.mk_forall(vec![("s".to_string(), Sort::Int)], iff);

    let rewritten = skolemize_deep(&mut terms, outer, true).expect("the body must be rewritten");
    let TermData::Forall(vars, body, _) = terms.get(rewritten).clone() else {
        panic!("the outer universal must stay a universal");
    };
    assert_eq!(vars[0].0, "s");
    assert!(
        any_subterm(&terms, body, &is_skolem_function_app),
        "the witness must depend on `s`"
    );
}

/// A universal whose whole body DEFINES a predicate, the
/// extensional-equality axiom shape `∀s. (= (eq s) (∀i. P s i))`, is left as
/// it was before the split (#iff-split-definition): its witness would be a
/// Skolem function of `s`, which no proof record binds.
#[test]
fn a_predicate_definition_under_a_universal_is_not_split() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let eq_s = terms.mk_app(Symbol::named("eq"), vec![s], Sort::Bool);
    let psi = terms.mk_app(Symbol::named("P"), vec![s, i], Sort::Bool);
    let inner = terms.mk_forall(vec![("i".to_string(), Sort::Int)], psi);
    let iff = terms.mk_eq(eq_s, inner);
    let outer = terms.mk_forall(vec![("s".to_string(), Sort::Int)], iff);
    assert!(skolemize_deep(&mut terms, outer, true).is_none());

    // The same with the sides swapped.
    let swapped = terms.mk_eq(inner, eq_s);
    let outer = terms.mk_forall(vec![("s".to_string(), Sort::Int)], swapped);
    assert!(skolemize_deep(&mut terms, outer, true).is_none());
}

/// Under [`super::scoped_definition_split`] (a solve that publishes without a
/// proof) the same definition is split like any other Boolean `=`, and the
/// guard restores the default when it drops.
#[test]
fn a_predicate_definition_is_split_when_no_proof_is_published() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let eq_s = terms.mk_app(Symbol::named("eq"), vec![s], Sort::Bool);
    let psi = terms.mk_app(Symbol::named("P"), vec![s, i], Sort::Bool);
    let inner = terms.mk_forall(vec![("i".to_string(), Sort::Int)], psi);
    let iff = terms.mk_eq(eq_s, inner);
    let outer = terms.mk_forall(vec![("s".to_string(), Sort::Int)], iff);
    {
        let _split = super::scoped_definition_split(true);
        let rewritten =
            skolemize_deep(&mut terms, outer, true).expect("the definition must be split");
        assert!(any_subterm(&terms, rewritten, &is_skolem_function_app));
    }
    assert!(
        skolemize_deep(&mut terms, outer, true).is_none(),
        "the default is restored when the guard drops"
    );
}

/// A head that misses a binder does not define the predicate at every
/// binding, so the equality is split as any other.
#[test]
fn a_head_missing_a_binder_is_not_a_definition() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Int);
    let t = terms.mk_var("t", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let eq_s = terms.mk_app(Symbol::named("eq"), vec![s], Sort::Bool);
    let psi = terms.mk_app(Symbol::named("P"), vec![s, t, i], Sort::Bool);
    let inner = terms.mk_forall(vec![("i".to_string(), Sort::Int)], psi);
    let iff = terms.mk_eq(eq_s, inner);
    let outer = terms.mk_forall(
        vec![("s".to_string(), Sort::Int), ("t".to_string(), Sort::Int)],
        iff,
    );
    let rewritten = skolemize_deep(&mut terms, outer, true).expect("the body must be rewritten");
    assert!(any_subterm(&terms, rewritten, &is_skolem_function_app));
}

/// A Boolean `=` with no quantifier on either side is a leaf, as before.
#[test]
fn a_ground_boolean_equality_is_untouched() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let iff = terms.mk_eq(a, b);
    assert!(skolemize_deep(&mut terms, iff, true).is_none());
}

/// A side that nests a quantifier, `(= b (∀y. ∃x. P x y))`, is not split
/// (#iff-split-alternation): its positive copy would need a Skolem function
/// of `y`. The equality stays a leaf, as before the split existed.
#[test]
fn a_side_with_a_quantifier_alternation_is_not_split() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let pxy = terms.mk_app(Symbol::named("P"), vec![x, y], Sort::Bool);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], pxy);
    let forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], exists);
    let iff = terms.mk_eq(b, forall);
    assert!(skolemize_deep(&mut terms, iff, true).is_none());

    // One level less and the equality is split again.
    let flat = terms.mk_eq(b, exists);
    assert!(skolemize_deep(&mut terms, flat, true).is_some());
}
