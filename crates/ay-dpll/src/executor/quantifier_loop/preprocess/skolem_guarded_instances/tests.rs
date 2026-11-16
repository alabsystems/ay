// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit coverage for the Skolem-witness guarded instantiation pass.

use super::*;

/// Mint a registered Skolem constant of `sort`, the way `skolemize` does.
fn skolem(terms: &mut TermStore, name: &str, sort: Sort) -> TermId {
    let term = terms.mk_fresh_var(name, sort);
    if let TermData::Var(fresh, _) = terms.get(term) {
        let fresh = fresh.clone();
        terms.mark_skolem_symbol(&fresh);
    }
    term
}

fn int_const(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_app(Symbol::Named(name.into()), vec![], Sort::Int)
}

use ay_core::term::Symbol;

/// A proxied EXISTENTIAL contributes `(or (not phi[sk]) q)`.
#[test]
fn existential_proxy_guards_the_instance_at_the_skolem_constant() {
    let mut terms = TermStore::new();
    let sk = skolem(&mut terms, "sk!w", Sort::Int);
    let k = int_const(&mut terms, "k");
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_le(x, k);
    let quantifier = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    // The Skolem constant must be reachable from the assertion vector.
    let seed = terms.mk_le(sk, k);
    let mut assertions = vec![seed, proxy];

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(quantifier, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome.asserted, 1, "one Skolem constant, one binder");
    let clause = *assertions.last().expect("clause appended");
    let instance = terms.mk_le(sk, k);
    let negated = terms.mk_not(instance);
    let expected = terms.mk_or(vec![negated, proxy]);
    assert_eq!(clause, expected, "(or (not phi[sk]) q)");
}

/// A proxied UNIVERSAL contributes the dual `(or (not q) phi[sk])`.
#[test]
fn universal_proxy_guards_the_instance_on_the_proxy_literal() {
    let mut terms = TermStore::new();
    let sk = skolem(&mut terms, "sk!w", Sort::Int);
    let k = int_const(&mut terms, "k");
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_le(x, k);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    let seed = terms.mk_le(sk, k);
    let mut assertions = vec![seed, proxy];

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(quantifier, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome.asserted, 1);
    let clause = *assertions.last().expect("clause appended");
    let instance = terms.mk_le(sk, k);
    let guard = terms.mk_not(proxy);
    let expected = terms.mk_or(vec![guard, instance]);
    assert_eq!(clause, expected, "(or (not q) phi[sk])");
}

/// With no Skolem constant of the binder sort there is no ground witness, so
/// the pass adds nothing and the assertion vector is untouched.
#[test]
fn no_skolem_constant_of_the_binder_sort_refuses() {
    let mut terms = TermStore::new();
    // A Skolem constant of a DIFFERENT sort must not be offered for an Int.
    let sk_bool = skolem(&mut terms, "sk!b", Sort::Bool);
    let k = int_const(&mut terms, "k");
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_le(x, k);
    let quantifier = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    let mut assertions = vec![sk_bool, proxy];
    let before = assertions.clone();

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(quantifier, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome, GuardedInstanceOutcome::default());
    assert_eq!(assertions, before, "assertion vector untouched on refusal");
}

/// A nested binder in the body is refused: the substitution's capture argument
/// only holds for a binder-free body, and the clause would carry a quantifier
/// into a vector that is about to drop every quantified assertion.
#[test]
fn nested_binder_in_the_body_refuses() {
    let mut terms = TermStore::new();
    let sk = skolem(&mut terms, "sk!w", Sort::Int);
    let k = int_const(&mut terms, "k");
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let inner_body = terms.mk_le(y, x);
    let inner = terms.mk_forall(vec![("y".to_string(), Sort::Int)], inner_body);
    let outer = terms.mk_exists(vec![("x".to_string(), Sort::Int)], inner);
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    let seed = terms.mk_le(sk, k);
    let mut assertions = vec![seed, proxy];
    let before = assertions.clone();

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(outer, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome, GuardedInstanceOutcome::default());
    assert_eq!(assertions, before);
}

/// The per-quantifier tuple budget is the cross product, so a binder count
/// beyond `MAX_BINDERS` is refused outright rather than enumerated.
#[test]
fn binder_count_beyond_the_cap_refuses() {
    let mut terms = TermStore::new();
    let sk = skolem(&mut terms, "sk!w", Sort::Int);
    let k = int_const(&mut terms, "k");
    let mut sum = k;
    let mut vars = Vec::new();
    for index in 0..=MAX_BINDERS {
        let name = format!("x{index}");
        let var = terms.mk_var(&name, Sort::Int);
        sum = terms.mk_add(vec![sum, var]);
        vars.push((name, Sort::Int));
    }
    let body = terms.mk_le(sum, k);
    let quantifier = terms.mk_exists(vars, body);
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    let seed = terms.mk_le(sk, k);
    let mut assertions = vec![seed, proxy];
    let before = assertions.clone();

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(quantifier, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome, GuardedInstanceOutcome::default());
    assert_eq!(assertions, before);
}

/// An empty proxy map is the OFF position of the kill switch's caller: nothing
/// is scanned and nothing is added.
#[test]
fn no_proxies_is_a_no_op() {
    let mut terms = TermStore::new();
    let k = int_const(&mut terms, "k");
    let mut assertions = vec![k];
    let before = assertions.clone();
    let outcome =
        assert_skolem_guarded_instances(&mut terms, &mut assertions, &DetHashMap::default());
    assert_eq!(outcome, GuardedInstanceOutcome::default());
    assert_eq!(assertions, before);
}

/// Two Skolem constants at one binder produce two distinct guarded clauses.
#[test]
fn one_binder_enumerates_every_skolem_candidate() {
    let mut terms = TermStore::new();
    let sk_a = skolem(&mut terms, "sk!a", Sort::Int);
    let sk_b = skolem(&mut terms, "sk!b", Sort::Int);
    let k = int_const(&mut terms, "k");
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_le(x, k);
    let quantifier = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    let seed_a = terms.mk_le(sk_a, k);
    let seed_b = terms.mk_le(sk_b, k);
    let mut assertions = vec![seed_a, seed_b, proxy];

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(quantifier, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome.created, 2);
    assert_eq!(outcome.asserted, 2);
}

/// Two binders over two candidates walk the full 2x2 cross product, and a body
/// that mentions only one binder collapses all four tuples to one clause.
#[test]
fn two_binders_enumerate_the_cross_product_and_deduplicate() {
    let mut terms = TermStore::new();
    let sk_a = skolem(&mut terms, "sk!a", Sort::Int);
    let sk_b = skolem(&mut terms, "sk!b", Sort::Int);
    let k = int_const(&mut terms, "k");
    // The body mentions `x` only, so the four (x, y) tuples yield two distinct
    // instances and — because `y` is not free in the body — exactly two
    // distinct clauses.
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_le(x, k);
    let quantifier = terms.mk_exists(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );
    let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
    let seed_a = terms.mk_le(sk_a, k);
    let seed_b = terms.mk_le(sk_b, k);
    let mut assertions = vec![seed_a, seed_b, proxy];

    let mut proxies: DetHashMap<TermId, TermId> = DetHashMap::default();
    proxies.insert(quantifier, proxy);
    let outcome = assert_skolem_guarded_instances(&mut terms, &mut assertions, &proxies);

    assert_eq!(outcome.created, 4, "2 candidates ^ 2 binders");
    assert_eq!(outcome.asserted, 2, "y is not free in the body");
}
