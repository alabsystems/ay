// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit specs for the quantifier proxy abstraction
//! (#quantifier-proxy-abstraction).
//!
//! These test the PASS, not the solver: the integration-level verdict spec is
//! `crates/ay-dpll/tests/group_quantifiers/quantifier_proxy_abstraction.rs`.
//! The load-bearing properties here are the ones the plan's soundness argument
//! rests on — target selection, the byte-identical no-op on entailed-only
//! assertions, the `Let` refusal, deterministic minting order, and the
//! reverse-substitution differential.

use super::*;
use ay_core::term::Symbol;

fn predicate(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn disjunction(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("or"), args, Sort::Bool)
}

fn is_bool_var(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(_, _)) && terms.sort(term) == &Sort::Bool
}

fn proxy_name(terms: &TermStore, term: TermId) -> String {
    match terms.get(term) {
        TermData::Var(name, _) => name.clone(),
        other => panic!("expected a proxy variable, got {other:?}"),
    }
}

/// A `forall` in a top-level CONJUNCTIVE position is entailed, the pre-existing
/// lane already instantiates it as a unit fact, and this pass must not touch
/// it: the assertion vector has to come out `TermId`-identical to the input so
/// the caller's `retain` deletes exactly what it deleted before.
#[test]
fn entailed_only_assertions_are_left_byte_identical() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let body = predicate(&mut terms, "p", vec![x]);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let ground = predicate(&mut terms, "g", vec![]);

    let mut assertions = vec![quantifier, ground];
    let before = assertions.clone();
    let entailed: DetHashSet<TermId> = [quantifier].into_iter().collect();

    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &entailed,
        &DetHashSet::default(),
    );

    assert_eq!(
        assertions, before,
        "an all-entailed assertion set must be left exactly as found"
    );
    assert!(!outcome.is_active(), "nothing was abstracted");
    assert!(outcome.proxies.is_empty(), "no proxy may be minted");
}

/// An entailed universal NESTED in ground structure is replaced by `true`, so
/// the assertion keeps its ground content instead of being deleted whole by
/// the caller's `retain` (#entailed-to-true). Purify mints no proxy for it and
/// the rewrite introduces no symbol.
#[test]
fn an_entailed_universal_inside_ground_structure_becomes_true() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let body = predicate(&mut terms, "p", vec![x]);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let ground = predicate(&mut terms, "g", vec![]);
    let fact = predicate(&mut terms, "e", vec![]);
    let not_fact = terms.mk_not(fact);
    let conjunction = terms.mk_app(Symbol::named("and"), vec![ground, quantifier], Sort::Bool);
    let clause = disjunction(&mut terms, vec![conjunction, not_fact]);

    let mut assertions = vec![clause, fact];
    let entailed: DetHashSet<TermId> = [quantifier].into_iter().collect();

    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &entailed,
        &DetHashSet::default(),
    );
    assert!(!outcome.is_active(), "nothing was abstracted");
    assert!(outcome.proxies.is_empty(), "no proxy may be minted");
    assert_eq!(
        assertions[0], clause,
        "purify leaves an all-entailed assertion"
    );

    let rewritten_count = keep_ground_content_of_entailed(
        &mut terms,
        &mut assertions,
        &entailed,
        &DetHashSet::default(),
    );
    assert_eq!(rewritten_count, 1);
    assert_eq!(assertions[1], fact, "a ground assertion is untouched");
    let rewritten = assertions[0];
    assert!(
        !crate::ematching::contains_quantifier(&terms, rewritten),
        "the entailed universal must be gone"
    );
    let truth = terms.mk_bool(true);
    let expected_conjunction = terms.mk_app(Symbol::named("and"), vec![ground, truth], Sort::Bool);
    let expected = disjunction(&mut terms, vec![expected_conjunction, not_fact]);
    assert_eq!(
        rewritten, expected,
        "the ground content must survive exactly, with the universal read as true"
    );
}

/// The shape the whole stage exists for: `(or (not g) (forall x. p x))`, whose
/// universal the assertion set does NOT entail. Baseline deleted the entire
/// clause, ground disjunct included. Here the clause survives with the
/// quantifier replaced by a fresh Boolean variable, and nothing else changes.
#[test]
fn disjunct_position_forall_becomes_a_fresh_bool_proxy() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let body = predicate(&mut terms, "p", vec![x]);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let ground = predicate(&mut terms, "g", vec![]);
    let not_ground = terms.mk_not_raw(ground);
    let clause = disjunction(&mut terms, vec![not_ground, quantifier]);

    let mut assertions = vec![clause, ground];
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &DetHashSet::default(),
        &DetHashSet::default(),
    );

    assert!(outcome.is_active(), "the clause must have been rewritten");
    assert_eq!(outcome.rewritten_assertions, 1);
    assert_eq!(outcome.refused_assertions, 0);
    assert_eq!(assertions[1], ground, "ground assertions are untouched");
    assert_ne!(assertions[0], clause, "the clause must have been rewritten");
    assert!(
        !crate::ematching::contains_quantifier(&terms, assertions[0]),
        "the rewritten clause must be quantifier-free so it survives the strip"
    );

    let proxy = *outcome
        .proxies
        .get(&quantifier)
        .expect("the quantifier must be mapped to a proxy");
    assert!(
        is_bool_var(&terms, proxy),
        "the proxy must be a plain Bool variable: `is_theory_atom` is false for \
         `Var`, which is what keeps the theory-atom selection sites untouched"
    );
    assert!(
        proxy_name(&terms, proxy).starts_with("qproxy_"),
        "the proxy name must carry the pass's prefix"
    );

    let TermData::App(symbol, args) = terms.get(assertions[0]).clone() else {
        panic!("the rewritten clause must still be an `or` application");
    };
    assert_eq!(symbol.name(), "or");
    assert_eq!(
        args,
        vec![not_ground, proxy],
        "only the quantifier disjunct may move; the GROUND disjunct is exactly \
         the content the baseline deletion threw away"
    );
}

/// The reverse-substitution differential the plan requires. It is a production
/// check, not only a `debug_assert`: applying `proxy -> quantifier` to the
/// rewritten assertion must reproduce the authored `TermId` exactly, otherwise
/// the abstraction map is not the identity it claims to be and every UNSAT
/// resting on it is unsupported.
#[test]
fn reverse_substitution_reproduces_the_authored_assertion() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let inner = predicate(&mut terms, "p", vec![x]);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], inner);
    let g1 = predicate(&mut terms, "g1", vec![]);
    let g2 = predicate(&mut terms, "g2", vec![]);
    // Deliberately awkward: a double negation and an `ite` on the path, so the
    // folding constructors would NOT reproduce the original term.
    let double_negated = {
        let once = terms.mk_not_raw(quantifier);
        terms.mk_not_raw(once)
    };
    let branch = terms.mk_ite_raw(g1, double_negated, g2);
    let clause = disjunction(&mut terms, vec![g2, branch]);

    let mut assertions = vec![clause];
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &DetHashSet::default(),
        &DetHashSet::default(),
    );
    assert!(outcome.is_active());

    let reverse: DetHashMap<TermId, TermId> = outcome
        .proxies
        .iter()
        .map(|(&quantifier, &proxy)| (proxy, quantifier))
        .collect();
    let mut cache = DetHashMap::default();
    let restored = substitute_top_down(&mut terms, assertions[0], &reverse, &mut cache);
    assert_eq!(
        restored,
        Some(clause),
        "reversing the abstraction must land back on the authored TermId"
    );
}

/// `Let` binds names this walk does not model, so the whole assertion is
/// refused and the caller's `retain` deletes it exactly as before.
#[test]
fn let_bearing_assertions_are_refused() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let inner = predicate(&mut terms, "p", vec![x]);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], inner);
    let ground = predicate(&mut terms, "g", vec![]);
    let clause = disjunction(&mut terms, vec![ground, quantifier]);
    let with_let = terms.mk_let(vec![("y".to_string(), ground)], clause);

    let mut assertions = vec![with_let];
    let before = assertions.clone();
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &DetHashSet::default(),
        &DetHashSet::default(),
    );

    assert_eq!(assertions, before, "a `Let`-bearing assertion is untouched");
    assert!(!outcome.is_active());
    assert_eq!(outcome.refused_assertions, 1);
}

/// Only the MAXIMAL quantifier subterms are proxied. A nested universal inside
/// another quantifier's body is never a map key, which is what makes the
/// top-down walk capture-safe: no substitution can reach a term mentioning a
/// bound variable.
#[test]
fn only_maximal_quantifier_subterms_are_proxied() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let inner_body = predicate(&mut terms, "r", vec![y, x]);
    let inner = terms.mk_forall(vec![("y".to_string(), Sort::Int)], inner_body);
    let guard = predicate(&mut terms, "p", vec![x]);
    let not_guard = terms.mk_not_raw(guard);
    let outer_body = disjunction(&mut terms, vec![not_guard, inner]);
    let outer = terms.mk_forall(vec![("x".to_string(), Sort::Int)], outer_body);
    let ground = predicate(&mut terms, "g", vec![]);
    let clause = disjunction(&mut terms, vec![ground, outer]);

    let mut assertions = vec![clause];
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &DetHashSet::default(),
        &DetHashSet::default(),
    );

    assert!(outcome.is_active());
    assert!(
        outcome.proxies.contains_key(&outer),
        "the maximal (outer) universal is the abstraction target"
    );
    assert!(
        !outcome.proxies.contains_key(&inner),
        "a universal under another binder must never be proxied: its body \
         mentions `x`, so hoisting it to a global Boolean symbol would not be \
         capture-safe"
    );
    assert_eq!(outcome.proxies.len(), 1);
}

/// Proxies are minted in `TermId` order so two runs of the same query allocate
/// identically — the determinism the campaign's differential measurements need.
#[test]
fn proxies_are_minted_in_deterministic_term_id_order() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let first_body = predicate(&mut terms, "p", vec![x]);
    let first = terms.mk_forall(vec![("x".to_string(), Sort::Int)], first_body);
    let second_body = predicate(&mut terms, "q", vec![x]);
    let second = terms.mk_forall(vec![("x".to_string(), Sort::Int)], second_body);
    let ground = predicate(&mut terms, "g", vec![]);
    // Present the LATER quantifier first, so insertion order and TermId order
    // disagree and only the sort keeps the allocation stable.
    let clause = disjunction(&mut terms, vec![ground, second, first]);

    let mut assertions = vec![clause];
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &DetHashSet::default(),
        &DetHashSet::default(),
    );

    assert_eq!(outcome.proxies.len(), 2);
    let first_proxy = outcome.proxies[&first];
    let second_proxy = outcome.proxies[&second];
    assert!(
        first.index() < second.index(),
        "fixture precondition: the quantifiers were interned in this order"
    );
    assert!(
        first_proxy.index() < second_proxy.index(),
        "the proxy for the lower-numbered quantifier must be minted first"
    );
}

/// A CEGQI counterexample lemma is keyed BY `TermId` in `cegqi_ce_lemma_ids`
/// and stripped by identity in `disambiguate_cegqi_unsat`. Rewriting one would
/// orphan the key and drop a genuine constraint from the ground re-solve — the
/// `#forall-bare-bool` wrong-SAT shape. Protected assertions keep the baseline
/// deletion instead.
#[test]
fn protected_ce_lemma_assertions_are_not_rewritten() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let body = predicate(&mut terms, "p", vec![x]);
    let quantifier = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let ground = predicate(&mut terms, "g", vec![]);
    let clause = disjunction(&mut terms, vec![ground, quantifier]);

    let mut assertions = vec![clause];
    let before = assertions.clone();
    let protected: DetHashSet<TermId> = [clause].into_iter().collect();
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &DetHashSet::default(),
        &protected,
    );

    assert_eq!(assertions, before, "a protected assertion is untouched");
    assert!(!outcome.is_active());
    assert!(outcome.proxies.is_empty());
}

/// An assertion carrying BOTH an entailed and a non-entailed universal is
/// abstracted in full. Proxying the entailed one too costs nothing — its sound
/// instances were already unit-pushed upstream and the assertion itself was
/// being deleted — and it is what leaves the rewritten assertion
/// quantifier-free, so it survives the strip.
#[test]
fn a_mixed_assertion_proxies_every_maximal_quantifier() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let entailed_body = predicate(&mut terms, "p", vec![x]);
    let entailed = terms.mk_forall(vec![("x".to_string(), Sort::Int)], entailed_body);
    let loose_body = predicate(&mut terms, "q", vec![x]);
    let loose = terms.mk_forall(vec![("x".to_string(), Sort::Int)], loose_body);
    let clause = disjunction(&mut terms, vec![entailed, loose]);

    let mut assertions = vec![clause];
    let entailed_set: DetHashSet<TermId> = [entailed].into_iter().collect();
    let outcome = purify_quantifier_atoms(
        &mut terms,
        &mut assertions,
        &entailed_set,
        &DetHashSet::default(),
    );

    assert!(outcome.is_active());
    assert_eq!(outcome.proxies.len(), 2);
    assert!(
        !crate::ematching::contains_quantifier(&terms, assertions[0]),
        "a partially-abstracted assertion would still be deleted by the strip, \
         which would lose the ground content this stage exists to keep"
    );
}
