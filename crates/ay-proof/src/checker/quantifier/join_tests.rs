// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId, TermStore};

use super::*;

struct JoinFixture {
    terms: TermStore,
    /// `(exists ((jx Int)) (exists ((jy Int) (jz Int)) φ))`
    nested: TermId,
    /// `(exists ((jx Int) (jy Int) (jz Int)) φ)`
    joined: TermId,
    body: TermId,
}

fn binders(names: &[&str]) -> Vec<(String, Sort)> {
    names
        .iter()
        .map(|n| ((*n).to_string(), Sort::Int))
        .collect()
}

fn fixture() -> JoinFixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("jx", Sort::Int);
    let y = terms.mk_var("jy", Sort::Int);
    let z = terms.mk_var("jz", Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [x, y, z], Sort::Int);
    let one = terms.mk_int(1.into());
    let body = terms.mk_app(Symbol::named("="), [sum, one], Sort::Bool);
    let inner = terms.mk_exists(binders(&["jy", "jz"]), body);
    let nested = terms.mk_exists(binders(&["jx"]), inner);
    let joined = terms.mk_exists(binders(&["jx", "jy", "jz"]), body);
    JoinFixture {
        terms,
        nested,
        joined,
        body,
    }
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn check(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_qnt_join(terms, ProofId(0), clause, 0, &[]).is_ok()
}

#[test]
fn qnt_join_accepts_the_curried_existential_and_universal() {
    let mut f = fixture();
    let equality = eq(&mut f.terms, f.nested, f.joined);
    assert!(check(&f.terms, &[equality]));

    let inner = f.terms.mk_forall(binders(&["jy", "jz"]), f.body);
    let nested = f.terms.mk_forall(binders(&["jx"]), inner);
    let joined = f.terms.mk_forall(binders(&["jx", "jy", "jz"]), f.body);
    let equality = eq(&mut f.terms, nested, joined);
    assert!(check(&f.terms, &[equality]));
}

#[test]
fn qnt_join_rejects_premises_args_and_extra_literals() {
    let mut f = fixture();
    let equality = eq(&mut f.terms, f.nested, f.joined);
    assert!(validate_qnt_join(&f.terms, ProofId(0), &[equality], 1, &[]).is_err());
    assert!(validate_qnt_join(&f.terms, ProofId(0), &[equality], 0, &[f.body]).is_err());
    assert!(!check(&f.terms, &[equality, equality]));
    assert!(!check(&f.terms, &[]));
}

/// The orientation is fixed: nested on the left, joined on the right.
#[test]
fn qnt_join_rejects_the_reversed_equality() {
    let mut f = fixture();
    let equality = eq(&mut f.terms, f.joined, f.nested);
    assert!(!check(&f.terms, &[equality]));
}

#[test]
fn qnt_join_rejects_mixed_quantifier_kinds() {
    let mut f = fixture();
    let inner = f.terms.mk_forall(binders(&["jy", "jz"]), f.body);
    let nested = f.terms.mk_exists(binders(&["jx"]), inner);
    let equality = eq(&mut f.terms, nested, f.joined);
    assert!(!check(&f.terms, &[equality]), "exists-forall is not a join");

    let forall_joined = f.terms.mk_forall(binders(&["jx", "jy", "jz"]), f.body);
    let equality = eq(&mut f.terms, f.nested, forall_joined);
    assert!(
        !check(&f.terms, &[equality]),
        "the joined side must keep the kind"
    );
}

#[test]
fn qnt_join_rejects_a_binder_list_that_is_not_the_concatenation() {
    let mut f = fixture();
    for names in [
        &["jy", "jx", "jz"][..],
        &["jx", "jy"][..],
        &["jx", "jy", "jz", "jw"][..],
        &["jx", "jz", "jy"][..],
    ] {
        let joined = f.terms.mk_exists(binders(names), f.body);
        let equality = eq(&mut f.terms, f.nested, joined);
        assert!(!check(&f.terms, &[equality]), "{names:?}");
    }
    // Same names, one binder re-sorted.
    let mut resorted = binders(&["jx", "jy", "jz"]);
    resorted[1].1 = Sort::Real;
    let joined = f.terms.mk_exists(resorted, f.body);
    let equality = eq(&mut f.terms, f.nested, joined);
    assert!(
        !check(&f.terms, &[equality]),
        "a re-sorted binder is not a join"
    );
}

/// `∃x.∃x.φ` binds one `x` (the inner one shadows), `∃x x.φ` is malformed:
/// a repeated name must be refused even when the lists concatenate.
#[test]
fn qnt_join_rejects_a_repeated_binder_name() {
    let mut f = fixture();
    let inner = f.terms.mk_exists(binders(&["jx"]), f.body);
    let nested = f.terms.mk_exists(binders(&["jx"]), inner);
    let joined = f.terms.mk_exists(binders(&["jx", "jx"]), f.body);
    let equality = eq(&mut f.terms, nested, joined);
    assert!(!check(&f.terms, &[equality]));
}

#[test]
fn qnt_join_rejects_different_bodies_and_empty_lists() {
    let mut f = fixture();
    let other = f.terms.true_term();
    let joined = f.terms.mk_exists(binders(&["jx", "jy", "jz"]), other);
    let equality = eq(&mut f.terms, f.nested, joined);
    assert!(
        !check(&f.terms, &[equality]),
        "the bodies must be identical"
    );

    let inner = f.terms.mk_exists(Vec::new(), f.body);
    let nested = f.terms.mk_exists(binders(&["jx", "jy", "jz"]), inner);
    let joined = f.terms.mk_exists(binders(&["jx", "jy", "jz"]), f.body);
    let equality = eq(&mut f.terms, nested, joined);
    assert!(
        !check(&f.terms, &[equality]),
        "an empty inner list is no join"
    );

    // Not quantifiers at all.
    let equality = eq(&mut f.terms, f.body, f.body);
    assert!(!check(&f.terms, &[equality]));
}
