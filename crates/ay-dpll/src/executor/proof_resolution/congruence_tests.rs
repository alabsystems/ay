// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::ComplementIndex;
use super::{find_direct_resolution_assumption, try_derive_empty_via_congruence_bridging};
use ay_core::{Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

fn pred(terms: &mut TermStore, name: &str, arg: TermId) -> TermId {
    terms.mk_app(Symbol::named(name), [arg], Sort::Bool)
}

fn unit_lemma(literal: TermId) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "EUF".to_owned(),
        clause: vec![literal],
        farkas: None,
        kind: TheoryLemmaKind::Generic,
        lia: None,
    }
}

/// The index answers exactly what the first-match linear scan answers,
/// including for duplicated assumptions and literals with no complement.
#[test]
fn complement_index_agrees_with_the_linear_scan() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let px = pred(&mut terms, "p", x);
    let py = pred(&mut terms, "p", y);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let not_px = terms.mk_not(px);
    let not_py = terms.mk_not(py);
    let not_q = terms.mk_not(q);
    let not_r = terms.mk_not(r);
    let assumptions: Vec<(ProofId, TermId)> = [px, not_py, q, not_q, px, not_py]
        .into_iter()
        .enumerate()
        .map(|(index, term)| (ProofId(index as u32), term))
        .collect();
    let index = ComplementIndex::new(&terms, &assumptions);
    for lit in [px, not_px, py, not_py, q, not_q, r, not_r] {
        assert_eq!(
            index.complement_of(&terms, lit),
            find_direct_resolution_assumption(&terms, lit, &assumptions),
            "literal {lit:?}"
        );
    }
}

/// The pre-filter keeps every equality that can rewrite the literal:
/// `(not (p y))`, `(= x y)` and the unit lemma `(p x)` still close by
/// congruence.
#[test]
fn bridging_still_closes_through_an_equality_inside_the_literal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let px = pred(&mut terms, "p", x);
    let py = pred(&mut terms, "p", y);
    let not_py = terms.mk_not(py);
    let x_eq_y = terms.mk_eq(x, y);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(not_py));
    proof.add_step(ProofStep::Assume(x_eq_y));
    proof.add_step(unit_lemma(px));

    assert!(try_derive_empty_via_congruence_bridging(
        &mut terms, &mut proof
    ));
    assert!(
        matches!(proof.steps.last(), Some(ProofStep::Step { clause, .. }) if clause.is_empty()),
        "the bridged derivation must end in the empty clause: {:?}",
        proof.steps.last()
    );
}

/// An equality with neither side inside the literal is never tried.
///
/// The literal sits on a maximally shared DAG (`g_{k+1} = h(g_k, g_k)`): 50
/// distinct nodes, but a tree of 2^48 leaves. Without the substitution-site
/// pre-filter every (lemma, equality, orientation) triple re-walked that tree
/// through the unmemoized `substitute_in_term` before discovering the
/// rewrite was a no-op, so this search did not finish; with it, the search
/// visits each DAG node once per lemma and correctly finds no bridge. This is
/// the shape (many unit lemmas, many equalities absent from them) that cost
/// the `nested_query_false_unsat` corpus row 8-27 s per call.
#[test]
#[ntest::timeout(20_000)]
fn bridging_skips_equalities_absent_from_the_literal_on_shared_dags() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let mut shared = x;
    for _ in 0..48 {
        shared = terms.mk_app(Symbol::named("h"), [shared, shared], Sort::Int);
    }
    let literal = pred(&mut terms, "p", shared);
    let z = terms.mk_var("z", Sort::Int);
    let pz = pred(&mut terms, "p", z);
    let not_pz = terms.mk_not(pz);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(not_pz));
    for index in 0..16 {
        let a = terms.mk_var(format!("a{index}"), Sort::Int);
        let b = terms.mk_var(format!("b{index}"), Sort::Int);
        let equality = terms.mk_eq(a, b);
        proof.add_step(ProofStep::Assume(equality));
    }
    for _ in 0..8 {
        proof.add_step(unit_lemma(literal));
    }
    let before = proof.steps.len();

    assert!(!try_derive_empty_via_congruence_bridging(
        &mut terms, &mut proof
    ));
    assert_eq!(
        proof.steps.len(),
        before,
        "a failed search must not add steps"
    );
}
