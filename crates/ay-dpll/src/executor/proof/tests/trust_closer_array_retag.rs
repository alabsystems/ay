// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trust-closer resolution and array-retag regressions.

use ay_core::{AletheRule, Proof, ProofStep, Symbol, TermStore, TheoryLemmaKind};
use ay_proof::check_proof_partial;

type Sort = ay_core::Sort;

/// #trust-lemma-dup-assume — the same term asserted twice must not produce a
/// no-op `th_resolution`.
///
/// `derive_empty_via_trust_lemma` collects one entry per `Assume`/unit-`Trust`
/// step, so a repeated term used to contribute the SAME negated literal to the
/// trust lemma more than once. The chain then removed all copies on the first
/// resolution, and every later step against that term resolved nothing: its
/// conclusion equalled premise 0's clause and premise 1 was unused. The strict
/// checker rejects that as `invalid th_resolution derivation` — 6178 such steps
/// were emitted across one `ay-chc --lib` run.
#[test]
fn trust_lemma_chain_is_valid_when_an_assumption_is_repeated() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    // `a` twice — the duplicate is what used to break the chain.
    proof.add_assume(a, Some("h0".to_string()));
    proof.add_assume(a, Some("h1".to_string()));
    proof.add_assume(not_b, Some("h2".to_string()));

    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    let (_summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "repeated assumption must still yield a checker-valid chain, got {error:?}"
    );
    assert!(
        matches!(proof.steps.last(), Some(ProofStep::Step { clause, .. }) if clause.is_empty()),
        "trust-lemma fallback must still close on the empty clause"
    );
    // One resolution per DISTINCT assumption term, not per collected entry.
    let resolutions = proof
        .steps
        .iter()
        .filter(|s| {
            matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    ..
                }
            )
        })
        .count();
    assert_eq!(
        resolutions, 2,
        "expected one th_resolution per distinct assumption term"
    );
}

/// #trust-closer-retag — build the `storecomm` closer shape.
///
/// Assumptions `¬(i0 = i1)` and `¬(L = R)` over two permuted store chains, so
/// the closer's head clause is `(cl (= i0 i1) (= L R))` — exactly the
/// `ArrayStorePermutation` schema. `read_through` swaps the array-equality
/// assumption for a read of both chains at one shared index, the shape the
/// `storecomm_sf` benchmarks produce.
fn store_permutation_closer_proof(read_through: bool) -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort.clone());
    let i0 = terms.mk_var("i0", Sort::Int);
    let i1 = terms.mk_var("i1", Sort::Int);
    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let store = |terms: &mut TermStore, base, index, value| {
        terms.mk_app(
            Symbol::named("store"),
            vec![base, index, value],
            array_sort.clone(),
        )
    };
    let left_inner = store(&mut terms, a, i0, v0);
    let left = store(&mut terms, left_inner, i1, v1);
    let right_inner = store(&mut terms, a, i1, v1);
    let right = store(&mut terms, right_inner, i0, v0);
    let (left_side, right_side) = if read_through {
        let k = terms.mk_var("k", Sort::Int);
        (
            terms.mk_app(Symbol::named("select"), vec![left, k], Sort::Int),
            terms.mk_app(Symbol::named("select"), vec![right, k], Sort::Int),
        )
    } else {
        (left, right)
    };

    let index_eq = terms.mk_app(Symbol::named("="), vec![i0, i1], ay_core::Sort::Bool);
    let conclusion = terms.mk_app(
        Symbol::named("="),
        vec![left_side, right_side],
        ay_core::Sort::Bool,
    );
    let not_index_eq = terms.mk_not_raw(index_eq);
    let not_conclusion = terms.mk_not_raw(conclusion);

    let mut proof = Proof::new();
    proof.add_assume(not_index_eq, Some("h0".to_string()));
    proof.add_assume(not_conclusion, Some("h1".to_string()));
    (terms, proof)
}

fn closer_head_kind(proof: &Proof) -> Option<TheoryLemmaKind> {
    proof.steps.iter().find_map(|step| match step {
        ProofStep::TheoryLemma { kind, .. } => Some(*kind),
        _ => None,
    })
}

/// The closer's head clause is the NEGATION of the leaves it resolves against.
/// When that clause is a standalone array theorem the strict checker already
/// validates, conceding `Generic` threw away a deliverable proof. The retag
/// must go through the checker's own recognizer, so the kind it assigns is by
/// construction the kind strict mode accepts.
#[test]
fn trust_closer_retags_a_store_permutation_head_and_strict_check_passes() {
    let (mut terms, mut proof) = store_permutation_closer_proof(false);
    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    assert_eq!(
        closer_head_kind(&proof),
        Some(TheoryLemmaKind::ArrayStorePermutation),
        "the closer must retag a store-permutation head through the recognizer"
    );
    ay_proof::check_proof_strict(&proof, &terms)
        .expect("the retagged closer must pass the STRICT checker, not merely the partial one");
}

/// The `storecomm_sf` shape: the conclusion reads both permuted chains at one
/// shared index instead of equating the arrays.
#[test]
fn trust_closer_retags_a_read_through_store_permutation_head() {
    let (mut terms, mut proof) = store_permutation_closer_proof(true);
    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    assert_eq!(
        closer_head_kind(&proof),
        Some(TheoryLemmaKind::ArrayStorePermutation),
        "the read-through storecomm_sf head must retag too"
    );
    ay_proof::check_proof_strict(&proof, &terms)
        .expect("the retagged read-through closer must pass the STRICT checker");
}

/// FAIL-CLOSED. A head no array schema covers must keep the honest `Generic`
/// trust stub: the retag only stops discarding provable heads, it never
/// invents a justification. Dropping the index-pair assumption leaves
/// `(cl (= L R))`, which is FALSE when `i0 = i1` and `v0 != v1`.
#[test]
fn trust_closer_keeps_generic_when_no_array_schema_covers_the_head() {
    let (mut terms, _) = store_permutation_closer_proof(false);
    // Rebuild with only the array-equality leaf, so condition (5) of the
    // store-permutation schema cannot be met.
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort.clone());
    let i0 = terms.mk_var("i0", Sort::Int);
    let i1 = terms.mk_var("i1", Sort::Int);
    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let store = |terms: &mut TermStore, base, index, value| {
        terms.mk_app(
            Symbol::named("store"),
            vec![base, index, value],
            array_sort.clone(),
        )
    };
    let left_inner = store(&mut terms, a, i0, v0);
    let left = store(&mut terms, left_inner, i1, v1);
    let right_inner = store(&mut terms, a, i1, v1);
    let right = store(&mut terms, right_inner, i0, v0);
    let conclusion = terms.mk_app(Symbol::named("="), vec![left, right], ay_core::Sort::Bool);
    let not_conclusion = terms.mk_not_raw(conclusion);

    let mut proof = Proof::new();
    proof.add_assume(not_conclusion, Some("h0".to_string()));
    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    assert_eq!(
        closer_head_kind(&proof),
        Some(TheoryLemmaKind::Generic),
        "a head with no index-pair literal must stay an honest trust stub"
    );
    assert!(
        ay_proof::check_proof_strict(&proof, &terms).is_err(),
        "an unjustified head must still be REFUSED by the strict checker"
    );
}

/// FAIL-CLOSED, non-array: a purely Boolean closer head is untouched.
#[test]
fn trust_closer_keeps_generic_for_a_non_array_head() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_b = terms.mk_not(b);
    let mut proof = Proof::new();
    proof.add_assume(a, Some("h0".to_string()));
    proof.add_assume(not_b, Some("h1".to_string()));

    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    assert_eq!(
        closer_head_kind(&proof),
        Some(TheoryLemmaKind::Generic),
        "a non-array closer head must be left exactly as it was"
    );
}
