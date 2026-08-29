// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authority for array-theory ORIGINAL clauses that reach the exact fragment
//! as a single packed `(or ..)` literal.
//!
//! The dead-last arm in `exact_fragment::intrinsic_authority` calls the
//! checker's own `ay_proof::recognize_array_theory_lemma`, so every kind it can
//! emit is one strict mode re-derives from the clause alone. These tests pin
//! both directions: the positives run all the way through `check_proof_strict`
//! (so the emitted kind must survive the metered validator), and the negatives
//! pin clauses that are NOT array tautologies — including Skolemized
//! extensionality, whose soundness is provenance rather than shape
//! (`ay-proof` `checker::array_axiom`, `recognize_array_select_store` doc) and
//! which must therefore stay unauthenticated on this path forever.

use super::*;
use ay_core::TheoryLemmaKind;

/// `(Array Int Int)` plus the index/value vocabulary the ROW schemas need.
struct ArrayFixture {
    terms: TermStore,
    array: TermId,
    index_i: TermId,
    index_j: TermId,
    value_v: TermId,
    value_w: TermId,
}

impl ArrayFixture {
    fn new(tag: &str) -> Self {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let array = terms.mk_var(format!("{tag}_a"), array_sort);
        let index_i = terms.mk_var(format!("{tag}_i"), Sort::Int);
        let index_j = terms.mk_var(format!("{tag}_j"), Sort::Int);
        let value_v = terms.mk_var(format!("{tag}_v"), Sort::Int);
        let value_w = terms.mk_var(format!("{tag}_w"), Sort::Int);
        Self {
            terms,
            array,
            index_i,
            index_j,
            value_v,
            value_w,
        }
    }
}

/// Model the measured shape: the whole array clause arrives as ONE packed
/// `(or ..)` literal bound to a single SAT variable. This is why the arm sits
/// outside the `clause.len() < 2` guard the direct-EUF arm needs.
fn fragment_for_packed_clause(
    terms: &mut TermStore,
    packed: TermId,
) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
    let var_to_term = HashMap::from_iter([(0u32, packed)]);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    SatProofManager::new(&var_to_term, terms).build_exact_original_proof_fragment(&trace, &[])
}

/// Refute the packed unit against its own negation so the fragment closes and
/// `check_proof_strict` has to decide the emitted theory lemma.
fn check_refutation_through_strict(
    terms: &mut TermStore,
    fragment: ExactOriginalProofFragment,
    proof_id: ProofId,
    packed: TermId,
) {
    let mut proof = fragment.proof;
    let not_packed = terms.mk_not_raw(packed);
    let assume_not_packed = proof.add_assume(not_packed, None);
    proof.add_resolution(Vec::new(), packed, proof_id, assume_not_packed);
    let quality = ay_proof::check_proof_strict(&proof, terms)
        .expect("the array lemma emitted by the intrinsic arm must pass strict checking");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn exact_fragment_checks_row2_read_over_write_clause_authority() {
    let mut fixture = ArrayFixture::new("row2_authority");
    let store = fixture
        .terms
        .mk_store(fixture.array, fixture.index_i, fixture.value_v);
    let read_store = fixture.terms.mk_select(store, fixture.index_j);
    let read_base = fixture.terms.mk_select(fixture.array, fixture.index_j);
    let row2 = fixture.terms.mk_eq(read_store, read_base);
    let guard = fixture.terms.mk_eq(fixture.index_i, fixture.index_j);
    let packed = fixture.terms.mk_or(vec![guard, row2]);

    assert_eq!(
        ay_proof::recognize_array_theory_lemma(&fixture.terms, &[packed]),
        Some(TheoryLemmaKind::ArraySelectStore { index_eq: false }),
        "the guarded ROW2 clause is the shape the dead-last arm claims"
    );

    let fragment = fragment_for_packed_clause(&mut fixture.terms, packed)
        .expect("a guarded ROW2 read-over-write clause has intrinsic array authority");
    let proof_id = fragment
        .bindings
        .get(&1)
        .expect("binding for original ID 1")
        .proof_id;
    assert!(matches!(
        fragment.proof.get_step(proof_id),
        Some(ProofStep::TheoryLemma {
            theory,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
            clause,
            ..
        }) if theory == "array" && clause == &vec![packed]
    ));

    check_refutation_through_strict(&mut fixture.terms, fragment, proof_id, packed);
}

#[test]
fn exact_fragment_checks_store_permutation_clause_authority() {
    let mut fixture = ArrayFixture::new("store_perm_authority");
    let store_i_then_j = {
        let inner = fixture
            .terms
            .mk_store(fixture.array, fixture.index_i, fixture.value_v);
        fixture
            .terms
            .mk_store(inner, fixture.index_j, fixture.value_w)
    };
    let store_j_then_i = {
        let inner = fixture
            .terms
            .mk_store(fixture.array, fixture.index_j, fixture.value_w);
        fixture
            .terms
            .mk_store(inner, fixture.index_i, fixture.value_v)
    };
    assert_ne!(
        store_i_then_j, store_j_then_i,
        "the two write orders must stay distinct terms for this to be a real schema"
    );
    let permutation = fixture.terms.mk_eq(store_i_then_j, store_j_then_i);
    let guard = fixture.terms.mk_eq(fixture.index_i, fixture.index_j);
    let packed = fixture.terms.mk_or(vec![guard, permutation]);

    assert_eq!(
        ay_proof::recognize_array_theory_lemma(&fixture.terms, &[packed]),
        Some(TheoryLemmaKind::ArrayStorePermutation),
        "guarded store commutativity is the metered kind the arm can also emit"
    );

    let fragment = fragment_for_packed_clause(&mut fixture.terms, packed)
        .expect("a guarded store-permutation clause has intrinsic array authority");
    let proof_id = fragment
        .bindings
        .get(&1)
        .expect("binding for original ID 1")
        .proof_id;
    assert!(matches!(
        fragment.proof.get_step(proof_id),
        Some(ProofStep::TheoryLemma {
            theory,
            kind: TheoryLemmaKind::ArrayStorePermutation,
            clause,
            ..
        }) if theory == "array" && clause == &vec![packed]
    ));

    check_refutation_through_strict(&mut fixture.terms, fragment, proof_id, packed);
}

#[test]
fn exact_fragment_rejects_unguarded_read_over_write_clause() {
    // `(= (select (store a i v) j) (select a j))` with the `(= i j)` guard
    // DROPPED. False whenever i == j, so it must never authenticate.
    let mut fixture = ArrayFixture::new("row2_unguarded");
    let store = fixture
        .terms
        .mk_store(fixture.array, fixture.index_i, fixture.value_v);
    let read_store = fixture.terms.mk_select(store, fixture.index_j);
    let read_base = fixture.terms.mk_select(fixture.array, fixture.index_j);
    let unguarded = fixture.terms.mk_eq(read_store, read_base);

    assert_eq!(
        ay_proof::recognize_array_theory_lemma(&fixture.terms, &[unguarded]),
        None
    );
    assert_eq!(
        fragment_for_packed_clause(&mut fixture.terms, unguarded)
            .expect_err("an unguarded read-over-write clause must remain unauthenticated"),
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![unguarded],
        }
    );
}

#[test]
fn exact_fragment_rejects_inverted_row1_guard_clause() {
    // `(or (= i j) (= (select (store a i v) j) v))` — ROW1 with the guard
    // polarity inverted. False whenever i != j.
    let mut fixture = ArrayFixture::new("row1_inverted");
    let store = fixture
        .terms
        .mk_store(fixture.array, fixture.index_i, fixture.value_v);
    let read_store = fixture.terms.mk_select(store, fixture.index_j);
    let row1 = fixture.terms.mk_eq(read_store, fixture.value_v);
    let inverted_guard = fixture.terms.mk_eq(fixture.index_i, fixture.index_j);
    let packed = fixture.terms.mk_or(vec![inverted_guard, row1]);

    assert_eq!(
        ay_proof::recognize_array_theory_lemma(&fixture.terms, &[packed]),
        None
    );
    assert_eq!(
        fragment_for_packed_clause(&mut fixture.terms, packed)
            .expect_err("an inverted ROW1 guard must remain unauthenticated"),
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![packed],
        }
    );
}

#[test]
fn exact_fragment_rejects_skolemized_extensionality_clause() {
    // `(or (= a1 a2) (not (= (select a1 k) (select a2 k))))` is NOT a
    // tautology: it is licensed by the provenance of the `array_ext_diff_intro`
    // witness `k`, never by shape. This arm has no proof to attach that
    // introduction to, so the clause must stay unauthenticated here. This test
    // exists to stop anyone widening the arm to swallow the measured
    // extensionality declines.
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array_a = terms.mk_var("ext_decline_a", array_sort.clone());
    let array_b = terms.mk_var("ext_decline_b", array_sort);
    let witness = terms.mk_var("ext_decline_k", Sort::Int);
    let arrays_equal = terms.mk_eq(array_a, array_b);
    let read_a = terms.mk_select(array_a, witness);
    let read_b = terms.mk_select(array_b, witness);
    let reads_equal = terms.mk_eq(read_a, read_b);
    let reads_differ = terms.mk_not_raw(reads_equal);
    let packed = terms.mk_or(vec![arrays_equal, reads_differ]);

    assert_eq!(
        ay_proof::recognize_array_theory_lemma(&terms, &[packed]),
        None,
        "shape alone must never license Skolemized extensionality"
    );
    assert_eq!(
        fragment_for_packed_clause(&mut terms, packed)
            .expect_err("Skolemized extensionality must remain unauthenticated on this path"),
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![packed],
        }
    );
}
