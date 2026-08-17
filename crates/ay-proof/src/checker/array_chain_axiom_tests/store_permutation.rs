// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// ArrayStorePermutation
// ============================================================================

#[test]
fn store_permutation_accepts_full_permutation_with_all_index_disequalities() {
    // (cl (= i0 i1) (= i0 i2) (= i1 i2)
    //     (= (store (store (store a i0 v0) i1 v1) i2 v2)
    //        (store (store (store a i2 v2) i0 v0) i1 v1)))
    let mut f = Fixture::new(3);
    let a = f.a;
    let left = f.chain(a, &[0, 1, 2]);
    let right = f.chain(a, &[2, 0, 1]);
    let conclusion = eq(&mut f.terms, left, right);
    let mut clause = f.all_index_eqs(3);
    clause.push(conclusion);

    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect("a full store permutation with every index disequality must certify");
}

#[test]
fn store_permutation_rejects_missing_index_disequality() {
    // NEGATIVE: identical to the accepted instance except the `(= i0 i2)`
    // literal is dropped. Without it the clause is FALSIFIABLE (take
    // i0 = i2 with v0 != v2: the two chains disagree at that index), so the
    // checker must reject.
    let mut f = Fixture::new(3);
    let a = f.a;
    let left = f.chain(a, &[0, 1, 2]);
    let right = f.chain(a, &[2, 0, 1]);
    let conclusion = eq(&mut f.terms, left, right);
    let i0 = f.idx[0];
    let i2 = f.idx[2];
    let dropped = eq(&mut f.terms, i0, i2);
    let mut clause: Vec<TermId> = f
        .all_index_eqs(3)
        .into_iter()
        .filter(|&lit| lit != dropped)
        .collect();
    assert_eq!(clause.len(), 2, "exactly one pair literal must be dropped");
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("a missing index-disequality literal must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_chains_that_are_not_a_permutation() {
    // NEGATIVE: the right chain writes `v0` at `i1` and `v1` at `i0` — the
    // (index, value) multisets differ, so the arrays are NOT equal even with
    // every index pairwise distinct.
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let (i0, i1, v0, v1) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let inner = store(&mut f.terms, a, i1, v0);
    let right = store(&mut f.terms, inner, i0, v1);
    let conclusion = eq(&mut f.terms, left, right);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("chains that are not a permutation of the same pairs must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_repeated_index_term() {
    // NEGATIVE: `store(store(a,i0,v0),i0,v1)` vs `store(store(a,i0,v1),i0,v0)`.
    // The (index, value) multisets are EQUAL and there is no pair of DISTINCT
    // index terms to disequate, yet the arrays differ (v1 vs v0 at i0). The
    // pairwise-distinct-index-terms condition is what closes this hole.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let i0 = terms.mk_var("i0", Sort::Int);
    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let left_inner = store(&mut terms, a, i0, v0);
    let left = store(&mut terms, left_inner, i0, v1);
    let right_inner = store(&mut terms, a, i0, v1);
    let right = store(&mut terms, right_inner, i0, v0);
    let conclusion = eq(&mut terms, left, right);

    let err = validate_strict(
        &terms,
        vec![conclusion],
        TheoryLemmaKind::ArrayStorePermutation,
    )
    .expect_err("a repeated index term must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_different_base_arrays() {
    // NEGATIVE: same written pairs, DIFFERENT base arrays. The chains agree on
    // the written indices but nowhere else.
    let mut f = Fixture::new(2);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(b, &[1, 0]);
    let conclusion = eq(&mut f.terms, left, right);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("store chains over different base arrays must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_negated_conclusion() {
    // NEGATIVE: the store equality appears NEGATED. `(not (= L R))` together
    // with the index equalities is satisfiable, not a tautology.
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(a, &[1, 0]);
    let conclusion = eq(&mut f.terms, left, right);
    let negated = f.terms.mk_not(conclusion);
    let mut clause = f.all_index_eqs(2);
    clause.push(negated);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("a negated store-permutation conclusion must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_recognizer_agrees_with_validator() {
    // The classifier must only ever assign a kind the validator accepts.
    let mut f = Fixture::new(3);
    let a = f.a;
    let left = f.chain(a, &[0, 1, 2]);
    let right = f.chain(a, &[2, 1, 0]);
    let conclusion = eq(&mut f.terms, left, right);
    let mut clause = f.all_index_eqs(3);
    clause.push(conclusion);

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayStorePermutation)
    );
    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect("recognized clause must validate");
}

#[test]
fn store_permutation_recognizer_declines_unsound_instance() {
    // The recognizer must NOT label the missing-disequality clause, or the
    // classifier would emit a rule strict mode rejects.
    let mut f = Fixture::new(3);
    let a = f.a;
    let left = f.chain(a, &[0, 1, 2]);
    let right = f.chain(a, &[2, 0, 1]);
    let conclusion = eq(&mut f.terms, left, right);
    let i0 = f.idx[0];
    let i2 = f.idx[2];
    let dropped = eq(&mut f.terms, i0, i2);
    let mut clause: Vec<TermId> = f
        .all_index_eqs(3)
        .into_iter()
        .filter(|&lit| lit != dropped)
        .collect();
    clause.push(conclusion);

    assert_eq!(recognize_array_theory_lemma(&f.terms, &clause), None);
}
