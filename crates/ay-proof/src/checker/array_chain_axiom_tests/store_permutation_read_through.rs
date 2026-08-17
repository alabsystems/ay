// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Store-permutation read-through regressions.

use super::*;

#[test]
fn store_permutation_rejects_ill_sorted_store_application() {
    // NEGATIVE: `TermStore` permits raw applications, so a forger can build a
    // `store` whose index argument has the wrong sort. The signature check must
    // refuse to treat it as an array operation.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let i0 = terms.mk_var("i0", Sort::Int);
    let bogus = terms.mk_var("bogus", Sort::Bool);
    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let sort = terms.sort(a).clone();
    // `store(a, bogus, v0)` — index sort Bool, not Int.
    let left_inner = terms.mk_app(Symbol::named("store"), vec![a, bogus, v0], sort.clone());
    let left = terms.mk_app(
        Symbol::named("store"),
        vec![left_inner, i0, v1],
        sort.clone(),
    );
    let right_inner = terms.mk_app(Symbol::named("store"), vec![a, i0, v1], sort.clone());
    let right = terms.mk_app(Symbol::named("store"), vec![right_inner, bogus, v0], sort);
    let conclusion = eq(&mut terms, left, right);
    let pair = eq(&mut terms, i0, bogus);

    let err = validate_strict(
        &terms,
        vec![pair, conclusion],
        TheoryLemmaKind::ArrayStorePermutation,
    )
    .expect_err("an ill-sorted store application must not be read as an array op");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// ArrayStorePermutation — READ-THROUGH conclusion
//
// `(= (select L k) (select R k))` in place of `(= L R)`. The side conditions
// are unchanged; the conclusion is the congruence corollary. Every positive
// case is paired with a negative that breaks exactly one side condition.
// ============================================================================

#[test]
fn store_permutation_accepts_read_through_conclusion() {
    // (cl (= i0 i1) (= (select (store (store a i0 v0) i1 v1) k)
    //                  (select (store (store a i1 v1) i0 v0) k)))
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(a, &[1, 0]);
    let k = f.terms.mk_var("k", Sort::Int);
    let left_read = select(&mut f.terms, left, k);
    let right_read = select(&mut f.terms, right, k);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect("a read of two permuted chains at one shared index must certify");
}

#[test]
fn store_permutation_accepts_read_through_at_a_written_index() {
    // The read index may itself be one of the written indices: `L = R` holds
    // outright, so the reads agree at EVERY index. This is the `storecomm_sf`
    // benchmark shape.
    let mut f = Fixture::new(3);
    let a = f.a;
    let left = f.chain(a, &[0, 1, 2]);
    let right = f.chain(a, &[2, 1, 0]);
    let i0 = f.idx[0];
    let left_read = select(&mut f.terms, left, i0);
    let right_read = select(&mut f.terms, right, i0);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let mut clause = f.all_index_eqs(3);
    clause.push(conclusion);

    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect("a read at a written index of two permuted chains must certify");
}

#[test]
fn store_permutation_rejects_read_through_at_two_different_indices() {
    // NEGATIVE: the two reads use DIFFERENT index terms. `L = R` gives
    // `select(L,k1) = select(R,k1)`, never `select(L,k1) = select(R,k2)`, and
    // the clause carries no premise relating `k1` to `k2`.
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(a, &[1, 0]);
    let k1 = f.terms.mk_var("k1", Sort::Int);
    let k2 = f.terms.mk_var("k2", Sort::Int);
    let left_read = select(&mut f.terms, left, k1);
    let right_read = select(&mut f.terms, right, k2);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("two different read indices must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_read_through_missing_index_disequality() {
    // NEGATIVE: the read-through form inherits condition (5). With no index
    // pair literal the clause is FALSE when i0 = i1, v0 != v1 and k = i0.
    // A second, IRRELEVANT literal keeps the clause at the same length as the
    // accepted case, so length alone cannot be what rejects it.
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(a, &[1, 0]);
    let k = f.terms.mk_var("k", Sort::Int);
    let left_read = select(&mut f.terms, left, k);
    let right_read = select(&mut f.terms, right, k);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let filler = f.terms.mk_var("filler", Sort::Bool);

    let err = validate_strict(
        &f.terms,
        vec![filler, conclusion],
        TheoryLemmaKind::ArrayStorePermutation,
    )
    .expect_err("a read-through conclusion with no index-pair literal must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_read_through_over_different_bases() {
    // NEGATIVE: condition (1). The two chains write the same pairs but over
    // DIFFERENT base arrays, so their reads agree only where the bases do.
    let mut f = Fixture::new(2);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(b, &[1, 0]);
    let k = f.terms.mk_var("k", Sort::Int);
    let left_read = select(&mut f.terms, left, k);
    let right_read = select(&mut f.terms, right, k);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("read-through over two different base arrays must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_read_through_that_is_not_a_permutation() {
    // NEGATIVE: condition (4) under the read-through conclusion — the right
    // chain swaps the VALUES, not the writes.
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let (i0, i1, v0, v1) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let inner = store(&mut f.terms, a, i1, v0);
    let right = store(&mut f.terms, inner, i0, v1);
    let k = f.terms.mk_var("k", Sort::Int);
    let left_read = select(&mut f.terms, left, k);
    let right_read = select(&mut f.terms, right, k);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("a read-through of chains that are not a permutation must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_read_through_with_a_repeated_index_term() {
    // NEGATIVE: condition (3) under the read-through conclusion. The multisets
    // are equal and there is no pair of DISTINCT index terms to disequate, yet
    // the two chains differ at `i0` (v1 vs v0), so the reads differ there too.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_sort());
    let i0 = terms.mk_var("i0", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let left_inner = store(&mut terms, a, i0, v0);
    let left = store(&mut terms, left_inner, i0, v1);
    let right_inner = store(&mut terms, a, i0, v1);
    let right = store(&mut terms, right_inner, i0, v0);
    let left_read = select(&mut terms, left, k);
    let right_read = select(&mut terms, right, k);
    let conclusion = eq(&mut terms, left_read, right_read);
    let pair = eq(&mut terms, i0, k);

    let err = validate_strict(
        &terms,
        vec![pair, conclusion],
        TheoryLemmaKind::ArrayStorePermutation,
    )
    .expect_err("a repeated index term must be rejected in the read-through form too");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_read_through_of_a_single_write() {
    // NEGATIVE: condition (2) — one write per side is not a permutation the
    // schema is defined over, and the clause carries no index pair at all.
    let mut f = Fixture::new(1);
    let a = f.a;
    let left = f.chain(a, &[0]);
    let right = f.chain(a, &[0]);
    let k = f.terms.mk_var("k", Sort::Int);
    let left_read = select(&mut f.terms, left, k);
    let right_read = select(&mut f.terms, right, k);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let filler = f.terms.mk_var("filler", Sort::Bool);

    let err = validate_strict(
        &f.terms,
        vec![filler, conclusion],
        TheoryLemmaKind::ArrayStorePermutation,
    )
    .expect_err("a depth-one read-through must be rejected by the chain-length condition");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn store_permutation_rejects_read_through_where_one_side_is_not_a_read() {
    // NEGATIVE: a mixed conclusion `(= (select L k) R)` names no array pair —
    // the two sides do not even share a sort.
    let mut f = Fixture::new(2);
    let a = f.a;
    let left = f.chain(a, &[0, 1]);
    let right = f.chain(a, &[1, 0]);
    let k = f.terms.mk_var("k", Sort::Int);
    let left_read = select(&mut f.terms, left, k);
    let conclusion = eq(&mut f.terms, left_read, right);
    let mut clause = f.all_index_eqs(2);
    clause.push(conclusion);

    let err = validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayStorePermutation)
        .expect_err("a conclusion mixing a read with an array must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}
