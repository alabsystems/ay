// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Same-index store-value equality regressions.

use super::*;

// ============================================================================
// ArrayRowChain sub-schema (I): same-index store equality forces value equality
// ============================================================================

/// `(not term)` as a raw application, mirroring what the proof emitter builds.
fn not_term(terms: &mut TermStore, term: TermId) -> TermId {
    terms.mk_not_raw(term)
}

#[test]
fn same_index_store_value_equality_accepts_the_exact_schema() {
    // (cl (not (= (store x i v) (store y i w))) (= v w))
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left = store(&mut terms, x, i, v);
    let right = store(&mut terms, y, i, w);
    let premise_eq = eq(&mut terms, left, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, v, w);

    validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("equal same-index stores force the written values equal");
}

#[test]
fn same_index_store_value_equality_accepts_reversed_literal_order() {
    // Same clause with the conclusion FIRST and the value equality written in
    // the opposite orientation.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left = store(&mut terms, x, i, v);
    let right = store(&mut terms, y, i, w);
    let premise_eq = eq(&mut terms, left, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, w, v);

    validate_strict(
        &terms,
        vec![conclusion, premise],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("literal order and equality orientation must not matter");
}

#[test]
fn same_index_store_value_equality_accepts_deeper_bases() {
    // The bases are arbitrary — here both are themselves stores. Only the
    // OUTERMOST write is peeled, and the argument never mentions the bases.
    let mut f = Fixture::new(2);
    let a = f.a;
    let deep_left = f.chain(a, &[0]);
    let deep_right = f.chain(a, &[1]);
    let i = f.terms.mk_var("i", Sort::Int);
    let v = f.terms.mk_var("v", Sort::Int);
    let w = f.terms.mk_var("w", Sort::Int);
    let left = store(&mut f.terms, deep_left, i, v);
    let right = store(&mut f.terms, deep_right, i, w);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = not_term(&mut f.terms, premise_eq);
    let conclusion = eq(&mut f.terms, v, w);

    validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("the bases under the outermost write are unconstrained");
}

#[test]
fn same_index_store_value_equality_rejects_different_write_indices() {
    // NEGATIVE: `store(x,i,v) = store(y,j,w)` with i != j does NOT force v = w
    // (take y = store(x,i,v) and x = store(y,j,w) with v != w).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left = store(&mut terms, x, i, v);
    let right = store(&mut terms, y, j, w);
    let premise_eq = eq(&mut terms, left, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, v, w);

    let err = validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("two different write indices must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn same_index_store_value_equality_rejects_an_unrelated_conclusion() {
    // NEGATIVE: the conclusion equates a written value with a THIRD term the
    // premise never mentions.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let left = store(&mut terms, x, i, v);
    let right = store(&mut terms, y, i, w);
    let premise_eq = eq(&mut terms, left, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, v, u);

    let err = validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a conclusion naming a term the premise never writes must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn same_index_store_value_equality_rejects_a_positive_premise() {
    // NEGATIVE: the store equality must appear NEGATED. As a positive literal
    // the clause reads `store(x,i,v) = store(y,i,w) OR v = w`, which is false
    // whenever both disjuncts are.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left = store(&mut terms, x, i, v);
    let right = store(&mut terms, y, i, w);
    let premise = eq(&mut terms, left, right);
    let conclusion = eq(&mut terms, v, w);

    let err = validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a non-negated store-equality premise must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn same_index_store_value_equality_rejects_a_non_store_side() {
    // NEGATIVE: `x = store(y,i,w)` says nothing about any value written into
    // `x`, so no value equality follows.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let right = store(&mut terms, y, i, w);
    let premise_eq = eq(&mut terms, x, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, v, w);

    let err = validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a premise side that is not a store must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn same_index_store_value_equality_rejects_an_extra_literal() {
    // NEGATIVE: sub-schema (I) is EXACT at two literals. A third literal is
    // refused rather than silently widened; a genuinely weakened clause has to
    // be derived by `weakening`, which records the step.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let filler = terms.mk_var("filler", Sort::Bool);
    let left = store(&mut terms, x, i, v);
    let right = store(&mut terms, y, i, w);
    let premise_eq = eq(&mut terms, left, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, v, w);

    let err = validate_strict(
        &terms,
        vec![premise, conclusion, filler],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("sub-schema (I) is exact at two literals");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn same_index_store_value_equality_rejects_an_ill_sorted_store() {
    // NEGATIVE: the right "store" writes a Bool into an Int-element array.
    // `TermStore` permits the raw application, so the checker has to
    // re-establish the signature itself.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", array_sort());
    let y = terms.mk_var("y", array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Bool);
    let left = store(&mut terms, x, i, v);
    let sort = terms.sort(y).clone();
    let right = terms.mk_app(Symbol::named("store"), vec![y, i, w], sort);
    let premise_eq = eq(&mut terms, left, right);
    let premise = not_term(&mut terms, premise_eq);
    let conclusion = eq(&mut terms, v, w);

    let err = validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("an ill-sorted store application must not be read as an array op");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}
