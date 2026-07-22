// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode tests for the n-ary array schemas `ArrayStorePermutation` and
//! `ArrayRowChain`.
//!
//! These are the schemas that let QF_AX `storecomm` / `read5` UNSAT proofs stop
//! emitting `:rule trust`. Because a WRONG UNSAT is total failure, every
//! positive test is paired with a negative test that breaks exactly one side
//! condition and asserts the checker REJECTS.

use crate::checker::*;
use ay_core::{ArraySort, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

/// Validate a `TheoryLemma` step in strict mode.
fn validate_strict(
    terms: &TermStore,
    clause: Vec<TermId>,
    kind: TheoryLemmaKind,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause,
        farkas: None,
        kind,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

/// `(Array Int Int)`.
fn array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

fn store(terms: &mut TermStore, array: TermId, index: TermId, value: TermId) -> TermId {
    let sort = terms.sort(array).clone();
    terms.mk_app(Symbol::named("store"), vec![array, index, value], sort)
}

fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![array, index], Sort::Int)
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// Base array `a` plus indices `i0..` and values `v0..`.
struct Fixture {
    terms: TermStore,
    a: TermId,
    idx: Vec<TermId>,
    val: Vec<TermId>,
}

impl Fixture {
    fn new(n: usize) -> Self {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", array_sort());
        let idx = (0..n)
            .map(|k| terms.mk_var(format!("i{k}"), Sort::Int))
            .collect();
        let val = (0..n)
            .map(|k| terms.mk_var(format!("v{k}"), Sort::Int))
            .collect();
        Self { terms, a, idx, val }
    }

    /// `store(... store(base, idx[order[0]], val[order[0]]) ..., idx[last], val[last])`
    /// — `order` lists the writes innermost-first.
    fn chain(&mut self, base: TermId, order: &[usize]) -> TermId {
        let mut current = base;
        for &k in order {
            current = store(&mut self.terms, current, self.idx[k], self.val[k]);
        }
        current
    }

    /// Every `(= i_p i_q)` literal for `p < q` over the first `n` indices.
    fn all_index_eqs(&mut self, n: usize) -> Vec<TermId> {
        let mut out = Vec::new();
        for p in 0..n {
            for q in (p + 1)..n {
                let (ip, iq) = (self.idx[p], self.idx[q]);
                out.push(eq(&mut self.terms, ip, iq));
            }
        }
        out
    }
}

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

// ============================================================================
// ArrayRowChain — sub-schema (A), chain evaluation
// ============================================================================

#[test]
fn row_chain_accepts_chain_read_with_all_skips_justified() {
    // (cl (= i0 i2) (= i0 i1) (= (select (store (store (store a i0 v0) i1 v1) i2 v2) i0) v0))
    // Reading at i0 skips the i2 and i1 writes; both skips carry their literal.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);

    validate_strict(
        &f.terms,
        vec![skip2, skip1, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("a fully-justified chain read must certify");
}

#[test]
fn row_chain_rejects_chain_read_with_an_unjustified_skip() {
    // NEGATIVE: the `(= i0 i1)` literal is missing, so nothing rules out
    // i0 = i1, under which the read yields v1, not v0.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let i2 = f.idx[2];
    let skip2 = eq(&mut f.terms, i0, i2);

    let err = validate_strict(
        &f.terms,
        vec![skip2, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("an unjustified store skip must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_wrong_evaluated_value() {
    // NEGATIVE: every skip is justified, but the clause claims the read equals
    // v1 rather than the actual v0.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v1 = f.val[1];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v1);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);

    let err = validate_strict(
        &f.terms,
        vec![skip2, skip1, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a mis-evaluated chain read must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_accepts_read_falling_through_to_the_base_array() {
    // Every write is skipped, so the read is the base array's own read.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[1, 2]);
    let i0 = f.idx[0];
    let read = select(&mut f.terms, chain, i0);
    let base_read = select(&mut f.terms, a, i0);
    let conclusion = eq(&mut f.terms, read, base_read);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);

    validate_strict(
        &f.terms,
        vec![skip1, skip2, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("a fully-skipped chain read must reduce to the base read");
}

// ============================================================================
// ArrayRowChain — sub-schema (B), read-out under an array equality
// ============================================================================

#[test]
fn row_chain_accepts_read_out_under_array_equality() {
    // read5's shape:
    //   (cl (= i0 i2) (not (= (store (store a i0 v0) i2 v2) b))
    //       (= v0 (select b i0)))
    // If the two arrays are equal and i0 != i2, reading both at i0 gives
    // v0 on the left and (select b i0) on the right.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0, 2]);
    let premise_eq = eq(&mut f.terms, left, b);
    let premise = f.terms.mk_not(premise_eq);
    let i0 = f.idx[0];
    let i2 = f.idx[2];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);
    let skip = eq(&mut f.terms, i0, i2);

    validate_strict(
        &f.terms,
        vec![skip, premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("a justified read-out under an array equality must certify");
}

#[test]
fn row_chain_rejects_read_out_with_an_unjustified_skip() {
    // NEGATIVE: same clause, minus the `(= i0 i2)` literal. With i0 = i2 the
    // left chain reads v2 at i0, so the conclusion does not follow.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0, 2]);
    let premise_eq = eq(&mut f.terms, left, b);
    let premise = f.terms.mk_not(premise_eq);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);

    let err = validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("an unjustified skip under an array equality must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_read_out_without_the_array_equality_premise() {
    // NEGATIVE: drop the `(not (= L R))` premise. `v0 = (select b i0)` alone is
    // plainly falsifiable.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let _left = f.chain(a, &[0, 2]);
    let i0 = f.idx[0];
    let i2 = f.idx[2];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);
    let skip = eq(&mut f.terms, i0, i2);

    let err = validate_strict(
        &f.terms,
        vec![skip, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a read-out with no array-equality premise must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_read_out_at_mismatched_indices() {
    // NEGATIVE: the premise arrays are read at DIFFERENT indices — the left
    // side is evaluated at i0 but the conclusion's select is at i1.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0]);
    let premise_eq = eq(&mut f.terms, left, b);
    let premise = f.terms.mk_not(premise_eq);
    let i1 = f.idx[1];
    let v0 = f.val[0];
    let other_read = select(&mut f.terms, b, i1);
    let conclusion = eq(&mut f.terms, v0, other_read);

    let err = validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a read-out whose two sides use different indices must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_array_equality_used_positively() {
    // NEGATIVE: the array equality is a POSITIVE literal, so the clause reads
    // "L = R OR v0 = select(b,i0)" — satisfiable, not a tautology.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0]);
    let premise = eq(&mut f.terms, left, b);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);

    let err = validate_strict(
        &f.terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a positive array equality is not a usable premise");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_recognizer_declines_unjustified_skip() {
    // Classifier/checker agreement on the fail-closed side.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let i2 = f.idx[2];
    let skip2 = eq(&mut f.terms, i0, i2);

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &[skip2, conclusion]),
        None
    );
}

#[test]
fn row_chain_recognizer_agrees_with_validator() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);
    let clause = vec![skip2, skip1, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain)
        .expect("recognized clause must validate");
}

// ============================================================================
// Cross-schema fail-closed guards
// ============================================================================

#[test]
fn new_array_kinds_reject_an_arbitrary_boolean_clause() {
    // The classic forgery: a bare Boolean literal labelled as an array axiom.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    for kind in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        let err = validate_strict(&terms, vec![p], kind)
            .expect_err("a bare Boolean clause is not an array axiom");
        assert!(
            matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
            "expected InvalidTheoryLemma for {kind:?}, got {err:?}"
        );
    }
}

#[test]
fn new_array_kinds_reject_empty_clause() {
    let terms = TermStore::new();
    for kind in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        validate_strict(&terms, vec![], kind)
            .expect_err("an empty array-axiom clause must be rejected");
    }
}

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
