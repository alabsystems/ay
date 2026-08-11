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
use ay_core::{
    ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};

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
fn row_chain_accepts_one_folded_and_one_exact_root_read() {
    // This is the shape emitted by sequence-layout proofs:
    //   L = store(B, x, v), R = store(B, y, v)
    //   (cl (not (= L R)) (= v (select R x)))
    // Under L = R, congruence transports the checked ROW1 fact L[x] = v to
    // R[x].  Evaluating R[x] itself would incorrectly require x != y; it is
    // deliberately retained as the exact root read.
    let mut f = Fixture::new(2);
    let b = f.a;
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);
    let right_read = select(&mut f.terms, right, x);
    let conclusion = eq(&mut f.terms, v, right_read);
    let clause = vec![premise, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("one checked ROW side plus one exact root read must certify");
    assert!(
        array_row_chain_printer_terms(&f.terms, &clause).is_some(),
        "the external printer must be able to replay the same exact schema"
    );
}

#[test]
fn row_chain_accepts_guarded_fallthrough_to_const_array_fill() {
    //   (cl (not (= A (store (const-array 0) 0 v)))
    //       (= 0 x)
    //       (= 0 (select A x)))
    // When A equals the store and x != 0, ROW2 reaches the constant-array
    // root, whose read is exactly its fill value.
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("x", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let constant = terms.mk_const_array(Sort::Int, zero);
    let folded = store(&mut terms, constant, zero, v);
    let a = terms.mk_var("A", array_sort());
    let premise_eq = eq(&mut terms, a, folded);
    let premise = terms.mk_not(premise_eq);
    let guard = eq(&mut terms, zero, x);
    let read = select(&mut terms, a, x);
    let conclusion = eq(&mut terms, zero, read);
    let clause = vec![premise, guard, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&terms, clause, TheoryLemmaKind::ArrayRowChain)
        .expect("a guarded store fallthrough to its const-array fill must certify");
}

#[test]
fn row_chain_rejects_unjustified_or_wrong_const_array_fallthrough() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let x = terms.mk_var("x", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let constant = terms.mk_const_array(Sort::Int, zero);
    let folded = store(&mut terms, constant, zero, v);
    let a = terms.mk_var("A", array_sort());
    let premise_eq = eq(&mut terms, a, folded);
    let premise = terms.mk_not(premise_eq);
    let read = select(&mut terms, a, x);
    let conclusion = eq(&mut terms, zero, read);

    validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("falling through a store requires its exact index-disequality guard");

    let guard = eq(&mut terms, zero, x);
    let wrong_conclusion = eq(&mut terms, one, read);
    validate_strict(
        &terms,
        vec![premise, guard, wrong_conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a const-array fallthrough must use the exact fill value");
}

#[test]
fn row_chain_accepts_equal_distinct_stores_forcing_base_alias() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let a = f.terms.mk_var("store-alias-a", array_sort());
    let (i, j, v) = (f.idx[0], f.idx[1], f.val[0]);
    let store_i = store(&mut f.terms, b, i, v);
    let store_j = store(&mut f.terms, b, j, v);
    let a_eq_i = eq(&mut f.terms, a, store_i);
    let not_a_eq_i = f.terms.mk_not(a_eq_i);
    let j_eq_a = eq(&mut f.terms, store_j, a);
    let not_j_eq_a = f.terms.mk_not(j_eq_a);
    let index_guard = eq(&mut f.terms, j, i);
    let base_alias = eq(&mut f.terms, a, b);
    let clause = vec![not_j_eq_a, base_alias, index_guard, not_a_eq_i];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain)
        .expect("equal same-value stores at distinct indices force the base alias");
}

#[test]
fn row_chain_rejects_forged_equal_stores_base_alias_variants() {
    let mut f = Fixture::new(3);
    let b = f.a;
    let other_base = f.terms.mk_var("store-alias-other-base", array_sort());
    let a = f.terms.mk_var("store-alias-a", array_sort());
    let other_anchor = f.terms.mk_var("store-alias-other-a", array_sort());
    let (i, j, wrong_index, v, wrong_value) = (f.idx[0], f.idx[1], f.idx[2], f.val[0], f.val[1]);
    let store_i = store(&mut f.terms, b, i, v);
    let store_j = store(&mut f.terms, b, j, v);
    let base_clause = |terms: &mut TermStore,
                       second_store: TermId,
                       second_anchor: TermId,
                       guard_rhs: TermId,
                       alias_base: TermId| {
        let first_eq = eq(terms, a, store_i);
        let first = terms.mk_not(first_eq);
        let second_eq = eq(terms, second_anchor, second_store);
        let second = terms.mk_not(second_eq);
        let guard = eq(terms, i, guard_rhs);
        let alias = eq(terms, alias_base, a);
        vec![first, second, guard, alias]
    };

    for (label, clause) in [
        (
            "different anchor",
            base_clause(&mut f.terms, store_j, other_anchor, j, b),
        ),
        (
            "wrong index guard",
            base_clause(&mut f.terms, store_j, a, wrong_index, b),
        ),
        (
            "wrong base conclusion",
            base_clause(&mut f.terms, store_j, a, j, other_base),
        ),
        ("different store base", {
            let other_store = store(&mut f.terms, other_base, j, v);
            base_clause(&mut f.terms, other_store, a, j, b)
        }),
        ("different stored value", {
            let other_store = store(&mut f.terms, b, j, wrong_value);
            base_clause(&mut f.terms, other_store, a, j, b)
        }),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_root_read_schema_with_swapped_orientations() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, right, left);
    let premise = f.terms.mk_not(premise_eq);
    let right_read = select(&mut f.terms, right, x);
    let conclusion = eq(&mut f.terms, right_read, v);
    let clause = vec![conclusion, premise];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("equality and clause orientation must not affect the schema");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());
}

#[test]
fn row_chain_accepts_exact_pure_root_read_congruence() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);
    let left_read = select(&mut f.terms, left, y);
    let right_read = select(&mut f.terms, right, y);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let clause = vec![premise, conclusion];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("the exact two-literal select-congruence schema must certify");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());

    // Replay the lemma inside a complete strict proof, rather than testing
    // only the isolated theory-step validator.
    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("exact select congruence must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_near_miss_pure_root_read_congruence() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let other = f.terms.mk_var("other", array_sort());
    let (i, j) = (f.idx[0], f.idx[1]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not(premise_eq);
    let read_a_i = select(&mut f.terms, a, i);
    let read_b_i = select(&mut f.terms, b, i);
    let read_b_j = select(&mut f.terms, b, j);
    let read_other_i = select(&mut f.terms, other, i);
    let exact = eq(&mut f.terms, read_a_i, read_b_i);
    let wrong_index = eq(&mut f.terms, read_a_i, read_b_j);
    let wrong_root = eq(&mut f.terms, read_a_i, read_other_i);
    let wrong_guard_eq = eq(&mut f.terms, a, other);
    let wrong_guard = f.terms.mk_not(wrong_guard_eq);
    let bool_index = f.terms.mk_var("bool_index", Sort::Bool);
    let ill_sorted_read = f
        .terms
        .mk_app(Symbol::named("select"), vec![b, bool_index], Sort::Int);
    let wrong_sort = eq(&mut f.terms, read_a_i, ill_sorted_read);
    let extra = eq(&mut f.terms, i, j);

    for (label, clause) in [
        ("wrong guard", vec![wrong_guard, exact]),
        ("wrong index", vec![premise, wrong_index]),
        ("wrong root", vec![premise, wrong_root]),
        ("wrong sort", vec![premise, wrong_sort]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain).expect_err(label);
        assert!(
            array_row_chain_printer_terms(&f.terms, &clause).is_none(),
            "{label}"
        );
    }
}

#[test]
fn row_chain_accepts_exact_const_array_read_under_equality() {
    let mut f = Fixture::new(1);
    let a = f.a;
    let i = f.idx[0];
    let fill = f.val[0];
    let constant = f.terms.mk_const_array(Sort::Int, fill);
    let premise_eq = eq(&mut f.terms, constant, a);
    let premise = f.terms.mk_not(premise_eq);
    let read = select(&mut f.terms, a, i);
    let conclusion = eq(&mut f.terms, fill, read);
    let clause = vec![conclusion, premise];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("an exact root read under equality with a const-array must certify");

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("const-array equality read must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_const_array_read_near_misses() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (i, j, fill, wrong_fill) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let constant = f.terms.mk_const_array(Sort::Int, fill);
    let premise_eq = eq(&mut f.terms, a, constant);
    let premise = f.terms.mk_not(premise_eq);
    let wrong_guard_eq = eq(&mut f.terms, a, b);
    let wrong_guard = f.terms.mk_not(wrong_guard_eq);
    let read_a_i = select(&mut f.terms, a, i);
    let read_a_j = select(&mut f.terms, a, j);
    let read_b_i = select(&mut f.terms, b, i);
    let exact = eq(&mut f.terms, read_a_i, fill);
    let wrong_guard_conclusion = eq(&mut f.terms, read_a_i, fill);
    let wrong_root = eq(&mut f.terms, read_b_i, fill);
    let wrong_fill_conclusion = eq(&mut f.terms, read_a_i, wrong_fill);
    let extra = eq(&mut f.terms, read_a_j, fill);

    for (label, clause) in [
        ("wrong guard", vec![wrong_guard, wrong_guard_conclusion]),
        ("wrong root", vec![premise, wrong_root]),
        ("wrong fill", vec![premise, wrong_fill_conclusion]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_exact_store_congruence_direct_and_packed() {
    let mut f = Fixture::new(2);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (index, value) = (f.idx[0], f.val[0]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not(premise_eq);
    let store_a = store(&mut f.terms, a, index, value);
    let store_b = store(&mut f.terms, b, index, value);
    let conclusion = eq(&mut f.terms, store_b, store_a);
    let direct = vec![premise, conclusion];

    validate_strict(&f.terms, direct.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("exact same-index/same-value store congruence must certify");
    assert!(
        array_row_chain_printer_terms(&f.terms, &direct).is_none(),
        "the ROW printer must fail closed on an unsupported store-congruence primitive"
    );

    let packed = f
        .terms
        .mk_app(Symbol::named("or"), direct.clone(), Sort::Bool);
    validate_strict(&f.terms, vec![packed], TheoryLemmaKind::ArrayRowChain)
        .expect("the exact packed-OR form emitted by AY must certify");

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", direct, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("exact store congruence must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_packed_non_bool_equality_child() {
    let mut f = Fixture::new(1);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (index, value) = (f.idx[0], f.val[0]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not_raw(premise_eq);
    let store_a = store(&mut f.terms, a, index, value);
    let store_b = store(&mut f.terms, b, index, value);
    let malformed_conclusion =
        f.terms
            .mk_app(Symbol::named("="), vec![store_a, store_b], Sort::Int);
    let packed = f.terms.mk_app(
        Symbol::named("or"),
        vec![premise, malformed_conclusion],
        Sort::Bool,
    );

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &[packed]),
        None,
        "classification must reject malformed packed children"
    );
    validate_strict(&f.terms, vec![packed], TheoryLemmaKind::ArrayRowChain)
        .expect_err("strict row replay must reject malformed packed children");
}

#[test]
fn row_chain_rejects_store_congruence_near_misses() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let other = f.terms.mk_var("other", array_sort());
    let (index, wrong_index, value, wrong_value) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not(premise_eq);
    let wrong_guard_eq = eq(&mut f.terms, a, other);
    let wrong_guard = f.terms.mk_not(wrong_guard_eq);
    let store_a = store(&mut f.terms, a, index, value);
    let store_b = store(&mut f.terms, b, index, value);
    let store_b_wrong_index = store(&mut f.terms, b, wrong_index, value);
    let store_b_wrong_value = store(&mut f.terms, b, index, wrong_value);
    let store_other = store(&mut f.terms, other, index, value);
    let exact = eq(&mut f.terms, store_a, store_b);
    let wrong_root = eq(&mut f.terms, store_a, store_other);
    let wrong_index_conclusion = eq(&mut f.terms, store_a, store_b_wrong_index);
    let wrong_value_conclusion = eq(&mut f.terms, store_a, store_b_wrong_value);
    let bool_index = f.terms.mk_var("bool_store_index", Sort::Bool);
    let ill_sorted_store = f.terms.mk_app(
        Symbol::named("store"),
        vec![b, bool_index, value],
        array_sort(),
    );
    let wrong_sort = eq(&mut f.terms, store_a, ill_sorted_store);
    let extra = eq(&mut f.terms, index, wrong_index);

    for (label, clause) in [
        ("wrong guard", vec![wrong_guard, exact]),
        ("wrong root", vec![premise, wrong_root]),
        ("wrong index", vec![premise, wrong_index_conclusion]),
        ("wrong value", vec![premise, wrong_value_conclusion]),
        ("wrong sort", vec![premise, wrong_sort]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_exact_store_idempotence_under_equality() {
    let mut f = Fixture::new(2);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (index, value) = (f.idx[0], f.val[0]);
    let stored = store(&mut f.terms, b, index, value);
    let premise_eq = eq(&mut f.terms, stored, a);
    let premise = f.terms.mk_not(premise_eq);
    let rewritten = store(&mut f.terms, a, index, value);
    let conclusion = eq(&mut f.terms, stored, rewritten);
    let clause = vec![conclusion, premise];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("the exact depth-one store-idempotence rewrite must certify");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_none());

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("store idempotence must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_store_idempotence_near_misses() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let other = f.terms.mk_var("other", array_sort());
    let (index, wrong_index, value, wrong_value) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let stored = store(&mut f.terms, b, index, value);
    let premise_eq = eq(&mut f.terms, a, stored);
    let premise = f.terms.mk_not(premise_eq);
    let rewritten = store(&mut f.terms, a, index, value);
    let exact = eq(&mut f.terms, stored, rewritten);
    let wrong_splice_store = store(&mut f.terms, other, index, value);
    let wrong_splice = eq(&mut f.terms, stored, wrong_splice_store);
    let wrong_index_store = store(&mut f.terms, a, wrong_index, value);
    let wrong_index_conclusion = eq(&mut f.terms, stored, wrong_index_store);
    let wrong_value_store = store(&mut f.terms, a, index, wrong_value);
    let wrong_value_conclusion = eq(&mut f.terms, stored, wrong_value_store);
    let inner = store(&mut f.terms, b, wrong_index, wrong_value);
    let depth_two = store(&mut f.terms, inner, index, value);
    let depth_guard_eq = eq(&mut f.terms, a, depth_two);
    let depth_guard = f.terms.mk_not(depth_guard_eq);
    let depth_rewritten = store(&mut f.terms, a, index, value);
    let depth_conclusion = eq(&mut f.terms, depth_two, depth_rewritten);
    let bool_index = f.terms.mk_var("bool_idempotence_index", Sort::Bool);
    let ill_sorted = f.terms.mk_app(
        Symbol::named("store"),
        vec![a, bool_index, value],
        array_sort(),
    );
    let wrong_sort = eq(&mut f.terms, stored, ill_sorted);
    let negated_conclusion = f.terms.mk_not(exact);
    let extra = eq(&mut f.terms, index, wrong_index);

    for (label, clause) in [
        ("positive guard", vec![premise_eq, exact]),
        ("negative conclusion", vec![premise, negated_conclusion]),
        ("wrong A/B splice", vec![premise, wrong_splice]),
        ("different index", vec![premise, wrong_index_conclusion]),
        ("different value", vec![premise, wrong_value_conclusion]),
        ("depth-two stored term", vec![depth_guard, depth_conclusion]),
        ("ill-sorted raw store", vec![premise, wrong_sort]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_exact_guarded_matching_outer_store_reads() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let c_root = f.terms.mk_var("c_root", array_sort());
    // Keep C non-atomic, as in the Seq proof. The generic ROW-chain lane
    // cannot walk through this inner store without another guard; schema (H)
    // must treat C as the exact outer-store base and inspect nothing below it.
    let c = store(&mut f.terms, c_root, f.idx[2], f.val[2]);
    let (store_index, read_index, value) = (f.idx[0], f.idx[1], f.val[0]);
    let left_store = store(&mut f.terms, a, store_index, value);
    let right_store = store(&mut f.terms, c, store_index, value);
    let premise_eq = eq(&mut f.terms, left_store, right_store);
    let premise = f.terms.mk_not(premise_eq);
    let guard = eq(&mut f.terms, store_index, read_index);
    let right_base_read = select(&mut f.terms, c, read_index);
    let left_store_read = select(&mut f.terms, left_store, read_index);
    let conclusion = eq(&mut f.terms, right_base_read, left_store_read);
    let direct = vec![guard, premise, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &direct),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, direct.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("the exact store/base form emitted by the Seq proof must certify");
    assert!(
        array_row_chain_printer_terms(&f.terms, &direct).is_none(),
        "the external printer must fail closed until it has an independent lowering"
    );

    let packed = f
        .terms
        .mk_app(Symbol::named("or"), direct.clone(), Sort::Bool);
    validate_strict(&f.terms, vec![packed], TheoryLemmaKind::ArrayRowChain)
        .expect("the packed-OR form must use the same exact checker lane");

    // Also cover the base/base form and equality orientations. The checker
    // treats each endpoint independently but keeps them on opposite sides.
    let left_base_read = select(&mut f.terms, a, read_index);
    let base_conclusion = eq(&mut f.terms, right_base_read, left_base_read);
    let reversed_premise_eq = eq(&mut f.terms, right_store, left_store);
    let reversed_premise = f.terms.mk_not(reversed_premise_eq);
    validate_strict(
        &f.terms,
        vec![base_conclusion, reversed_premise, guard],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("the exact base/base and reversed-orientation form must certify");

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", direct, TheoryLemmaKind::ArrayRowChain);
    let premise_assumption = proof.add_assume(premise_eq, None);
    let after_premise = proof.add_resolution(
        vec![guard, conclusion],
        premise_eq,
        lemma,
        premise_assumption,
    );
    let not_guard = f.terms.mk_not(guard);
    let guard_assumption = proof.add_assume(not_guard, None);
    let unit_conclusion =
        proof.add_resolution(vec![conclusion], guard, after_premise, guard_assumption);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("the guarded store-read lemma must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_guarded_matching_outer_store_read_near_misses() {
    let mut f = Fixture::new(4);
    let a = f.a;
    let c_root = f.terms.mk_var("c_root", array_sort());
    let c = store(&mut f.terms, c_root, f.idx[3], f.val[2]);
    let other = f.terms.mk_var("other", array_sort());
    let (store_index, read_index, wrong_index, value, wrong_value) =
        (f.idx[0], f.idx[1], f.idx[2], f.val[0], f.val[1]);
    let left_store = store(&mut f.terms, a, store_index, value);
    let right_store = store(&mut f.terms, c, store_index, value);
    let premise_eq = eq(&mut f.terms, left_store, right_store);
    let premise = f.terms.mk_not(premise_eq);
    let guard = eq(&mut f.terms, store_index, read_index);
    let wrong_guard = eq(&mut f.terms, wrong_index, read_index);
    let negative_guard = f.terms.mk_not(guard);
    let left_store_read = select(&mut f.terms, left_store, read_index);
    let right_base_read = select(&mut f.terms, c, read_index);
    let exact = eq(&mut f.terms, left_store_read, right_base_read);
    let negative_conclusion = f.terms.mk_not(exact);
    let wrong_root_read = select(&mut f.terms, other, read_index);
    let wrong_root = eq(&mut f.terms, left_store_read, wrong_root_read);
    let right_wrong_read = select(&mut f.terms, c, wrong_index);
    let wrong_read_index = eq(&mut f.terms, left_store_read, right_wrong_read);
    let right_wrong_outer_index = store(&mut f.terms, c, wrong_index, value);
    let wrong_index_premise_eq = eq(&mut f.terms, left_store, right_wrong_outer_index);
    let wrong_index_premise = f.terms.mk_not(wrong_index_premise_eq);
    let right_wrong_value = store(&mut f.terms, c, store_index, wrong_value);
    let wrong_value_premise_eq = eq(&mut f.terms, left_store, right_wrong_value);
    let wrong_value_premise = f.terms.mk_not(wrong_value_premise_eq);
    let extra = eq(&mut f.terms, read_index, wrong_index);

    for (label, clause) in [
        ("missing guard", vec![premise, exact]),
        ("wrong guard", vec![wrong_guard, premise, exact]),
        ("negative guard", vec![negative_guard, premise, exact]),
        ("positive premise", vec![guard, premise_eq, exact]),
        (
            "different outer index",
            vec![guard, wrong_index_premise, exact],
        ),
        (
            "different outer value",
            vec![guard, wrong_value_premise, exact],
        ),
        ("wrong read root", vec![guard, premise, wrong_root]),
        (
            "different read indices",
            vec![guard, premise, wrong_read_index],
        ),
        (
            "negative conclusion",
            vec![guard, premise, negative_conclusion],
        ),
        ("extra literal", vec![guard, premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_rejects_wrong_root_read_endpoint() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let other = f.terms.mk_var("other", array_sort());
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);
    let wrong_read = select(&mut f.terms, other, x);
    let conclusion = eq(&mut f.terms, v, wrong_read);
    let clause = vec![premise, conclusion];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect_err("the raw endpoint must be the exact premise-array root read");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_none());
}

#[test]
fn row_chain_rejects_root_read_at_the_wrong_index_or_value() {
    let mut f = Fixture::new(3);
    let b = f.a;
    let (x, y, wrong_index, v, wrong_value) = (f.idx[0], f.idx[1], f.idx[2], f.val[0], f.val[1]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);

    let wrong_read = select(&mut f.terms, right, wrong_index);
    let wrong_index_conclusion = eq(&mut f.terms, v, wrong_read);
    validate_strict(
        &f.terms,
        vec![premise, wrong_index_conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("the folded and raw sides must use the same exact index");

    let right_read = select(&mut f.terms, right, x);
    let wrong_value_conclusion = eq(&mut f.terms, wrong_value, right_read);
    validate_strict(
        &f.terms,
        vec![premise, wrong_value_conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("the folded side must end at the exact stored value");
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
