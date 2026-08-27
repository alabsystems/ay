// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The adversarial half of the BOOL-ERASED folded extensionality battery:
//! every way the fold or the witness provenance can be wrong, plus the
//! exhaustive sweep. Each negative names a CONCRETE falsifying assignment and
//! CHECKS it with the independent bounded model in the parent module.

use super::*;

// ============================================================================
// NEGATIVE: each breaks the FOLD, and each is refutable at a named point.
// ============================================================================

#[test]
fn a_value_side_naming_the_wrong_stored_value_is_refutable_and_declined() {
    // The chain writes `true` at `i` but the value side is `(not (= i k))`, so
    // it names the OPPOSITE of the write.
    // FALSIFYING ASSIGNMENT: `i = 0`, `k = 1`, `E = [true, true]`. Then
    // `C = store(const(false), 0, true) = [true, false]`, so `E != C` and the
    // array equality is FALSE; and `select(E, 1) = true` while the value side
    // `(not (0 = 1))` is `true`, so the read equality HOLDS and its negation is
    // FALSE. Every literal is FALSE.
    let mut f = Corpus::new();
    let guard = eq(&mut f.terms, f.write_index, f.witness);
    let value = f.terms.mk_not(guard);
    let read = select(&mut f.terms, f.root, f.witness);
    let premise = eq(&mut f.terms, f.root, f.chain);
    let conclusion_eq = eq(&mut f.terms, read, value);
    let conclusion = f.terms.mk_not(conclusion_eq);
    let clause = folded_ext_clause(&mut f.terms, f.root, f.chain, read, value);
    let binding = f.binding(vec![1, 1], 0, 1);
    refuted_and_declined(
        &f.terms,
        clause,
        &[premise, conclusion],
        f.root,
        f.chain,
        f.witness,
        &binding,
    );
}

#[test]
fn a_const_base_with_the_wrong_default_is_refutable_and_declined() {
    // The chain's base is `const(true)` but the erased ELSE branch of `(= i k)`
    // is `false`.
    // FALSIFYING ASSIGNMENT: `i = 0`, `k = 1`, `E = [true, false]`. Then
    // `C = store(const(true), 0, true) = [true, true]`, so `E != C`; and
    // `select(E, 1) = false` while the value side `(0 = 1)` is `false`, so the
    // read equality HOLDS and its negation is FALSE.
    let mut terms = TermStore::new();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), truth);
    let i = terms.mk_var("i", index_sort());
    let k = terms.mk_var("__ay_ext_diff!9", index_sort());
    let root = terms.mk_var("E", bool_array_sort());
    let chain = store(&mut terms, base, i, truth);
    let value = eq(&mut terms, i, k);
    let read = select(&mut terms, root, k);
    let premise = eq(&mut terms, root, chain);
    let conclusion_eq = eq(&mut terms, read, value);
    let conclusion = terms.mk_not(conclusion_eq);
    let clause = folded_ext_clause(&mut terms, root, chain, read, value);
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (k, Value::Index(1)),
    ];
    refuted_and_declined(
        &terms,
        clause,
        &[premise, conclusion],
        root,
        chain,
        k,
        &binding,
    );
}

#[test]
fn a_guard_over_an_unrelated_index_is_refutable_and_declined() {
    // The chain writes at `i`; the erased fold's guard tests a THIRD index `j`.
    // FALSIFYING ASSIGNMENT: `i = 0`, `j = 1`, `k = 0`, `E = [false, true]`.
    // `C = store(const(false), 0, true) = [true, false]`, so `E != C` and the
    // array equality is FALSE; `select(E, 0) = false` and the value side
    // `(1 = 0)` is `false`, so the read equality HOLDS and its negation is
    // FALSE. Every literal is FALSE.
    let mut f = Corpus::new();
    let other = f.terms.mk_var("j", index_sort());
    let value = eq(&mut f.terms, other, f.witness);
    let read = select(&mut f.terms, f.root, f.witness);
    let premise = eq(&mut f.terms, f.root, f.chain);
    let conclusion_eq = eq(&mut f.terms, read, value);
    let conclusion = f.terms.mk_not(conclusion_eq);
    let clause = folded_ext_clause(&mut f.terms, f.root, f.chain, read, value);
    let mut binding = f.binding(vec![0, 1], 0, 0);
    binding.push((other, Value::Index(1)));
    refuted_and_declined(
        &f.terms,
        clause,
        &[premise, conclusion],
        f.root,
        f.chain,
        f.witness,
        &binding,
    );
}

#[test]
fn a_bool_fold_at_a_non_bool_element_sort_is_declined() {
    // The two erased readings are offered ONLY at element sort `Bool`. At any
    // other sort `mk_ite` leaves the `Ite` node alone, so reading a bare `=` as
    // `ite(c, true, false)` would be reading structure no fold produced. The
    // element-sort test is BACKSTOPPED by the well-sortedness test at the top
    // of the walk (a `=` term is always `Bool`-sorted, so it can never be an
    // element of a non-`Bool` array) — the mutation ledger records that this
    // guard alone is not enough to turn a fixture red, and names the backstop.
    let mut terms = TermStore::new();
    let index_array = Sort::Array(Box::new(ArraySort::new(index_sort(), index_sort())));
    let i = terms.mk_var("i", index_sort());
    let k = terms.mk_var("__ay_ext_diff!11", index_sort());
    let v = terms.mk_var("v", index_sort());
    let root = terms.mk_var("E", index_array.clone());
    let base = terms.mk_var("B", index_array);
    let chain = store(&mut terms, base, i, v);
    let value = eq(&mut terms, i, k);
    let read = select(&mut terms, root, k);
    let clause = folded_ext_clause(&mut terms, root, chain, read, value);
    assert!(
        !recognize_folded_array_extensionality(&terms, &[clause], root, chain, k),
        "a Bool-erased reading must not be offered at a non-Bool element sort"
    );
}

#[test]
fn an_erased_branch_under_a_deeper_store_is_refutable_and_declined() {
    // The erased branch is a CONSTANT: it can never be a raw select, and the
    // remaining `mk_ite` Bool rewrites (`(or c x)`, `(and c x)`) are
    // deliberately not decoded. A two-store chain therefore fails closed
    // instead of being read through the erased branch — and it must, because
    // the true denotation is `(or (= i k) (= j k))`, not `(= i k)`.
    //
    // FALSIFYING ASSIGNMENT: `i = 0`, `j = 1`, `k = 1`, `E = [true, false]`.
    // `C = store(store(const(false), 1, true), 0, true) = [true, true]`, so
    // `E != C` and the array equality is FALSE; `select(E, 1) = false` and the
    // value side `(0 = 1)` is `false`, so the read equality HOLDS and its
    // negation is FALSE. Every literal is FALSE.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let k = terms.mk_var("__ay_ext_diff!13", index_sort());
    let root = terms.mk_var("E", bool_array_sort());
    let inner = store(&mut terms, base, j, truth);
    let chain = store(&mut terms, inner, i, truth);
    let value = eq(&mut terms, i, k);
    let read = select(&mut terms, root, k);
    let premise = eq(&mut terms, root, chain);
    let conclusion_eq = eq(&mut terms, read, value);
    let conclusion = terms.mk_not(conclusion_eq);
    let clause = folded_ext_clause(&mut terms, root, chain, read, value);
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(1)),
        (k, Value::Index(1)),
    ];
    refuted_and_declined(
        &terms,
        clause,
        &[premise, conclusion],
        root,
        chain,
        k,
        &binding,
    );
}

// ============================================================================
// PROVENANCE: the accept is authority, and every condition is load-bearing.
// ============================================================================

#[test]
fn the_corpus_leaf_is_rejected_without_an_introduction() {
    let mut f = Corpus::new();
    let clause = f.clause();
    let error = check_provenance(&f.terms, vec![ext_lemma_step(clause)], &f.problem)
        .expect_err("a folded leaf with no introduction must be rejected");
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected an InvalidTheoryLemma rejection, got {error:?}"
    );
}

#[test]
fn the_corpus_leaf_is_rejected_when_the_introduction_names_another_pair() {
    let mut f = Corpus::new();
    let clause = f.clause();
    let other = f.terms.mk_var("F", bool_array_sort());
    let error = check_provenance(
        &f.terms,
        vec![intro_step(f.witness, f.root, other), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect_err("an introduction for a DIFFERENT pair must not license this clause");
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected an InvalidTheoryLemma rejection, got {error:?}"
    );
}

#[test]
fn the_corpus_leaf_is_rejected_when_the_witness_is_not_fresh() {
    let mut f = Corpus::new();
    let clause = f.clause();
    // The problem itself constrains the witness, so it witnesses nothing.
    let read = select(&mut f.terms, f.root, f.witness);
    let mut problem = f.problem.clone();
    problem.push(read);
    let error = check_provenance(
        &f.terms,
        vec![
            intro_step(f.witness, f.root, f.chain),
            ext_lemma_step(clause),
        ],
        &problem,
    )
    .expect_err("a witness the problem also constrains must be rejected");
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected an InvalidTheoryLemma rejection, got {error:?}"
    );
}

// ============================================================================
// SWEEP: every one-store Bool chain the producer can emit, both polarities,
// with every ACCEPT's denotation re-checked by the independent model.
// ============================================================================

#[test]
fn sweep_one_store_bool_chains_accept_exactly_the_true_denotations() {
    // 2 fills x 2 stored values x 2 spellings of the erased value side x
    // 2 guard argument orders = 16 clauses. Ground truth is computed by the
    // INDEPENDENT model, not by the recognizer.
    let mut accepted = 0usize;
    let mut declined = 0usize;
    for fill in [false, true] {
        for stored in [false, true] {
            for negate_value in [false, true] {
                for flip_guard in [false, true] {
                    let mut terms = TermStore::new();
                    let falsity = terms.false_term();
                    let truth = terms.true_term();
                    let fill_term = if fill { truth } else { falsity };
                    let stored_term = if stored { truth } else { falsity };
                    let base = terms.mk_const_array(index_sort(), fill_term);
                    let i = terms.mk_var("i", index_sort());
                    let k = terms.mk_var("__ay_ext_diff!1", index_sort());
                    let root = terms.mk_var("E", bool_array_sort());
                    let chain = store(&mut terms, base, i, stored_term);
                    let guard = if flip_guard {
                        eq(&mut terms, k, i)
                    } else {
                        eq(&mut terms, i, k)
                    };
                    let value = if negate_value {
                        terms.mk_not(guard)
                    } else {
                        guard
                    };
                    let read = select(&mut terms, root, k);
                    let clause = folded_ext_clause(&mut terms, root, chain, read, value);
                    let got =
                        recognize_folded_array_extensionality(&terms, &[clause], root, chain, k);
                    // The denotation is true exactly when the stored value is
                    // the guard's `then` branch and the fill is its `else`.
                    let want = if negate_value {
                        !stored && fill
                    } else {
                        stored && !fill
                    };
                    assert_eq!(
                        got, want,
                        "fill={fill} stored={stored} negate={negate_value} flip={flip_guard}"
                    );
                    if got {
                        accepted += 1;
                        denotation_holds_everywhere(&mut terms, chain, k, value);
                    } else {
                        declined += 1;
                    }
                }
            }
        }
    }
    // Exactly one `(fill, stored)` pair works for each of the two erased
    // readings, and the guard's argument order is irrelevant: 2 x 2 = 4.
    assert_eq!(accepted, 4, "exactly one (fill, stored) pair per reading");
    assert_eq!(declined, 12);
}
