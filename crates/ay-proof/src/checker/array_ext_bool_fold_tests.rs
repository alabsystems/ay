// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The BOOL-ERASED witness read: `mk_ite`'s two propositional rewrites, inside
//! the folded array-extensionality schema.
//!
//! At element sort `Bool`, `mk_ite` does not leave an `Ite` node behind:
//!
//! ```text
//! (ite c true false) = c          (ite c false true) = (not c)
//! ```
//!
//! so the read of a `store` chain over `(Array _ Bool)` reaches the proof with
//! the branch constants ERASED. The corpus shape, from
//! `benchmarks/smt/chc_multi_pred_array.smt2`, is
//!
//! ```text
//! (or (= E (store (as const (Array (_ BitVec 32) Bool)) #x00000000 true))
//!     (not (= (select E k) (= #x00000000 k))))
//! ```
//!
//! **This clause is NOT a theorem** and this file proves that first, with a
//! named falsifying assignment CHECKED by the independent bounded array model.
//! It is sound only because `k` is the extensionality witness minted for
//! exactly that array pair — authority, not shape — so every accept here is an
//! accept of the FOLD (`V` really is `select(C, k)`), and the clause itself is
//! licensed only by `ExtDiffRegistry` provenance, which the negatives below
//! break one condition at a time.
//!
//! Every ACCEPT is re-checked by the INDEPENDENT evaluator in
//! `crate::array_row_axiom::model`, which shares no code with the recognizer:
//! it re-derives the McCarthy semantics from the term structure and enumerates
//! every assignment over a bounded alphabet.

use crate::array_row_axiom::model::{decidable, falsify, holds, Alphabet, Value};
use crate::checker::*;
use ay_core::{
    AletheRule, ArraySort, Proof, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};

fn index_sort() -> Sort {
    Sort::Uninterpreted("Index".to_string())
}

fn bool_array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(index_sort(), Sort::Bool)))
}

fn small() -> Alphabet {
    Alphabet {
        indices: 2,
        elements: 2,
    }
}

/// A RAW `(select a i)`: `mk_select` folds the very reads this schema is about.
fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    // A non-array base cannot occur in these fixtures; taking the term's own
    // sort as the result sort keeps the helper total instead of aborting.
    let element = match terms.sort(array).clone() {
        Sort::Array(sort) => sort.element_sort.clone(),
        other => other,
    };
    terms.mk_app(Symbol::named("select"), vec![array, index], element)
}

/// A RAW `(store a i v)`: `mk_store` collapses store-over-store.
fn store(terms: &mut TermStore, base: TermId, index: TermId, value: TermId) -> TermId {
    let sort = terms.sort(base).clone();
    terms.mk_app(Symbol::named("store"), vec![base, index, value], sort)
}

/// A RAW `(= a b)`: `mk_eq` folds Boolean equalities and distributes over `ite`.
fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// `(or (= a b) (not (= folded_a folded_b)))` — the single-literal `or` shape
/// the solver actually emits.
fn folded_ext_clause(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    folded_a: TermId,
    folded_b: TermId,
) -> TermId {
    let eq_ab = eq(terms, a, b);
    let folded_eq = eq(terms, folded_a, folded_b);
    let not_folded_eq = terms.mk_not(folded_eq);
    terms.mk_or(vec![eq_ab, not_folded_eq])
}

fn intro_step(witness: TermId, a: TermId, b: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: Vec::new(),
        premises: Vec::new(),
        args: vec![witness, a, b],
    }
}

fn ext_lemma_step(clause: TermId) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: vec![clause],
        farkas: None,
        kind: TheoryLemmaKind::ArrayExtensionality,
        lia: None,
    }
}

fn check_provenance(
    terms: &TermStore,
    steps: Vec<ProofStep>,
    problem: &[TermId],
) -> Result<(), ProofCheckError> {
    let proof = Proof::from_steps(steps);
    crate::validate_array_extensionality_provenance(&proof, terms, problem)
}

/// The EXACT corpus shape: `E`, a `(Array Index Bool)` variable; `C`, the
/// one-store chain `store(const(false), i, true)`; `k`, the witness; and the
/// producer's ERASED value side `(= i k)`.
struct Corpus {
    terms: TermStore,
    root: TermId,
    chain: TermId,
    write_index: TermId,
    witness: TermId,
    /// `(= i k)` — what `mk_ite(k = i, true, false)` collapses to.
    value: TermId,
    problem: Vec<TermId>,
}

impl Corpus {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let falsity = terms.false_term();
        let truth = terms.true_term();
        let base = terms.mk_const_array(index_sort(), falsity);
        let write_index = terms.mk_var("i", index_sort());
        let witness = terms.mk_var("__ay_ext_diff!21", index_sort());
        let root = terms.mk_var("E", bool_array_sort());
        let chain = store(&mut terms, base, write_index, truth);
        let value = eq(&mut terms, write_index, witness);
        let eq_ab = eq(&mut terms, root, chain);
        let problem = vec![terms.mk_not(eq_ab)];
        Self {
            terms,
            root,
            chain,
            write_index,
            witness,
            value,
            problem,
        }
    }

    /// The whole clause, in the shape the promotion sees.
    fn clause(&mut self) -> TermId {
        let read = select(&mut self.terms, self.root, self.witness);
        folded_ext_clause(&mut self.terms, self.root, self.chain, read, self.value)
    }

    /// `E := cells`, `i := write`, `k := read`.
    fn binding(&self, cells: Vec<usize>, write: usize, read: usize) -> Vec<(TermId, Value)> {
        vec![
            (self.root, Value::Array(cells)),
            (self.write_index, Value::Index(write)),
            (self.witness, Value::Index(read)),
        ]
    }
}

/// Assert, with the INDEPENDENT bounded array model, that `candidate` denotes
/// `select(array, index)` at EVERY assignment of the box — the exact claim the
/// fold recognizer makes when it accepts.
fn denotation_holds_everywhere(
    terms: &mut TermStore,
    array: TermId,
    index: TermId,
    candidate: TermId,
) {
    let read = select(terms, array, index);
    let identity = eq(terms, candidate, read);
    assert!(
        decidable(terms, &[identity], &small()),
        "the array model could not interpret the denotation, so its silence is not evidence"
    );
    assert!(
        falsify(terms, &[identity], &small()).is_none(),
        "the INDEPENDENT array model falsified an ACCEPTED fold's denotation"
    );
}

/// The whole bar for one negative: the recognizer DECLINES, the model can
/// DECIDE every literal, and the NAMED assignment falsifies every one of them —
/// so a fixture can never pass by being unfalsifiable.
fn refuted_and_declined(
    terms: &TermStore,
    clause: TermId,
    literals: &[TermId],
    array_a: TermId,
    array_b: TermId,
    witness: TermId,
    named: &[(TermId, Value)],
) {
    assert!(
        !recognize_folded_array_extensionality(terms, &[clause], array_a, array_b, witness),
        "the folded schema accepted a clause that is not the extensionality axiom for this pair"
    );
    assert!(
        decidable(terms, literals, &small()),
        "the array model could not interpret the clause, so its silence is not evidence"
    );
    for &literal in literals {
        assert_eq!(
            holds(terms, literal, named, &small()),
            Some(false),
            "the NAMED assignment must falsify every literal of the clause"
        );
    }
    assert!(
        falsify(terms, literals, &small()).is_some(),
        "the exhaustive enumeration must agree that the clause is refutable"
    );
}

// ============================================================================
// REPRODUCTION: the corpus leaf is NOT a theorem.
// ============================================================================

#[test]
fn the_corpus_extensionality_leaf_is_refutable_with_a_checked_countermodel() {
    // FALSIFYING ASSIGNMENT, checked below literal by literal:
    // `i = 0`, so `C = store(const(false), 0, true) = [true, false]`;
    // `E = [true, true]`; `k = 0`.
    // Then `select(E, 0) = true` and the value side `(0 = 0)` is `true`, so the
    // read equality HOLDS and its negation is FALSE; and `E != C` because they
    // differ at index 1, so the positive array equality is FALSE. Every literal
    // of the clause is FALSE, so the clause is FALSE.
    //
    // A step asserting it is therefore NOT a theorem, and no amount of
    // shape-checking can ever make it one: it is licensed only by the witness's
    // provenance.
    let mut f = Corpus::new();
    let premise = eq(&mut f.terms, f.root, f.chain);
    let read = select(&mut f.terms, f.root, f.witness);
    let conclusion_eq = eq(&mut f.terms, read, f.value);
    let conclusion = f.terms.mk_not(conclusion_eq);
    let literals = [premise, conclusion];
    let binding = f.binding(vec![1, 1], 0, 0);

    assert!(
        decidable(&f.terms, &literals, &small()),
        "the array model could not interpret the corpus leaf"
    );
    for &literal in &literals {
        assert_eq!(
            holds(&f.terms, literal, &binding, &small()),
            Some(false),
            "the NAMED assignment must falsify every literal of the corpus leaf"
        );
    }
    assert!(
        falsify(&f.terms, &literals, &small()).is_some(),
        "the exhaustive enumeration must agree that the corpus leaf is refutable"
    );
}

// ============================================================================
// POSITIVE: the erased fold is recognized, and its denotation re-checked.
// ============================================================================

#[test]
fn recognizes_the_bool_erased_then_branch_fold() {
    // `(ite (= i k) true false) = (= i k)`.
    let mut f = Corpus::new();
    let clause = f.clause();
    assert!(
        recognize_folded_array_extensionality(&f.terms, &[clause], f.root, f.chain, f.witness),
        "the corpus fold must be recognized"
    );
    denotation_holds_everywhere(&mut f.terms, f.chain, f.witness, f.value);
}

#[test]
fn recognizes_the_bool_erased_else_branch_fold() {
    // `(ite (= i k) false true) = (not (= i k))`, the mirror rewrite.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), truth);
    let i = terms.mk_var("i", index_sort());
    let k = terms.mk_var("__ay_ext_diff!7", index_sort());
    let root = terms.mk_var("E", bool_array_sort());
    let chain = store(&mut terms, base, i, falsity);
    let guard = eq(&mut terms, i, k);
    let value = terms.mk_not(guard);
    let read = select(&mut terms, root, k);
    let clause = folded_ext_clause(&mut terms, root, chain, read, value);
    assert!(
        recognize_folded_array_extensionality(&terms, &[clause], root, chain, k),
        "the mirror Bool fold must be recognized"
    );
    denotation_holds_everywhere(&mut terms, chain, k, value);
}

#[test]
fn the_corpus_leaf_certifies_with_a_matching_fresh_introduction() {
    let mut f = Corpus::new();
    let clause = f.clause();
    check_provenance(
        &f.terms,
        vec![
            intro_step(f.witness, f.root, f.chain),
            ext_lemma_step(clause),
        ],
        &f.problem,
    )
    .expect("the corpus leaf must certify once its witness is introduced");
}

#[test]
fn the_corpus_leaf_passes_the_untouched_strict_checker() {
    // The whole strict walk — the per-step theory-lemma dispatch as well as the
    // provenance pass — with the problem scope the gate uses. The refutation is
    // deliberately NOT closed by assuming the clause's negation: that
    // assumption mentions the witness, and a problem scope that mentions the
    // witness would (correctly) fail the freshness test.
    let mut f = Corpus::new();
    let clause = f.clause();
    let proof = Proof::from_steps(vec![
        intro_step(f.witness, f.root, f.chain),
        ext_lemma_step(clause),
    ]);
    // The refutation is deliberately NOT closed by assuming the clause's
    // negation: that assumption mentions the witness, and a problem scope that
    // mentions the witness would (correctly) fail the freshness test. So the
    // whole-proof walk validates every step and then complains only that the
    // LAST clause is not empty — which is exactly the acceptance being pinned.
    let error =
        crate::check_proof_strict_with_context(&proof, &f.terms, None, None, Some(&f.problem))
            .expect_err("an open proof cannot end in the empty clause");
    assert!(
        matches!(error, ProofCheckError::FinalClauseNotEmpty { .. }),
        "every STEP must validate; the only complaint may be the open end, got {error:?}"
    );
}

#[test]
fn the_untouched_strict_checker_refuses_a_forged_pair() {
    // The SAME clause, promoted with an introduction that names another array.
    // The strict checker refuses it, so a promotion this pass gets wrong is
    // rejected rather than believed.
    let mut f = Corpus::new();
    let clause = f.clause();
    let other = f.terms.mk_var("F", bool_array_sort());
    let proof = Proof::from_steps(vec![
        intro_step(f.witness, f.root, other),
        ext_lemma_step(clause),
    ]);
    let error =
        crate::check_proof_strict_with_context(&proof, &f.terms, None, None, Some(&f.problem))
            .expect_err("a forged array pair must be refused by the strict checker");
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { .. }),
        "the refusal must come from the LEMMA, not from the open end, got {error:?}"
    );
}

#[cfg(test)]
#[path = "array_ext_bool_fold_negative_tests.rs"]
mod negatives;
