// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL negatives for the STORE-OVER-STORE schema.
//!
//! Every semantic negative NAMES a falsifying assignment and CHECKS it with the
//! INDEPENDENT bounded array model, so "declined" is backed by a countermodel
//! rather than by the producer's own opinion. Each one is then run past the
//! minter, the checker's own recognizer, and the UNTOUCHED strict checker.
//!
//! GUARD MUTATION LEDGER — 14 mutations, **12 RED, 2 honest negatives**.
//! Each guard was deleted or weakened, the whole `array_store_overwrite` suite
//! run, and the guard restored. `(J)` is the checker sub-schema
//! `matches_exact_same_index_store_overwrite`; `mint` is
//! `mint_store_overwrite_axiom`; `walk` is `plan_store_overwrite_instances`.
//!
//! | # | mutation | result |
//! |---|---|---|
//! | 1 | (J): `outer_index == inner_index` dropped | **RED** `a_fold_at_a_different_index_is_refused`, `an_inner_write_at_a_different_index_is_refused` |
//! | 2 | (J): `outer_index == folded_index` dropped | **RED** `a_folded_side_written_at_a_different_index_is_refused` (RE-AIMED, see below) |
//! | 3 | (J): `outer_value == folded_value` dropped | **RED** `a_different_written_value_is_refused` |
//! | 4 | (J): `inner_base == folded_base` dropped | **RED** `a_different_base_array_is_refused` |
//! | 5 | (J): `literals.len() != 1` relaxed to `is_empty()` | **RED** `a_two_literal_clause_is_refused` |
//! | 6 | (J): the FOLDED side's `well_sorted_store_parts` dropped | not separately expressible — it supplies three of the comparison's operands, so deleting it does not type-check. The property is pinned directly by `a_non_store_folded_side_is_refused` |
//! | 7 | (J): the INNER `well_sorted_store_parts` dropped (depth-one accepted) | **RED**, 9 tests |
//! | 8 | (J): `sort(overwrite) == sort(folded)` dropped | STILL PASSED — **unfalsifiable, and provably so**: the other parses already force `sort(overwrite) = sort(shadowed) = sort(inner_base) = sort(folded_base) = sort(folded)`. Defence in depth, kept |
//! | 9 | mint: the value-element-sort guard dropped AND the recognizer admission test dropped | **RED** `a_value_that_is_not_element_sorted_is_declined` |
//! | 10 | mint: `store` arity `!= 3` relaxed to `< 3`, AND the recognizer test dropped | **RED** `a_store_of_the_wrong_arity_is_declined` |
//! | 11 | mint: every sort relation of `well_sorted_store_parts` dropped AND the recognizer test dropped | **RED** `a_store_over_a_differently_sorted_base_is_declined`, `an_index_that_is_not_index_sorted_is_declined` |
//! | 12 | mint: the FOLDED side built over `shadowed` instead of its base | **RED**, 8 tests |
//! | 13 | walk: the `definition_index != at` break dropped | **RED** `a_definition_at_a_different_index_mints_nothing` |
//! | 14 | mint: the recognizer admission test dropped ALONE | STILL PASSED — the checker's own validator backstops it, and every accept in this file is re-checked by `check_proof_strict`. Pairing it with 9/10/11 is what makes each sort guard observably load-bearing |
//!
//! **Mutation 2's first fixture was VACUOUS and the failure is recorded rather
//! than hidden.** `a_fold_at_a_different_index_is_refused` moves the OUTER
//! write to a second index, which guard 1 already refuses, so it could never
//! observe guard 2. Re-aimed at a clause whose depth-two side is a genuine
//! same-index overwrite and whose FOLDED side writes elsewhere. The re-aimed
//! fixture ALSO carried an over-strong assertion (that the countermodel must
//! separate the shadowed value from the live one), which made it fail
//! unmutated for a reason unrelated to the guard — the enumerator's first
//! countermodel legitimately has `u == v` because the two sides already
//! disagree wherever the base array is non-constant. Both defects were found
//! by running the suite unfiltered, and mutation 2 was re-run against the
//! corrected fixture.

use super::mint_store_overwrite_axiom;
use crate::array_row_axiom::model::{
    array, array_sort, decidable, element, element_sort, eq, falsify, index, index_sort, small,
    store, Value,
};
use crate::quality::check_proof_strict;
use ay_core::{
    AletheRule, ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore,
    TheoryLemmaKind,
};

/// The refutation the CHECKER is asked to replay for a forged instance. A
/// schema the validator refuses can never reach `Ok`.
fn strict_checks(terms: &mut TermStore, equality: TermId) -> bool {
    let negated = terms.mk_not(equality);
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![equality],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    check_proof_strict(&proof, terms).is_ok()
}

/// Assert that `clause` is REFUTED by the independent model, returning the
/// witness so the caller can pin the assignment that separates the terms, and
/// that neither the recognizer nor the strict checker admits it.
fn refuted(terms: &mut TermStore, clause: TermId) -> Vec<(TermId, Value)> {
    assert!(
        decidable(terms, &[clause], &small()),
        "the model must DECIDE the clause: silence would not be evidence"
    );
    let witness = falsify(terms, &[clause], &small())
        .expect("the INDEPENDENT array model must refute this clause");
    assert_eq!(
        crate::recognize_array_theory_lemma(terms, &[clause]),
        None,
        "the checker's own recognizer must refuse a refutable clause"
    );
    assert!(
        !strict_checks(terms, clause),
        "the UNTOUCHED strict checker must refuse a refutable clause"
    );
    witness
}

fn bound(witness: &[(TermId, Value)], term: TermId) -> Value {
    witness
        .iter()
        .find(|(id, _)| *id == term)
        .map(|(_, value)| value.clone())
        .expect("every atom of the clause is bound by the witness")
}

#[test]
fn a_fold_at_a_different_index_is_refused() {
    // `(= (store (store a i u) j v) (store a j v))` — the outer write and the
    // fold use DIFFERENT indices. FALSIFYING ASSIGNMENT: a = [0, 0], i = 0,
    // j = 1, u = 1, v = 0. LHS = store([1,0], 1, 0) = [1,0]; RHS = [0,0].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, other, value);
    let folded = store(&mut terms, base, other, value);
    let forged = eq(&mut terms, overwrite, folded);
    let witness = refuted(&mut terms, forged);
    assert_ne!(
        bound(&witness, at),
        bound(&witness, other),
        "the witness must separate the two index terms"
    );
    // The minter cannot build it: the folded side always writes at the OUTER
    // store's own index term.
    let minted = mint_store_overwrite_axiom(&mut terms, shadowed, value)
        .expect("the SAME-index instance is the one the minter produces");
    assert_ne!(minted, forged);
    assert_eq!(
        crate::format_term_alethe(&terms, minted),
        "(= (store (store a i u) i v) (store a i v))"
    );
}

#[test]
fn an_inner_write_at_a_different_index_is_refused() {
    // `(= (store (store a j u) i v) (store a i v))` — the SHADOWED write is at
    // a different index, so it is not shadowed at all. FALSIFYING ASSIGNMENT:
    // a = [0, 0], j = 1, i = 0, u = 1, v = 0.
    // LHS = store(store([0,0],1,1), 0, 0) = [0,1]; RHS = store([0,0],0,0) = [0,0].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, other, shadowed_value);
    let overwrite = store(&mut terms, shadowed, at, value);
    let folded = store(&mut terms, base, at, value);
    let forged = eq(&mut terms, overwrite, folded);
    let witness = refuted(&mut terms, forged);
    assert_ne!(
        bound(&witness, at),
        bound(&witness, other),
        "the witness must separate the two index terms"
    );
}

#[test]
fn a_folded_side_written_at_a_different_index_is_refused() {
    // `(= (store (store a i u) i v) (store a j v))` — the depth-two side is a
    // genuine same-index overwrite, but the FOLDED side writes at a different
    // index. RE-AIMED: the earlier different-index fixture moved the OUTER
    // write, which the inner-index guard already refuses, so it could not
    // observe this guard at all. FALSIFYING ASSIGNMENT: a = [0, 0], i = 0,
    // j = 1, u = 0, v = 1. LHS = store(store([0,0],0,0),0,1) = [1,0];
    // RHS = store([0,0],1,1) = [0,1].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, at, value);
    let folded = store(&mut terms, base, other, value);
    let forged = eq(&mut terms, overwrite, folded);
    let witness = refuted(&mut terms, forged);
    assert_ne!(
        bound(&witness, at),
        bound(&witness, other),
        "the witness must separate the two index terms"
    );
    // The shadowed value is deliberately NOT asserted to differ from the live
    // one: with `i != j` the two sides already disagree wherever the BASE array
    // is non-constant, so the enumerator's first countermodel legitimately has
    // `u == v`. Asserting otherwise made this fixture fail for a reason that
    // had nothing to do with the guard it aims at.
}

#[test]
fn a_different_written_value_is_refused() {
    // `(= (store (store a i u) i v) (store a i w))` with `v != w`.
    // FALSIFYING ASSIGNMENT: a = [0, 0], i = 0, u = 0, v = 1, w = 0.
    // LHS = [1,0]; RHS = [0,0].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let other_value = element(&mut terms, "w");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, at, value);
    let folded = store(&mut terms, base, at, other_value);
    let forged = eq(&mut terms, overwrite, folded);
    let witness = refuted(&mut terms, forged);
    assert_ne!(
        bound(&witness, value),
        bound(&witness, other_value),
        "the witness must separate the two written values"
    );
}

#[test]
fn a_different_base_array_is_refused() {
    // `(= (store (store a i u) i v) (store b i v))` with `a != b`.
    // FALSIFYING ASSIGNMENT: a = [0, 0], b = [0, 1], i = 0, u = 0, v = 0.
    // LHS = [0,0]; RHS = [0,1].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let other_base = array(&mut terms, "b");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, at, value);
    let folded = store(&mut terms, other_base, at, value);
    let forged = eq(&mut terms, overwrite, folded);
    let witness = refuted(&mut terms, forged);
    assert_ne!(
        bound(&witness, base),
        bound(&witness, other_base),
        "the witness must separate the two base arrays"
    );
}

#[test]
fn unguarded_store_commutativity_is_refused() {
    // `(= (store (store a i u) j v) (store (store a j v) i u))` is store
    // COMMUTATIVITY, which is only valid when `i` and `j` are distinct — the
    // permutation schema demands one index-equality literal per pair, and this
    // sub-schema must never admit it silently. FALSIFYING ASSIGNMENT:
    // a = [0, 0], i = j = 0, u = 0, v = 1. LHS = [1,0]; RHS = [0,0].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let left_inner = store(&mut terms, base, at, shadowed_value);
    let left = store(&mut terms, left_inner, other, value);
    let right_inner = store(&mut terms, base, other, value);
    let right = store(&mut terms, right_inner, at, shadowed_value);
    let forged = eq(&mut terms, left, right);
    let witness = refuted(&mut terms, forged);
    assert_eq!(
        bound(&witness, at),
        bound(&witness, other),
        "the witness must COLLIDE the two indices — that is what makes \
         unguarded commutativity false"
    );
    assert_ne!(
        bound(&witness, shadowed_value),
        bound(&witness, value),
        "the witness must separate the two written values"
    );
}

#[test]
fn a_depth_one_left_side_is_refused() {
    // `(= (store a i v) (store a i v))` is reflexive and never minted; the
    // interesting refusal is `(= (store a i v) (store b i v))`, which has no
    // depth-two side at all. FALSIFYING ASSIGNMENT: a = [0,0], b = [0,1],
    // i = 0, v = 0.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let other_base = array(&mut terms, "b");
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    let left = store(&mut terms, base, at, value);
    let right = store(&mut terms, other_base, at, value);
    let forged = eq(&mut terms, left, right);
    let witness = refuted(&mut terms, forged);
    assert_ne!(bound(&witness, base), bound(&witness, other_base));
}

#[test]
fn a_non_store_folded_side_is_refused() {
    // `(= (store (store a i u) i v) b)` — the folded side is a bare array.
    // FALSIFYING ASSIGNMENT: a = [0,0], b = [0,0], i = 0, u = 0, v = 1.
    // LHS = [1,0]; RHS = [0,0].
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let bare = array(&mut terms, "b");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, at, value);
    let forged = eq(&mut terms, overwrite, bare);
    refuted(&mut terms, forged);
}

#[test]
fn a_two_literal_clause_is_refused() {
    // The valid unit, padded with a second literal. The schema is exactly one
    // literal: a padded clause is a WEAKER claim the row-chain validator has no
    // sub-schema for, and admitting it would let a producer smuggle an
    // arbitrary literal into a certified leaf.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let equality =
        mint_store_overwrite_axiom(&mut terms, shadowed, value).expect("the unit must mint");
    let other = index(&mut terms, "j");
    let pad = terms.mk_app(Symbol::named("="), vec![at, other], Sort::Bool);
    assert_eq!(
        crate::recognize_array_theory_lemma(&terms, &[equality, pad]),
        None,
        "a padded clause is not the one-literal schema"
    );
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![equality, pad],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    assert!(check_proof_strict(&proof, &terms).is_err());
}

#[test]
fn a_store_of_the_wrong_arity_is_declined() {
    // A four-operand `store` is not an array operation at all. Built RAW,
    // because the sort-checked builder would refuse to construct it.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let quaternary = terms.mk_app(
        Symbol::named("store"),
        vec![base, at, shadowed_value, value],
        array_sort(),
    );
    assert!(mint_store_overwrite_axiom(&mut terms, quaternary, value).is_none());
    let binary = terms.mk_app(Symbol::named("store"), vec![base, at], array_sort());
    assert!(mint_store_overwrite_axiom(&mut terms, binary, value).is_none());
}

#[test]
fn a_value_that_is_not_element_sorted_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    // An INDEX-sorted value cannot be written into an element cell.
    assert!(mint_store_overwrite_axiom(&mut terms, shadowed, at).is_none());
}

#[test]
fn a_store_over_a_differently_sorted_base_is_declined() {
    // The base array's INDEX sort disagrees with the application's. Built RAW
    // for the same reason as the arity case.
    let mut terms = TermStore::new();
    let foreign_sort = Sort::Array(Box::new(ArraySort::new(
        Sort::Uninterpreted("Other".to_string()),
        element_sort(),
    )));
    let foreign_base = terms.mk_var("foreign", foreign_sort);
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let mismatched = terms.mk_app(
        Symbol::named("store"),
        vec![foreign_base, at, shadowed_value],
        array_sort(),
    );
    assert!(mint_store_overwrite_axiom(&mut terms, mismatched, value).is_none());
    // And the forged clause is refused by the checker even if a producer
    // builds it by hand.
    let overwrite = terms.mk_app(
        Symbol::named("store"),
        vec![mismatched, at, value],
        array_sort(),
    );
    let folded = terms.mk_app(
        Symbol::named("store"),
        vec![foreign_base, at, value],
        array_sort(),
    );
    let forged = terms.mk_app(Symbol::named("="), vec![overwrite, folded], Sort::Bool);
    assert_eq!(crate::recognize_array_theory_lemma(&terms, &[forged]), None);
    assert!(!strict_checks(&mut terms, forged));
}

#[test]
fn an_index_that_is_not_index_sorted_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let value = element(&mut terms, "v");
    let element_index = element(&mut terms, "e");
    let mismatched = terms.mk_app(
        Symbol::named("store"),
        vec![base, element_index, value],
        array_sort(),
    );
    assert!(mint_store_overwrite_axiom(&mut terms, mismatched, value).is_none());
    let _ = index_sort();
}

#[test]
fn a_non_store_term_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let value = element(&mut terms, "v");
    assert!(mint_store_overwrite_axiom(&mut terms, base, value).is_none());
}
