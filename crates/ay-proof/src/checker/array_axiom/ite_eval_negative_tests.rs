// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL negatives for `ArrayRowChain` sub-schema (K).
//!
//! Each one names a CONCRETE falsifying assignment in its own body and CHECKS
//! it: every literal of the clause is evaluated under that exact binding by the
//! INDEPENDENT bounded array model and asserted FALSE. The exhaustive
//! enumeration is then asked to agree, and the schema is asserted to DECLINE —
//! so a fixture cannot pass by being unfalsifiable, and a mutation cannot pass
//! by making the model silent.
//!
//! The alphabet is two indices and two elements, so `Value::Array(vec![a, b])`
//! is the array `[0 -> a, 1 -> b]`.

use super::ite_eval_fixture::*;
use super::recognize_array_row_chain_ite_eval;
use crate::array_row_axiom::model::{decidable, falsify, holds, Alphabet, Value};
use ay_core::{Sort, TermId, TermStore};

fn small() -> Alphabet {
    Alphabet {
        indices: 2,
        elements: 2,
    }
}

/// The whole bar for one negative: the schema DECLINES, the model can DECIDE
/// every literal, the NAMED assignment falsifies every literal, and the
/// exhaustive enumeration independently finds a countermodel too.
fn refuted(terms: &TermStore, clause: &[TermId], literals: &[TermId], named: &[(TermId, Value)]) {
    assert!(
        !recognize_array_row_chain_ite_eval(terms, clause),
        "sub-schema (K) accepted a REFUTABLE clause"
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

/// `E`, a const-array-rooted one-store chain over Bool, and the producer's own
/// value side — the exact corpus shape, ready to be perturbed.
struct Corpus {
    terms: TermStore,
    root: TermId,
    chain: TermId,
    base: TermId,
    write_index: TermId,
    read_index: TermId,
    value: TermId,
}

impl Corpus {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let falsity = terms.false_term();
        let truth = terms.true_term();
        let base = terms.mk_const_array(index_sort(), falsity);
        let write_index = terms.mk_var("i", index_sort());
        let read_index = terms.mk_var("j", index_sort());
        let root = terms.mk_var("E", array_sort(Sort::Bool));
        let chain = store(&mut terms, base, write_index, truth);
        let value = producer_value(&mut terms, chain, read_index);
        Self {
            terms,
            root,
            chain,
            base,
            write_index,
            read_index,
            value,
        }
    }

    /// `E := [0 -> a, 1 -> b]`, `i := 0`, `j := 0`.
    fn binding(&self, cells: Vec<usize>, write: usize, read: usize) -> Vec<(TermId, Value)> {
        vec![
            (self.root, Value::Array(cells)),
            (self.write_index, Value::Index(write)),
            (self.read_index, Value::Index(read)),
        ]
    }
}

#[test]
fn the_extensionality_direction_is_refutable_and_declined() {
    // `(or (= E C) (not (= (select E j) V)))` — the OTHER polarity, and the
    // one that occurs in `smt/chc_multi_pred_array` six times.
    //
    // FALSIFYING ASSIGNMENT: `C = store(const(false), 0, true) = [true, false]`,
    // `E = [true, true]`, `i = 0`, `j = 0`. Then `select(E, 0) = true` and
    // `V = (0 = 0) = true`, so the conclusion literal is TRUE and its negation
    // FALSE; and `E != C` because they differ at index 1, so the positive array
    // equality is FALSE too. The clause is FALSE.
    //
    // It is a theorem only when `j` is the Skolem extensionality WITNESS minted
    // for the pair — authority, not shape. `validate_array_extensionality`'s
    // `ExtDiffRegistry` is where that lives, and (K) must never claim it.
    let mut fixture = Corpus::new();
    let premise = eq(&mut fixture.terms, fixture.root, fixture.chain);
    let read = select(&mut fixture.terms, fixture.root, fixture.read_index);
    let conclusion_eq = eq(&mut fixture.terms, read, fixture.value);
    let conclusion = fixture.terms.mk_not(conclusion_eq);
    let literals = vec![premise, conclusion];
    let binding = fixture.binding(vec![1, 1], 0, 0);
    refuted(&fixture.terms, &literals, &literals, &binding);
}

#[test]
fn a_value_side_naming_the_wrong_stored_value_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: the chain writes `true` at `i`, the value side
    // claims `ite((= i j), false, false)` — i.e. `false` — so at `i = j = 0`,
    // `E = C = [true, false]` gives `select(E, 0) = true != false`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let condition = eq(&mut terms, i, j);
    let value = terms.mk_ite_raw(condition, falsity, falsity);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(0)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn a_guard_over_an_unrelated_index_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: the guard tests `(= k j)` for an index `k` the
    // chain never writes. With `i = 0`, `k = 1`, `j = 0`, `E = C = [true, false]`:
    // `select(E, 0) = true`, while the value side takes its ELSE branch
    // (`k != j`) and reads the const-array default `false`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let k = terms.mk_var("k", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let condition = eq(&mut terms, k, j);
    let value = terms.mk_ite_raw(condition, truth, falsity);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (k, Value::Index(1)),
        (j, Value::Index(0)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn a_const_base_with_the_wrong_default_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: the chain's base is `const(false)` but the value
    // side falls through to `true`. With `i = 0`, `j = 1`, `E = C = [true, false]`:
    // `select(E, 1) = false` and the value side is `true`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let condition = eq(&mut terms, i, j);
    let value = terms.mk_ite_raw(condition, truth, truth);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(1)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn an_else_branch_reading_a_different_index_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: the else branch reads the base at `k`, not `j`.
    // With a VARIABLE base `a = [true, false]`, `i = 0`, `j = 1`, `k = 0`,
    // `E = C = store(a, 0, true) = [true, false]`: `select(E, 1) = false`, but
    // the else branch yields `select(a, 0) = true`.
    let mut terms = TermStore::new();
    let base = terms.mk_var("a", array_sort(Sort::Bool));
    let truth = terms.true_term();
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let k = terms.mk_var("k", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let condition = eq(&mut terms, i, j);
    let wrong_read = select(&mut terms, base, k);
    let value = terms.mk_ite_raw(condition, truth, wrong_read);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (base, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(1)),
        (k, Value::Index(0)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn a_conclusion_reading_a_third_array_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: the read is of an array `D` the premise never
    // mentions. `D = [false, false]`, `E = C = [true, false]`, `i = j = 0`:
    // `select(D, 0) = false` while the value side is `true`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let other = terms.mk_var("D", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let value = producer_value(&mut terms, chain, j);
    let premise_eq = eq(&mut terms, root, chain);
    let premise = terms.mk_not(premise_eq);
    let read = select(&mut terms, other, j);
    let conclusion = eq(&mut terms, read, value);
    let literals = vec![premise, conclusion];
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (other, Value::Array(vec![0, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(0)),
    ];
    refuted(&terms, &literals, &literals, &binding);
}

#[test]
fn the_conclusion_alone_without_the_array_premise_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: with the premise deleted nothing ties `E` to the
    // chain. `E = [false, false]`, `i = j = 0`: `select(E, 0) = false` and the
    // value side is `true`.
    let mut fixture = Corpus::new();
    let read = select(&mut fixture.terms, fixture.root, fixture.read_index);
    let conclusion = eq(&mut fixture.terms, read, fixture.value);
    let literals = vec![conclusion];
    let binding = fixture.binding(vec![0, 0], 0, 0);
    refuted(&fixture.terms, &literals, &literals, &binding);
}

#[test]
fn a_positive_array_premise_with_a_positive_conclusion_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: `(or (= E C) (= (select E j) V))`. `E = [false, false]`,
    // `i = j = 0` gives `C = [true, false]`, so `E != C`, and
    // `select(E, 0) = false` while `V = true`.
    let mut fixture = Corpus::new();
    let premise = eq(&mut fixture.terms, fixture.root, fixture.chain);
    let read = select(&mut fixture.terms, fixture.root, fixture.read_index);
    let conclusion = eq(&mut fixture.terms, read, fixture.value);
    let literals = vec![premise, conclusion];
    let binding = fixture.binding(vec![0, 0], 0, 0);
    refuted(&fixture.terms, &literals, &literals, &binding);
}

#[test]
fn a_value_side_that_stops_short_of_the_chain_is_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: the chain has TWO writes and the value side only
    // accounts for the outer one, falling through to the const default.
    // `i1 = 1` (inner, writes `true`), `i2 = 0` (outer, writes `false`),
    // `j = 1`: `C = [false, true]`, `E = C`, `select(E, 1) = true`, while the
    // value side takes its else branch (`i2 != j`) and yields `false`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i1 = terms.mk_var("i1", index_sort());
    let i2 = terms.mk_var("i2", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let inner = store(&mut terms, base, i1, truth);
    let chain = store(&mut terms, inner, i2, falsity);
    let condition = eq(&mut terms, i2, j);
    let value = terms.mk_ite_raw(condition, falsity, falsity);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![0, 1])),
        (i1, Value::Index(1)),
        (i2, Value::Index(0)),
        (j, Value::Index(1)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn swapped_ite_branches_are_refutable_and_declined() {
    // FALSIFYING ASSIGNMENT: `ite((= i j), select(a, j), v)` has the branches
    // the wrong way round. `a = [false, false]`, `i = j = 0`, `v = true`:
    // `E = C = store(a, 0, true) = [true, false]`, `select(E, 0) = true`, and
    // the value side takes the THEN branch, yielding `select(a, 0) = false`.
    let mut terms = TermStore::new();
    let base = terms.mk_var("a", array_sort(Sort::Bool));
    let truth = terms.true_term();
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let condition = eq(&mut terms, i, j);
    let base_read = select(&mut terms, base, j);
    let value = terms.mk_ite_raw(condition, base_read, truth);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (base, Value::Array(vec![0, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(0)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn the_negated_fold_direction_names_the_wrong_stored_value_and_is_refutable() {
    // The `(ite c false true) = (not c)` decode arm, aimed the wrong way: the
    // chain writes `true` but the value side is `(not (= i j))`, which is the
    // evaluation of a chain that writes `false` over `const(true)`.
    //
    // FALSIFYING ASSIGNMENT: `i = j = 0`, `E = C = [true, false]`:
    // `select(E, 0) = true`, and `(not (= 0 0)) = false`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let condition = eq(&mut terms, i, j);
    let value = terms.mk_not(condition);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    let binding = vec![
        (root, Value::Array(vec![1, 0])),
        (i, Value::Index(0)),
        (j, Value::Index(0)),
    ];
    refuted(&terms, &clause, &literals, &binding);
}

#[test]
fn an_ill_sorted_store_is_declined() {
    // A raw `(store a i v)` whose VALUE operand is index-sorted. Nothing about
    // it is well-formed, so the array model cannot interpret it either — this
    // is a DECLINE assertion only, and it says so rather than reading the
    // model's silence as evidence.
    let mut terms = TermStore::new();
    let base = terms.mk_var("a", array_sort(element_sort()));
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(element_sort()));
    let v = terms.mk_var("v", element_sort());
    let malformed = store(&mut terms, base, i, i);
    let condition = eq(&mut terms, i, j);
    let base_read = select(&mut terms, base, j);
    let value = terms.mk_ite_raw(condition, v, base_read);
    let read = select(&mut terms, root, j);
    let premise_eq = eq(&mut terms, root, malformed);
    let premise = terms.mk_not(premise_eq);
    let conclusion = eq(&mut terms, read, value);
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &[premise, conclusion]),
        "a store whose value operand is not element-sorted must be declined"
    );
}

#[test]
fn a_depth_zero_chain_is_declined_and_belongs_to_the_congruence_sub_schema() {
    // `(or (not (= E A)) (= (select E j) (select A j)))` is VALID — it is plain
    // select congruence, sub-schema (D). (K) must still decline it: a ROW
    // sub-schema that accepted pure congruence would be claiming a step it does
    // not take. Asserted as a DECLINE that is NOT a refutation, and the sibling
    // schema is asserted to own it.
    let mut terms = TermStore::new();
    let other = terms.mk_var("A", array_sort(element_sort()));
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(element_sort()));
    let read = select(&mut terms, root, j);
    let other_read = select(&mut terms, other, j);
    let premise_eq = eq(&mut terms, root, other);
    let premise = terms.mk_not(premise_eq);
    let conclusion = eq(&mut terms, read, other_read);
    let literals = vec![premise, conclusion];
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &literals),
        "a depth-0 chain is congruence, not a ROW step, and (K) must decline it"
    );
    assert!(decidable(&terms, &literals, &small()));
    assert!(
        falsify(&terms, &literals, &small()).is_none(),
        "the declined clause is congruence and therefore valid"
    );
    assert_eq!(
        crate::recognize_array_theory_lemma(&terms, &literals),
        Some(ay_core::TheoryLemmaKind::ArrayRowChain),
        "sub-schema (D) already owns it"
    );
}

#[test]
fn a_three_literal_clause_is_declined() {
    // (K) is EXACT at two literals, like (C)-(J). A third literal — here a
    // spurious index equality — makes it decline rather than silently ignore
    // material the soundness argument never accounts for.
    let mut fixture = Corpus::new();
    let (clause, _) = assemble(
        &mut fixture.terms,
        fixture.root,
        fixture.chain,
        fixture.read_index,
        fixture.value,
        Spelling::plain(),
    );
    let extra = eq(&mut fixture.terms, fixture.write_index, fixture.read_index);
    let mut widened = clause.clone();
    widened.push(extra);
    assert!(
        recognize_array_row_chain_ite_eval(&fixture.terms, &clause),
        "the two-literal clause is the accepted baseline"
    );
    assert!(
        !recognize_array_row_chain_ite_eval(&fixture.terms, &widened),
        "a third literal must make sub-schema (K) decline"
    );
    // …and the base array is untouched by the widening, so nothing else moved.
    assert!(fixture.terms.get_const_array(fixture.base).is_some());
}
