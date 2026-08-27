// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Positive coverage for `ArrayRowChain` sub-schema (K), and the EXHAUSTIVE
//! sweep every accept is re-checked on.
//!
//! Every ACCEPT is re-checked THREE ways: by the INDEPENDENT bounded array-model
//! enumerator (`crate::array_row_axiom::model`), by the UNTOUCHED
//! `check_proof_strict` on the clause closed into a refutation, and by the
//! checker's own `recognize_array_theory_lemma`. Every DECLINE in the sweep is
//! recorded with the reason it is out of schema.
//!
//! `congruence_derivation_sweep_tests::falsifies` cannot serve here: it treats
//! `select`/`store` as UNINTERPRETED, under which read-over-write is not valid
//! at all and every accept would read as REFUTABLE.

use super::ite_eval_fixture::*;
use super::recognize_array_row_chain_ite_eval;
use crate::array_row_axiom::model::{decidable, falsify, Alphabet};
use ay_core::{Sort, TermId, TermStore};

/// Two indices and two elements, i.e. four array values — the same box the
/// sibling read-over-write sweeps use.
fn small() -> Alphabet {
    Alphabet {
        indices: 2,
        elements: 2,
    }
}

/// Every layer of the bar at once, for one accepted clause.
fn accept(terms: &mut TermStore, clause: &[TermId], literals: &[TermId]) {
    assert!(
        recognize_array_row_chain_ite_eval(terms, clause),
        "sub-schema (K) must accept this clause"
    );
    assert!(
        decidable(terms, literals, &small()),
        "the array model could not interpret the clause, so its silence is not evidence"
    );
    assert!(
        falsify(terms, literals, &small()).is_none(),
        "the INDEPENDENT array model falsified an ACCEPTED sub-schema (K) clause"
    );
    assert!(
        strict_checks(terms, clause),
        "the untouched strict checker refused an ACCEPTED sub-schema (K) clause"
    );
    assert_eq!(
        crate::recognize_array_theory_lemma(terms, clause),
        Some(ay_core::TheoryLemmaKind::ArrayRowChain),
        "an accepted clause must be recognized as the ArrayRowChain kind"
    );
}

#[test]
fn the_ordinary_builders_fold_the_nodes_this_schema_needs() {
    // Pinned, not asserted in prose: this is why every fixture builds raw.
    let mut terms = TermStore::new();
    let base = terms.mk_var("a", array_sort(element_sort()));
    let i = terms.mk_var("i", index_sort());
    let v = terms.mk_var("v", element_sort());
    let raw_store = store(&mut terms, base, i, v);
    assert_eq!(
        terms.mk_select(raw_store, i),
        v,
        "mk_select FOLDS the read-over-write this schema evaluates"
    );

    let bool_array = terms.mk_var("b", array_sort(Sort::Bool));
    let truth = terms.true_term();
    let falsity = terms.false_term();
    let bool_read = select(&mut terms, bool_array, i);
    assert_eq!(
        terms.mk_eq(bool_read, truth),
        bool_read,
        "mk_eq FOLDS `(= x true)` to `x`"
    );

    let condition = eq(&mut terms, i, i);
    let folded = terms.mk_ite(condition, truth, falsity);
    assert_eq!(
        folded, condition,
        "mk_ite FOLDS `(ite c true false)` to `c` — the fold decode arm exists \
         because of this"
    );
}

#[test]
fn a_one_store_chain_over_a_variable_base_certifies() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("E", array_sort(element_sort()));
    let base = terms.mk_var("a", array_sort(element_sort()));
    let i = terms.mk_var("i", index_sort());
    let v = terms.mk_var("v", element_sort());
    let j = terms.mk_var("j", index_sort());
    let chain = store(&mut terms, base, i, v);
    let value = producer_value(&mut terms, chain, j);
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    accept(&mut terms, &clause, &literals);
}

#[test]
fn the_corpus_shape_certifies_a_bool_element_chain_over_a_const_array() {
    // `smt/chc_multi_pred_array`, the whole measured population of this shape:
    //   (or (not (= A (store (const false) i true)))
    //       (= (select A j) (= i j)))
    // where the value side is `mk_ite(c, true, false)` FOLDED to `c` itself.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("A", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let value = producer_value(&mut terms, chain, j);
    assert!(
        matches!(terms.get(value), ay_core::TermData::App(ay_core::Symbol::Named(name), args)
            if name == "=" && args.len() == 2),
        "the producer's value side must be the FOLDED equality, not an `ite`"
    );
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    accept(&mut terms, &clause, &literals);
}

#[test]
fn the_corpus_shape_certifies_a_non_bool_chain_over_a_const_array() {
    // The same file's other array: `(Array _ (_ BitVec 8))`, whose value side
    // keeps a genuine `ite` because the element sort is not Bool.
    let mut terms = TermStore::new();
    let fill = terms.mk_var("fill", element_sort());
    let base = terms.mk_const_array(index_sort(), fill);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let v = terms.mk_var("v", element_sort());
    let root = terms.mk_var("A", array_sort(element_sort()));
    let chain = store(&mut terms, base, i, v);
    let value = producer_value(&mut terms, chain, j);
    assert!(
        matches!(terms.get(value), ay_core::TermData::Ite(..)),
        "a non-Bool element sort must leave a genuine `ite` node"
    );
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    accept(&mut terms, &clause, &literals);
}

#[test]
fn the_read_index_may_be_a_written_index() {
    // `entry_index == index`: the walk stops on the first entry and the value
    // side is the stored value itself, with no `ite` anywhere.
    let mut terms = TermStore::new();
    let root = terms.mk_var("E", array_sort(element_sort()));
    let base = terms.mk_var("a", array_sort(element_sort()));
    let i = terms.mk_var("i", index_sort());
    let v = terms.mk_var("v", element_sort());
    let chain = store(&mut terms, base, i, v);
    let value = producer_value(&mut terms, chain, i);
    assert_eq!(value, v, "reading at the written index is the stored value");
    let (clause, literals) = assemble(&mut terms, root, chain, i, value, Spelling::plain());
    accept(&mut terms, &clause, &literals);
}

#[test]
fn every_spelling_of_one_clause_is_accepted_identically() {
    for spelling in Spelling::all() {
        let mut terms = TermStore::new();
        let root = terms.mk_var("E", array_sort(element_sort()));
        let base = terms.mk_var("a", array_sort(element_sort()));
        let i = terms.mk_var("i", index_sort());
        let v = terms.mk_var("v", element_sort());
        let j = terms.mk_var("j", index_sort());
        let chain = store(&mut terms, base, i, v);
        let value = producer_value(&mut terms, chain, j);
        let (clause, literals) = assemble(&mut terms, root, chain, j, value, spelling);
        accept(&mut terms, &clause, &literals);
    }
}

/// EXHAUSTIVE two-sided sweep: every chain the producer can build over the box,
/// in every spelling.
///
/// The box deliberately CONTAINS refutable neighbours — the sibling negative
/// file builds them from the same fixtures and each is refuted with a named
/// assignment — so a sweep that accepted everything would be caught there.
#[test]
fn every_accept_over_the_producer_box_is_valid_in_the_independent_array_model() {
    let mut accepted = 0usize;
    let mut declined: Vec<String> = Vec::new();
    for element in [element_sort(), Sort::Bool] {
        for chain_len in 1usize..=3 {
            for const_base in [false, true] {
                for read_written in 0..=chain_len {
                    for spelling in Spelling::all() {
                        let mut terms = TermStore::new();
                        let arrays = array_sort(element.clone());
                        let root = terms.mk_var("E", arrays.clone());
                        let base = if const_base {
                            let fill = if element == Sort::Bool {
                                terms.false_term()
                            } else {
                                terms.mk_var("fill", element.clone())
                            };
                            terms.mk_const_array(index_sort(), fill)
                        } else {
                            terms.mk_var("a", arrays.clone())
                        };
                        let j = terms.mk_var("j", index_sort());
                        // `read_written == k > 0` makes the k-th write (counted
                        // innermost-first) land on the READ index.
                        let mut chain = base;
                        for k in 1..=chain_len {
                            let at = if k == read_written {
                                j
                            } else {
                                terms.mk_var(format!("i{k}"), index_sort())
                            };
                            let value = if element == Sort::Bool {
                                if k % 2 == 0 {
                                    terms.true_term()
                                } else {
                                    let falsity = terms.false_term();
                                    let truth = terms.true_term();
                                    if chain_len == 1 {
                                        truth
                                    } else {
                                        falsity
                                    }
                                }
                            } else {
                                terms.mk_var(format!("v{k}"), element.clone())
                            };
                            chain = store(&mut terms, chain, at, value);
                        }
                        let value = producer_value(&mut terms, chain, j);
                        let (clause, literals) =
                            assemble(&mut terms, root, chain, j, value, spelling);
                        if recognize_array_row_chain_ite_eval(&terms, &clause) {
                            accept(&mut terms, &clause, &literals);
                            accepted += 1;
                        } else {
                            declined.push(format!(
                                "element={element:?} len={chain_len} const_base={const_base} \
                                 read_written={read_written}"
                            ));
                        }
                    }
                }
            }
        }
    }
    // Pinned exactly: 36 chain configurations x 16 spellings = 576 clauses.
    assert_eq!(
        (accepted, declined.len()),
        (464, 112),
        "the sweep's accept/decline split moved"
    );
    // Two-sided: the DECLINES are the Bool chains of length >= 2 whose folded
    // value side is an `(or ..)`/`(and ..)` this schema deliberately does not
    // decode. Every one of them must be a Bool chain — a decline on a non-Bool
    // chain would mean the schema lost a shape it is supposed to accept.
    for reason in &declined {
        assert!(
            reason.contains("element=Bool"),
            "unexpected decline outside the undecoded Bool folds: {reason}"
        );
    }
}

#[test]
fn a_declined_bool_or_fold_is_a_decline_and_not_an_unsound_accept() {
    // The one shape this schema deliberately leaves on the table: a Bool
    // element chain of length 2 whose evaluation `mk_ite` rewrote to `(or c x)`.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i1 = terms.mk_var("i1", index_sort());
    let i2 = terms.mk_var("i2", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("A", array_sort(Sort::Bool));
    let inner = store(&mut terms, base, i1, truth);
    let chain = store(&mut terms, inner, i2, truth);
    let value = producer_value(&mut terms, chain, j);
    assert!(
        matches!(terms.get(value), ay_core::TermData::App(ay_core::Symbol::Named(name), _)
            if name == "or"),
        "mk_ite must have rewritten this evaluation into an `or`"
    );
    let (clause, literals) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &clause),
        "the `or` fold is deliberately not decoded and must DECLINE"
    );
    // …and the clause it declines really is VALID, so this is a completeness
    // gap and not a soundness one. Recorded so the next pass knows which it is.
    assert!(decidable(&terms, &literals, &small()));
    assert!(
        falsify(&terms, &literals, &small()).is_none(),
        "the declined clause is nevertheless valid — this is a completeness gap"
    );
}
