// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL negatives for the read-over-write axiom minter.
//!
//! Every negative in this file names a CONCRETE falsifying assignment and
//! CHECKS it with the independent array-model evaluator in
//! `array_row_axiom_tests.rs`, then shows that the minter, the checker's own
//! recognizer, and the UNTOUCHED strict checker all refuse it. A negative that
//! only shows a decline would not distinguish "declined because it is unsound"
//! from "declined because the code happened not to build it".

use super::mint_row1_axiom;
use super::model::{
    array, array_sort, decidable, element, element_sort, eq, falsify, index, index_sort, select,
    small, store, strict_checks, Value,
};
use ay_core::{Symbol, TermStore};

/// Assert `clause` is REFUTED, print the assignment, and return it.
fn refuted(terms: &TermStore, clause: &[ay_core::TermId]) -> Vec<(ay_core::TermId, Value)> {
    assert!(
        decidable(terms, clause, &small()),
        "the array model could not interpret the clause, so a decline proves nothing"
    );
    falsify(terms, clause, &small()).expect("this clause is NOT valid and must be refuted")
}

/// 1. READ-OVER-WRITE AT A DIFFERENT INDEX — the instance that is only sound
///    when a disequality is available.
///
/// `(= (select (store a i v) j) v)` is refuted by
/// `a = [0, 0]`, `i = 0`, `j = 1`, `v = 1`: the read returns `a[1] = 0`, the
/// value side is `1`.
#[test]
fn a_read_over_write_at_a_different_index_is_refuted_and_never_minted() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let value = element(&mut terms, "v");
    let stored = store(&mut terms, base, at, value);
    let read = select(&mut terms, stored, other);
    let forged = eq(&mut terms, read, value);

    let witness = refuted(&terms, &[forged]);
    let bound = |term| {
        witness
            .iter()
            .find(|(id, _)| *id == term)
            .expect("bound")
            .1
            .clone()
    };
    assert_ne!(bound(at), bound(other), "the witness separates the indices");

    // The minter cannot produce it: the read index it builds IS the store's.
    let minted = mint_row1_axiom(&mut terms, stored).expect("the store itself yields an instance");
    assert_ne!(minted, forged);
    // The checker's own recognizer refuses it as the index-EQUAL schema.
    assert_ne!(
        crate::recognize_array_select_store(&terms, &[forged]),
        Some(true)
    );
    // And the untouched strict checker refuses the leaf outright.
    assert!(!strict_checks(&mut terms, forged));
}

/// 2. A STORE CHAIN WITH AN INDEX COLLISION — reading the chain at the shared
///    index returns the OUTER value, never the shadowed inner one.
///
/// `(= (select (store (store a i u) i v) i) u)` is refuted by `u = 0`, `v = 1`
/// (any array, any index): the read returns `v = 1`, the value side is `0`.
#[test]
fn a_shadowed_store_value_is_refuted_and_never_minted() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let inner = store(&mut terms, base, at, shadowed);
    let outer = store(&mut terms, inner, at, value);
    let read = select(&mut terms, outer, at);
    let forged = eq(&mut terms, read, shadowed);

    let witness = refuted(&terms, &[forged]);
    let bound = |term| {
        witness
            .iter()
            .find(|(id, _)| *id == term)
            .expect("bound")
            .1
            .clone()
    };
    assert_ne!(
        bound(shadowed),
        bound(value),
        "the witness separates the shadowed value from the live one"
    );

    // What the minter DOES produce for the outer store is the OUTER value, and
    // that instance is valid.
    let minted = mint_row1_axiom(&mut terms, outer).expect("the outer store yields an instance");
    assert_ne!(minted, forged);
    assert!(falsify(&terms, &[minted], &small()).is_none());
    assert!(strict_checks(&mut terms, minted));
    assert_ne!(
        crate::recognize_array_select_store(&terms, &[forged]),
        Some(true)
    );
    assert!(!strict_checks(&mut terms, forged));
}

/// 3. A MISMATCHED ARRAY SORT — a raw `store` application whose index operand
///    is element-sorted is not an array-theory operator at all, and the minter
///    must refuse it rather than mint a well-shaped lie.
#[test]
fn a_store_whose_operands_do_not_match_the_array_sort_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let wrong = element(&mut terms, "not_an_index");
    let value = element(&mut terms, "v");
    // Raw: the sort-checked builder would refuse this outright.
    let malformed = terms.mk_app(
        Symbol::named("store"),
        vec![base, wrong, value],
        array_sort(),
    );
    assert!(
        mint_row1_axiom(&mut terms, malformed).is_none(),
        "a store whose index operand is not index-sorted must be declined"
    );

    // The mirror case: the RESULT sort disagrees with the base array's, so the
    // application is not a store over `base` at all.
    let at = index(&mut terms, "i");
    let other_element = ay_core::Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort(),
        ay_core::Sort::Uninterpreted("Other".to_string()),
    )));
    let mismatched = terms.mk_app(Symbol::named("store"), vec![base, at, value], other_element);
    assert!(
        mint_row1_axiom(&mut terms, mismatched).is_none(),
        "a store whose result sort disagrees with its base must be declined"
    );
}

/// 4. AN UNENTAILED CONCLUSION — the value side is a DIFFERENT element term.
///
/// `(= (select (store a i v) i) w)` is refuted by `v = 0`, `w = 1`.
#[test]
fn a_read_over_write_against_the_wrong_value_is_refuted_and_never_minted() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    let other = element(&mut terms, "w");
    let stored = store(&mut terms, base, at, value);
    let read = select(&mut terms, stored, at);
    let forged = eq(&mut terms, read, other);

    let witness = refuted(&terms, &[forged]);
    let bound = |term| {
        witness
            .iter()
            .find(|(id, _)| *id == term)
            .expect("bound")
            .1
            .clone()
    };
    assert_ne!(
        bound(value),
        bound(other),
        "the witness separates the values"
    );

    let minted = mint_row1_axiom(&mut terms, stored).expect("the store yields its own instance");
    assert_ne!(minted, forged);
    assert_ne!(
        crate::recognize_array_select_store(&terms, &[forged]),
        Some(true)
    );
    assert!(!strict_checks(&mut terms, forged));
}

/// 5. A NON-STORE TERM — nothing to mint, and no guessing.
#[test]
fn a_non_store_term_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let read = select(&mut terms, base, at);
    assert!(mint_row1_axiom(&mut terms, base).is_none());
    assert!(mint_row1_axiom(&mut terms, read).is_none());
    assert!(mint_row1_axiom(&mut terms, at).is_none());
}

/// 6. A `store` APPLICATION OF THE WRONG ARITY is not the array operator —
///    in EITHER direction. The over-arity case is separate on purpose: a
///    `>= 3` arity test would accept a four-operand application whose extra
///    operand nothing ever looks at.
#[test]
fn a_store_of_the_wrong_arity_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    let extra = element(&mut terms, "extra");
    let over = terms.mk_app(
        Symbol::named("store"),
        vec![base, at, value, extra],
        array_sort(),
    );
    assert!(
        mint_row1_axiom(&mut terms, over).is_none(),
        "a four-operand `store` application is not the array operator"
    );
    let binary = terms.mk_app(Symbol::named("store"), vec![base, at], array_sort());
    assert!(mint_row1_axiom(&mut terms, binary).is_none());
}

/// 7. THE ELEMENT SORT IS RE-DERIVED, not assumed: a store whose VALUE operand
///    is not element-sorted is declined.
#[test]
fn a_store_whose_value_is_not_element_sorted_is_declined() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let wrong = terms.mk_var("wrong", index_sort());
    let malformed = terms.mk_app(Symbol::named("store"), vec![base, at, wrong], array_sort());
    assert!(mint_row1_axiom(&mut terms, malformed).is_none());
    let _ = element_sort();
}

/// 8. THE BASE ARRAY'S OWN SORT is re-derived: a raw `store` whose base array
///    has a DIFFERENT index sort from the application's result is not a store
///    over that base, and neither the minter nor the strict checker may treat
///    it as one.
#[test]
fn a_store_over_a_differently_sorted_base_is_declined() {
    let mut terms = TermStore::new();
    let other_index = ay_core::Sort::Uninterpreted("Index2".to_string());
    let other_base_sort = ay_core::Sort::Array(Box::new(ay_core::ArraySort::new(
        other_index,
        element_sort(),
    )));
    let base = terms.mk_var("a_other", other_base_sort);
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    // The RESULT sort is the ordinary one, so the index and value operands both
    // agree with it; only the BASE disagrees.
    let malformed = terms.mk_app(Symbol::named("store"), vec![base, at, value], array_sort());
    assert!(
        mint_row1_axiom(&mut terms, malformed).is_none(),
        "a store whose base array is differently sorted must be declined"
    );
    // And the checker refuses the leaf it would have produced, independently.
    let read = terms.mk_app(Symbol::named("select"), vec![malformed, at], element_sort());
    let forged = terms.mk_app(Symbol::named("="), vec![read, value], ay_core::Sort::Bool);
    assert_ne!(
        crate::recognize_array_select_store(&terms, &[forged]),
        Some(true)
    );
    assert!(!strict_checks(&mut terms, forged));
}
