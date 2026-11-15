// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The select scan's else-value is the model's `(default a)` when it has one,
//! a base without one takes the value an unconditional definition passes
//! down (`definition_agreement_tests.rs` has the self-read that needs it), and
//! an unconditional definition whose built default still disputes the
//! model's `(default w)` stays withheld (`model_defaults.rs`,
//! `definition_order.rs`).

use super::tests::{array_of, bv, cell, define, extract, model};
use super::*;

#[test]
fn select_scan_takes_the_models_default() {
    for (default_value, expected) in [(Some(6u64), "#x06"), (None, "#x00")] {
        let mut terms = TermStore::new();
        let u = terms.mk_var("u", array_of(4, Sort::bitvec(8)));
        let three = bv(&mut terms, 3, 4);
        let read = terms.mk_select(u, three);
        let default_u = terms.mk_array_default(u);
        let mut values = vec![(read, 5)];
        values.extend(default_value.map(|value| (default_u, value)));

        let arrays = extract(&terms, &model(&values, &[]), &[]);

        assert_eq!(cell(&arrays, u, "#x3"), "#x05", "the read is unchanged");
        assert_eq!(cell(&arrays, u, "#x7"), expected, "{default_value:?}");
    }
}

#[test]
fn bool_select_scan_takes_the_models_default() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", array_of(4, Sort::Bool));
    let three = bv(&mut terms, 3, 4);
    let read = terms.mk_select(a, three);
    let default_a = terms.mk_array_default(a);

    let arrays = extract(
        &terms,
        &model(&[], &[(read, false), (default_a, true)]),
        &[],
    );

    assert_eq!(cell(&arrays, a, "#x3"), "false");
    assert_eq!(cell(&arrays, a, "#x7"), "true");
}

/// The top-level `w := (store u #xa (select w y))`, `y = 3`, `u[3] = w[3] =
/// 5`, and the model's `(default w)`.
fn self_read(
    terms: &mut TermStore,
    default_w: Option<u64>,
    default_u: Option<u64>,
) -> (ArrayModel, TermId, TermId) {
    let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
    let u = terms.mk_var("u", array_of(4, Sort::bitvec(8)));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let ten = bv(terms, 10, 4);
    let w_at_y = terms.mk_select(w, y);
    let u_at_y = terms.mk_select(u, y);
    let store = terms.mk_store(u, ten, w_at_y);
    let w_def = define(terms, w, store);
    let mut values = vec![(y, 3), (w_at_y, 5), (u_at_y, 5)];
    if let Some(value) = default_w {
        let term = terms.mk_array_default(w);
        values.push((term, value));
    }
    if let Some(value) = default_u {
        let term = terms.mk_array_default(u);
        values.push((term, value));
    }
    (extract(terms, &model(&values, &[]), &[w_def]), w, u)
}

/// `u`'s own `(default u)` disagrees with `(default w)`: the built default is
/// `u`'s, which model completion would refute, so `w` stays withheld.
#[test]
fn base_with_its_own_disputed_default_withholds_the_definition() {
    for (default_u, lifted) in [(5u64, true), (0, false)] {
        let mut terms = TermStore::new();
        let (arrays, w, _) = self_read(&mut terms, Some(5), Some(default_u));
        assert_eq!(
            !arrays.read_conflicted.contains(&w),
            lifted,
            "(default u) = {default_u}"
        );
    }
}

/// The same dispute withholds a definition that does not read its own
/// variable: `w := (store u #xa #x01)` at the top level.
#[test]
fn disputed_default_withholds_any_unconditional_definition() {
    for (default_u, lifted) in [(5u64, true), (0, false)] {
        let mut terms = TermStore::new();
        let w = terms.mk_var("w", array_of(4, Sort::bitvec(8)));
        let u = terms.mk_var("u", array_of(4, Sort::bitvec(8)));
        let ten = bv(&mut terms, 10, 4);
        let one = bv(&mut terms, 1, 8);
        let store = terms.mk_store(u, ten, one);
        let w_def = define(&mut terms, w, store);
        let default_w = terms.mk_array_default(w);
        let default_u_term = terms.mk_array_default(u);
        let values = [(default_w, 5), (default_u_term, default_u)];

        let arrays = extract(&terms, &model(&values, &[]), &[w_def]);

        assert_eq!(
            !arrays.read_conflicted.contains(&w),
            lifted,
            "(default u) = {default_u}"
        );
    }
}

/// Two definitions over one base offer it different values: it takes none.
#[test]
fn base_offered_two_defaults_takes_neither() {
    let mut terms = TermStore::new();
    let u = terms.mk_var("u", array_of(4, Sort::bitvec(8)));
    let mut assertions = Vec::new();
    let mut values = Vec::new();
    for (name, index, default_value) in [("w1", 1u64, 5u64), ("w2", 2, 6)] {
        let w = terms.mk_var(name, array_of(4, Sort::bitvec(8)));
        let at = bv(&mut terms, index, 4);
        let one = bv(&mut terms, 1, 8);
        let store = terms.mk_store(u, at, one);
        assertions.push(define(&mut terms, w, store));
        let default_w = terms.mk_array_default(w);
        values.push((default_w, default_value));
    }
    let three = bv(&mut terms, 3, 4);
    let read = terms.mk_select(u, three);
    values.push((read, 7));

    let hints = Executor::array_default_hints(&terms, &model(&values, &[]), &assertions);
    assert!(!hints.contains_key(&u), "{hints:?}");
    let arrays = extract(&terms, &model(&values, &[]), &assertions);
    assert_eq!(cell(&arrays, u, "#x9"), "#x00");
}

/// A `(default w)` value that does not fit its width renders no cell: no
/// built default matches it, so an unconditional definition stays withheld
/// (fail closed), and the scan does not publish it as an else-value.
#[test]
fn unrepresentable_model_default_withholds_and_is_not_published() {
    let mut terms = TermStore::new();
    let w = terms.mk_var("w", array_of(4, Sort::bitvec(3)));
    let u = terms.mk_var("u", array_of(4, Sort::bitvec(3)));
    let ten = bv(&mut terms, 10, 4);
    let one = bv(&mut terms, 1, 3);
    let store = terms.mk_store(u, ten, one);
    let w_def = define(&mut terms, w, store);
    let default_w = terms.mk_array_default(w);
    let three = bv(&mut terms, 3, 4);
    let read = terms.mk_select(u, three);

    let bv_model = model(&[(default_w, 9), (read, 2)], &[]);
    assert_eq!(Executor::model_array_default(&terms, &bv_model, w), None);
    assert_eq!(
        Executor::model_array_default_value(&terms, &bv_model, w),
        Some(None)
    );
    let arrays = extract(&terms, &bv_model, &[w_def]);
    assert!(arrays.read_conflicted.contains(&w));
    assert_eq!(cell(&arrays, u, "#x7"), "#b000");
}
