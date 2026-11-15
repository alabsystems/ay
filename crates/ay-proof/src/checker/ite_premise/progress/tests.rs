// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod boundaries;
mod cancellation;

const C: TermId = TermId(0);
const T: TermId = TermId(1);
const E: TermId = TermId(2);
const X: TermId = TermId(3);
const ITE: AuthoredIte = (C, T, E);

fn entries() -> Vec<(TermData, Sort)> {
    ["c", "t", "e", "x"]
        .into_iter()
        .enumerate()
        .map(|(index, name)| (TermData::Var(name.into(), index as u32), Sort::Bool))
        .collect()
}

fn append(entries: &mut Vec<(TermData, Sort)>, data: TermData) -> TermId {
    let id = TermId(entries.len() as u32);
    entries.push((data, Sort::Bool));
    id
}

fn app(entries: &mut Vec<(TermData, Sort)>, name: &str, args: &[TermId]) -> TermId {
    append(entries, TermData::App(Symbol::named(name), args.to_vec()))
}

fn store(entries: Vec<(TermData, Sort)>) -> TermStore {
    TermStore::from_entries(entries, None, None, 0)
}

fn compare(terms: &TermStore, assumed: TermId, authored: &[AuthoredIte], expected: bool) {
    let old =
        super::super::legacy_assumed_is_authored_bool_ite_consequence(terms, assumed, authored);
    let new = assumed_is_authored_bool_ite_consequence_with_progress(
        terms,
        assumed,
        authored,
        &mut |_, _| true,
    );
    assert_eq!(old, expected, "legacy matcher for {assumed:?}");
    assert_eq!(new, Ok(expected), "metered matcher for {assumed:?}");
}

fn branches(entries: &mut Vec<(TermData, Sort)>) -> (TermId, TermId) {
    let not_c = append(entries, TermData::Not(C));
    let then_form = app(entries, "or", &[not_c, T]);
    let else_form = app(entries, "or", &[C, E]);
    (then_form, else_form)
}

#[test]
fn single_and_combined_forms_preserve_the_oracle() {
    let mut values = entries();
    let (then_form, else_form) = branches(&mut values);
    let combined = app(&mut values, "and", &[then_form, else_form]);
    let reversed = app(&mut values, "and", &[else_form, then_form]);
    let repeated = app(&mut values, "and", &[then_form, then_form]);
    let extra = app(&mut values, "or", &[C, E, X]);
    let terms = store(values);
    for assumed in [then_form, else_form, combined, reversed] {
        compare(&terms, assumed, &[ITE], true);
    }
    for assumed in [T, E, X, repeated, extra] {
        compare(&terms, assumed, &[ITE], false);
    }
    compare(&terms, then_form, &[], false);
    compare(&terms, then_form, &[(X, E, T), ITE], true);
}

#[test]
fn conjunctive_condition_is_flattened_only_once() {
    let mut values = entries();
    let cond = app(&mut values, "and", &[C, X]);
    let not_c = append(&mut values, TermData::Not(C));
    let not_x = append(&mut values, TermData::Not(X));
    let good = app(&mut values, "or", &[not_c, not_x, T]);
    let dropped = app(&mut values, "or", &[not_c, T]);
    let else_form = app(&mut values, "or", &[cond, E]);
    let nested = app(&mut values, "and", &[cond, X]);
    let not_cond = append(&mut values, TermData::Not(cond));
    let nested_good = app(&mut values, "or", &[not_cond, not_x, T]);
    let terms = store(values);
    compare(&terms, good, &[(cond, T, E)], true);
    compare(&terms, dropped, &[(cond, T, E)], false);
    compare(&terms, else_form, &[(cond, T, E)], true);
    compare(&terms, nested_good, &[(nested, T, E)], true);
    compare(&terms, good, &[(nested, T, E)], false);
}

#[test]
fn expected_duplicates_and_surplus_literals_keep_slot_then_set_semantics() {
    let mut values = entries();
    let not_c = append(&mut values, TermData::Not(C));
    let cond = app(&mut values, "and", &[C, C]);
    let branch = app(&mut values, "or", &[T, T]);
    let compact = app(&mut values, "or", &[not_c, T]);
    let surplus = app(&mut values, "or", &[not_c, T, T]);
    let twice = app(&mut values, "or", &[not_c, not_c]);
    let thrice = app(&mut values, "or", &[not_c, not_c, not_c]);
    let terms = store(values);
    compare(&terms, compact, &[(cond, branch, E)], true);
    compare(&terms, surplus, &[ITE], false);
    compare(&terms, not_c, &[(C, not_c, E)], true);
    compare(&terms, twice, &[(C, not_c, E)], true);
    compare(&terms, thrice, &[(C, not_c, E)], false);
}

#[test]
fn empty_connectives_and_combined_fallthrough_preserve_the_oracle() {
    let mut values = entries();
    let empty_or = app(&mut values, "or", &[]);
    let empty_and = app(&mut values, "and", &[]);
    let not_empty_and = append(&mut values, TermData::Not(empty_and));
    let combined = app(&mut values, "and", &[C, X]);
    let terms = store(values);
    compare(&terms, not_empty_and, &[(empty_and, empty_or, E)], true);
    compare(&terms, empty_or, &[(empty_and, empty_or, E)], false);
    compare(&terms, C, &[(C, T, empty_or)], true);
    compare(&terms, combined, &[(combined, T, empty_or)], true);
}

#[test]
fn indexed_connectives_remain_opaque() {
    let mut values = entries();
    let cond = append(
        &mut values,
        TermData::App(Symbol::indexed("and", vec![0]), vec![C, X]),
    );
    let branch = append(
        &mut values,
        TermData::App(Symbol::indexed("or", vec![0]), vec![T, E]),
    );
    let not_cond = append(&mut values, TermData::Not(cond));
    let accepted = app(&mut values, "or", &[not_cond, branch]);
    let expanded = app(&mut values, "or", &[not_cond, T, E]);
    let terms = store(values);
    compare(&terms, accepted, &[(cond, branch, X)], true);
    compare(&terms, expanded, &[(cond, branch, X)], false);
}

#[test]
fn only_the_legacy_then_sort_guard_is_applied() {
    let mut values = entries();
    let (then_form, else_form) = branches(&mut values);
    values[T.index()].1 = Sort::Int;
    let terms = store(values.clone());
    compare(&terms, then_form, &[ITE], false);
    compare(&terms, else_form, &[ITE], false);
    values[T.index()].1 = Sort::Bool;
    values[E.index()].1 = Sort::Int;
    compare(&store(values), else_form, &[ITE], true);
}
