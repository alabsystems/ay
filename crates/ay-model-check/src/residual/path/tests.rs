// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

mod mixed;
mod stores;

struct Empty;
impl ModelView for Empty {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn classifier<'a>(
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    evaluator: &'a Evaluator<'a>,
    resolve: &'a DtResolve<'a>,
) -> Classifier<'a> {
    Classifier {
        terms,
        model,
        ev: evaluator,
        resolve,
        aliases: Vec::new(),
        alias_eq_terms: Vec::new(),
        entries: Vec::new(),
        classify_work: 0,
        witness_value_work: 0,
    }
}

fn record(name: &str, field: &str, sort: Sort) -> Sort {
    Sort::Datatype(DatatypeSort::new(
        name,
        vec![DatatypeConstructor::new(
            format!("mk{name}"),
            vec![DatatypeField::new(field, sort)],
        )],
    ))
}

#[test]
fn successful_path_has_an_exact_shared_work_boundary_and_sticky_refusal() {
    let mut terms = TermStore::new();
    let inner = record("Inner", "value", Sort::Bool);
    let outer = record("Outer", "inner", inner.clone());
    let array = terms.mk_var("array", Sort::array(Sort::Int, outer.clone()));
    let index = terms.mk_int(0.into());
    let read = terms.mk_app(Symbol::named("select"), [array, index], outer);
    let middle = terms.mk_app(Symbol::named("inner"), [read], inner);
    let leaf = terms.mk_app(Symbol::named("value"), [middle], Sort::Bool);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let mut measured = classifier(&terms, &model, &evaluator, &resolve);
    let (_, _, slot) = measured.parse_free_read(leaf).expect("two exact selectors");
    assert!(matches!(slot, Slot::Path(path) if path == ["inner", "value"]));
    let cost = measured.classify_work;
    assert!((1..MAX_CLASSIFY_WORK).contains(&cost));
    let mut exact = classifier(&terms, &model, &evaluator, &resolve);
    exact.classify_work = MAX_CLASSIFY_WORK - cost;
    assert!(exact.parse_free_read(leaf).is_some());
    assert_eq!(exact.classify_work, MAX_CLASSIFY_WORK);
    let mut short = classifier(&terms, &model, &evaluator, &resolve);
    short.classify_work = MAX_CLASSIFY_WORK - cost + 1;
    assert!(short.parse_free_read(leaf).is_none());
    assert!(short.classify_work > MAX_CLASSIFY_WORK);
    assert!(short.parse_free_read(leaf).is_none());
    assert!(classifier(&terms, &model, &evaluator, &resolve)
        .parse_free_read(leaf)
        .is_some());
}

#[test]
fn malformed_or_oversized_metadata_is_not_a_negative_selector_census() {
    let mut terms = TermStore::new();
    let valid = record("Inner", "value", Sort::Bool);
    let enormous = record("Outer", &"x".repeat(MAX_CLASSIFY_WORK), valid);
    let receiver = terms.mk_var("receiver", enormous);
    let duplicate = Sort::Datatype(DatatypeSort::new(
        "Duplicate",
        vec![
            DatatypeConstructor::unit("same"),
            DatatypeConstructor::unit("same"),
        ],
    ));
    let malformed = terms.mk_var("malformed", duplicate);
    let ordinary = terms.mk_var("ordinary", Sort::Bool);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    assert!(classifier(&terms, &model, &evaluator, &resolve)
        .selector_shaped("value", receiver)
        .is_none());
    assert!(classifier(&terms, &model, &evaluator, &resolve)
        .selector_shaped("value", malformed)
        .is_none());
    assert_eq!(
        classifier(&terms, &model, &evaluator, &resolve).selector_shaped("value", ordinary),
        Some(false)
    );
}

#[test]
fn borrowed_schema_depth_refusal_precedes_any_owned_snapshot() {
    let mut sort = Sort::Bool;
    for _ in 0..=MAX_CLASSIFY_DEPTH {
        sort = Sort::array(Sort::Int, sort);
    }
    let mut work = 0usize;
    assert!(!metadata::sort_work(&sort, 0, &mut |n| {
        work += n;
        true
    }));
    assert!(work < 4 * MAX_CLASSIFY_DEPTH);
    assert!(metadata::sort_work(&Sort::Bool, 0, &mut |_| true));
}

#[test]
fn ordinary_selector_names_do_not_inherit_unsupported_theory_prefixes() {
    for name in ["bv_payload", "str.custom"] {
        let mut terms = TermStore::new();
        let sort = record("Named", name, Sort::Bool);
        let array = terms.mk_var("array", Sort::array(Sort::Int, sort.clone()));
        let index = terms.mk_int(0.into());
        let read = terms.mk_app(Symbol::named("select"), [array, index], sort);
        let leaf = terms.mk_app(Symbol::named(name), [read], Sort::Bool);
        let model = Empty;
        let evaluator = Evaluator::new(&terms, &model);
        let resolve = |_: &str| None;
        assert!(
            matches!(classifier(&terms, &model, &evaluator, &resolve).parse_free_read(leaf), Some((_, _, Slot::Field(field))) if field == name)
        );
    }
    for name in [
        "bvnot",
        "str.len",
        "fp.custom",
        "seq.custom",
        "default",
        "not",
    ] {
        assert!(reserved(name));
    }
}
