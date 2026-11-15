// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use crate::expr::{Expr, ExprValue};
use crate::sort::Sort;
use std::sync::Arc;

fn pair_sort() -> Sort {
    Sort::struct_type("Pair", [("left", Sort::bv8()), ("right", Sort::bool())])
}

fn fields() -> Vec<Expr> {
    vec![Expr::bitvec_const(7, 8), Expr::true_()]
}

fn raw_constructor(datatype: &str, constructor: &str, args: Vec<Expr>, sort: Sort) -> Expr {
    Expr {
        sort,
        value: Arc::new(ExprValue::DatatypeConstructor {
            datatype_name: datatype.to_owned(),
            constructor_name: constructor.to_owned(),
            args,
        }),
    }
}

#[test]
fn constructor_requires_the_declared_datatype_and_a_known_constructor() {
    for (datatype, constructor, sort) in [
        ("Other", "Pair_mk", pair_sort()),
        ("Pair", "Other_mk", pair_sort()),
        ("Pair", "missing", pair_sort()),
        ("Pair", "Pair_mk", Sort::bool()),
        ("Pair", "Pair_mk", Sort::bv8()),
    ] {
        assert!(Expr::try_datatype_constructor(datatype, constructor, fields(), sort).is_err());
    }
}

#[test]
fn constructor_checks_exact_arity_and_every_field_including_unselected_siblings() {
    for args in [
        vec![],
        vec![Expr::bitvec_const(7, 8)],
        vec![Expr::bitvec_const(7, 8), Expr::true_(), Expr::false_()],
        vec![Expr::bitvec_const(7, 16), Expr::true_()],
        vec![Expr::true_(), Expr::true_()],
        vec![Expr::bitvec_const(7, 8), Expr::bitvec_const(1, 8)],
    ] {
        assert!(Expr::try_datatype_constructor("Pair", "Pair_mk", args, pair_sort()).is_err());
    }
}

#[test]
fn selector_checks_datatype_name_selector_name_and_requested_result_sort() {
    let value = Expr::var("p", pair_sort());
    for (datatype, selector, result_sort) in [
        ("Other", "left", Sort::bv8()),
        ("Pair", "missing", Sort::bv8()),
        ("Pair", "Pair_mk", Sort::bv8()),
        ("Pair", "left", Sort::bv16()),
        ("Pair", "left", Sort::bool()),
        ("Pair", "right", Sort::bv8()),
    ] {
        assert!(value
            .clone()
            .try_field_select(datatype, selector, result_sort)
            .is_err());
    }
    assert!(Expr::true_()
        .try_field_select("Pair", "left", Sort::bv8())
        .is_err());
}

#[test]
fn selector_and_tester_cannot_launder_a_malformed_raw_constructor() {
    let malformed = [
        raw_constructor("Other", "Pair_mk", fields(), pair_sort()),
        raw_constructor("Pair", "Other_mk", fields(), pair_sort()),
        raw_constructor("Pair", "Pair_mk", Vec::new(), pair_sort()),
        raw_constructor(
            "Pair",
            "Pair_mk",
            vec![Expr::bitvec_const(7, 8)],
            pair_sort(),
        ),
        raw_constructor(
            "Pair",
            "Pair_mk",
            vec![Expr::bitvec_const(7, 8), Expr::true_(), Expr::false_()],
            pair_sort(),
        ),
        raw_constructor(
            "Pair",
            "Pair_mk",
            vec![Expr::bitvec_const(7, 16), Expr::true_()],
            pair_sort(),
        ),
        // Selecting left must still reject the malformed, unselected right.
        raw_constructor(
            "Pair",
            "Pair_mk",
            vec![Expr::bitvec_const(7, 8), Expr::bitvec_const(1, 8)],
            pair_sort(),
        ),
    ];
    for value in malformed {
        assert!(value
            .clone()
            .try_field_select("Pair", "left", Sort::bv8())
            .is_err());
        assert!(value
            .clone()
            .try_field_select("Pair", "right", Sort::bool())
            .is_err());
        assert!(value.try_is_constructor("Pair", "Pair_mk").is_err());
    }
}

#[test]
fn tester_checks_both_names_and_the_subject_datatype() {
    let value = Expr::var("p", pair_sort());
    assert!(value
        .clone()
        .try_is_constructor("Other", "Pair_mk")
        .is_err());
    assert!(value.clone().try_is_constructor("Pair", "missing").is_err());
    assert!(value.try_is_constructor("Pair", "left").is_err());
    assert!(Expr::true_().try_is_constructor("Pair", "Pair_mk").is_err());
}

#[test]
fn valid_struct_construction_and_selector_folding_preserve_original_field_arcs() {
    let left = Expr::var("source_left", Sort::bv8());
    let right = Expr::var("source_right", Sort::bool());
    let value = Expr::try_datatype_constructor(
        "Pair",
        "Pair_mk",
        vec![left.clone(), right.clone()],
        pair_sort(),
    )
    .expect("well-typed constructor");
    let ExprValue::DatatypeConstructor {
        datatype_name,
        constructor_name,
        args,
    } = value.value()
    else {
        panic!("constructor retained")
    };
    assert_eq!(datatype_name, "Pair");
    assert_eq!(constructor_name, "Pair_mk");
    assert!(Arc::ptr_eq(&args[0].value, &left.value));
    assert!(Arc::ptr_eq(&args[1].value, &right.value));
    let selected = value
        .clone()
        .try_field_select("Pair", "left", Sort::bv8())
        .unwrap();
    assert!(Arc::ptr_eq(&selected.value, &left.value));
    assert_eq!(selected.sort(), left.sort());
    let selected = value
        .try_field_select("Pair", "right", Sort::bool())
        .unwrap();
    assert!(Arc::ptr_eq(&selected.value, &right.value));
}

fn assert_retained_selector(subject: &Expr, datatype: &str, name: &str, result_sort: Sort) {
    let selected = subject
        .clone()
        .try_field_select(datatype, name, result_sort.clone())
        .expect("declared enum selector remains a valid partial operation");
    assert_eq!(selected.sort(), &result_sort);
    let ExprValue::DatatypeSelector {
        datatype_name,
        selector_name,
        expr,
    } = selected.value()
    else {
        panic!("enum selector is not folded or distributed")
    };
    assert_eq!(datatype_name, datatype);
    assert_eq!(selector_name, name);
    assert!(Arc::ptr_eq(&expr.value, &subject.value));
}

#[test]
fn enum_selector_on_another_constructor_remains_partial_and_well_typed() {
    let sort = Sort::enum_type(
        "Maybe",
        vec![("Some", vec![("value", Sort::bv8())]), ("None", vec![])],
    );
    let some = Expr::try_datatype_constructor(
        "Maybe",
        "Some",
        vec![Expr::bitvec_const(7, 8)],
        sort.clone(),
    )
    .unwrap();
    let none = Expr::try_datatype_constructor("Maybe", "None", Vec::new(), sort.clone()).unwrap();
    let symbolic = Expr::var("maybe", sort.clone());
    for malformed in [
        raw_constructor("Maybe", "Some", vec![Expr::true_()], sort.clone()),
        raw_constructor("Maybe", "None", vec![Expr::bitvec_const(7, 8)], sort),
    ] {
        assert!(malformed
            .clone()
            .try_field_select("Maybe", "value", Sort::bv8())
            .is_err());
        assert!(malformed.try_is_constructor("Maybe", "None").is_err());
    }
    for subject in [&some, &none, &symbolic] {
        assert_retained_selector(subject, "Maybe", "value", Sort::bv8());
        let tester = subject.clone().try_is_constructor("Maybe", "Some").unwrap();
        let ExprValue::DatatypeTester {
            datatype_name,
            constructor_name,
            expr,
        } = tester.value()
        else {
            panic!("tester preserves the source subject")
        };
        assert_eq!(datatype_name, "Maybe");
        assert_eq!(constructor_name, "Some");
        assert!(tester.sort().is_bool());
        assert!(Arc::ptr_eq(&expr.value, &subject.value));
    }
    let choice = Expr::ite(Expr::var("pick", Sort::bool()), some, none);
    assert_retained_selector(&choice, "Maybe", "value", Sort::bv8());
}

#[test]
fn enum_selector_overloads_are_resolved_by_declared_result_sort_without_downcast() {
    let sort = Sort::enum_type(
        "Choice",
        vec![
            ("Byte", vec![("payload", Sort::bv8())]),
            ("Flag", vec![("payload", Sort::bool())]),
        ],
    );
    let byte = Expr::try_datatype_constructor(
        "Choice",
        "Byte",
        vec![Expr::bitvec_const(7, 8)],
        sort.clone(),
    )
    .unwrap();
    let flag = Expr::try_datatype_constructor("Choice", "Flag", vec![Expr::true_()], sort.clone())
        .unwrap();
    let symbolic = Expr::var("choice", sort);
    for subject in [&byte, &flag, &symbolic] {
        assert_retained_selector(subject, "Choice", "payload", Sort::bv8());
        assert_retained_selector(subject, "Choice", "payload", Sort::bool());
        assert!(subject
            .clone()
            .try_field_select("Choice", "payload", Sort::bv16())
            .is_err());
    }
}

#[test]
fn duplicate_constructor_or_same_constructor_selector_names_are_ambiguous() {
    let duplicate_constructor = Sort::enum_type(
        "Duplicate",
        vec![
            ("Make", vec![("field", Sort::bv8())]),
            ("Make", vec![("field", Sort::bool())]),
        ],
    );
    assert!(Expr::try_datatype_constructor(
        "Duplicate",
        "Make",
        vec![Expr::bitvec_const(7, 8)],
        duplicate_constructor.clone(),
    )
    .is_err());
    let subject = Expr::var("ambiguous", duplicate_constructor);
    assert!(subject
        .clone()
        .try_is_constructor("Duplicate", "Make")
        .is_err());
    assert!(subject
        .try_field_select("Duplicate", "field", Sort::bv8())
        .is_err());

    for sibling_sort in [Sort::bv8(), Sort::bool()] {
        let duplicate_selector = Sort::struct_type(
            "Duplicate",
            [("field", Sort::bv8()), ("field", sibling_sort.clone())],
        );
        let sibling = Expr::var("sibling", sibling_sort);
        assert!(Expr::try_datatype_constructor(
            "Duplicate",
            "Duplicate_mk",
            vec![Expr::bitvec_const(7, 8), sibling],
            duplicate_selector.clone(),
        )
        .is_err());
        assert!(Expr::var("ambiguous", duplicate_selector)
            .try_field_select("Duplicate", "field", Sort::bv8())
            .is_err());
    }
}
