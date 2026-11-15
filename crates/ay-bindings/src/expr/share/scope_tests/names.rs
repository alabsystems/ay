// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::super::scope::reserved_names;
use super::*;

#[test]
fn unused_binders_and_function_position_symbols_are_reserved() {
    let term = large(boolean("b"));
    let quantified = Expr::forall(bind("ay_let_share_0"), term.clone().eq(term));
    assert!(reserved_names(&quantified, &[]).contains("ay_let_share_0"));
    let text = quantified.to_smtlib_shared();
    assert!(text.contains("(forall ((ay_let_share_0 Bool)"));
    assert!(text.contains("(let ((ay_let_share_1 "));
    assert!(!text.contains("(let ((ay_let_share_0 "));

    let applied = Expr::func_app("ay_let_share_0", vec![boolean("x")]);
    let term = large(boolean("b"));
    let source = term.clone().eq(term).and(applied);
    assert!(reserved_names(&source, &[]).contains("ay_let_share_0"));
    let text = source.to_smtlib_shared();
    assert!(text.contains("(ay_let_share_0 x)"));
    assert!(text.contains("(let ((ay_let_share_1 "));
    assert!(!text.contains("(let ((ay_let_share_0 "));
    assert!(matches!(
        oracle::assertion(&text),
        ay_frontend::Term::Let(..)
    ));
}

#[test]
fn datatype_terms_and_unused_sibling_metadata_reserve_all_names() {
    let datatype = Sort::enum_type(
        "ay_let_share_1",
        [
            ("ay_let_share_2", vec![("used", Sort::bool())]),
            (
                "ay_let_share_5",
                vec![("ay_let_share_3", Sort::uninterpreted("ay_let_share_4"))],
            ),
        ],
    );
    let value = Expr::try_datatype_constructor(
        "ay_let_share_1",
        "ay_let_share_2",
        vec![boolean("b")],
        datatype,
    )
    .unwrap();
    let selected = value
        .clone()
        .try_field_select("ay_let_share_1", "used", Sort::bool())
        .unwrap();
    let tested = value
        .try_is_constructor("ay_let_share_1", "ay_let_share_2")
        .unwrap();
    let names = reserved_names(&selected.and(tested), &[]);
    // Names 3, 4 and 5 occur only in the unused sibling declaration, not in
    // selected/tested term syntax. No constructor branch is discarded here.
    for ordinal in 1..=5 {
        assert!(names.contains(&format!("ay_let_share_{ordinal}")));
    }
    assert!(names.contains("used"));
    assert!(names.contains("b"));
}

#[test]
fn value_identity_does_not_hide_different_outer_sort_metadata() {
    let value = Arc::new(ExprValue::Var { name: "v".into() });
    let first = Expr {
        sort: Sort::uninterpreted("ay_let_share_0"),
        value: Arc::clone(&value),
    };
    let second = Expr {
        sort: Sort::uninterpreted("ay_let_share_1"),
        value,
    };
    assert!(Arc::ptr_eq(&first.value, &second.value));
    // Deliberately raw mixed-sort input to the name census only: no builder,
    // formatter or solver is asked to treat this as a well-typed formula.
    let source = Expr {
        sort: Sort::bool(),
        value: Arc::new(ExprValue::Distinct(vec![first, second])),
    };
    let names = reserved_names(&source, &[]);
    assert!(names.contains("ay_let_share_0"));
    assert!(names.contains("ay_let_share_1"));
    assert!(names.contains("v"));
}
