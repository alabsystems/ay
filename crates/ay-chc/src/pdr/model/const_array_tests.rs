// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};
use ay_frontend::{sexp::parse_sexps, SExpr};

fn constant(key: ChcSort, value: ChcExpr) -> ChcExpr {
    ChcExpr::ConstArray(key, Arc::new(value))
}

fn record(name: &str) -> ChcSort {
    ChcSort::Datatype {
        name: name.into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "mk cell".into(),
            selectors: vec![ChcDtSelector {
                name: "cell byte".into(),
                sort: ChcSort::BitVec(8),
            }],
        }]),
    }
}

fn elements(expr: &SExpr) -> &[SExpr] {
    match expr {
        SExpr::List(items) => items,
        _ => panic!("expected list: {expr:?}"),
    }
}

fn symbol(name: &str) -> SExpr {
    SExpr::Symbol(name.into())
}

fn assert_array_qualification(expression: &SExpr, key: &SExpr, cell: &SExpr) {
    let application = elements(expression);
    assert_eq!(application.len(), 2);
    let qualified = elements(&application[0]);
    assert_eq!(qualified.len(), 3);
    assert_eq!(qualified[0], symbol("as"));
    assert_eq!(qualified[1], symbol("const"));
    assert_eq!(
        elements(&qualified[2]),
        &[symbol("Array"), key.clone(), cell.clone()]
    );
}

#[test]
fn ordinary_constant_arrays_keep_exact_existing_smt_bytes() {
    for (key, value, expected) in [
        (
            ChcSort::BitVec(64),
            ChcExpr::BitVec(0, 8),
            "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv0 8))",
        ),
        (
            ChcSort::BitVec(1),
            ChcExpr::Bool(true),
            "((as const (Array (_ BitVec 1) Bool)) true)",
        ),
        (
            ChcSort::Bool,
            ChcExpr::Bool(false),
            "((as const (Array Bool Bool)) false)",
        ),
        (
            ChcSort::Int,
            ChcExpr::Int(-3),
            "((as const (Array Int Int)) (- 3))",
        ),
        (
            ChcSort::Real,
            ChcExpr::Real(-1, 2),
            "((as const (Array Real Real)) (/ (- 1) 2))",
        ),
    ] {
        assert_eq!(
            InvariantModel::expr_to_smtlib(&constant(key, value)),
            expected
        );
    }
}

#[test]
fn quoted_record_cell_sort_agrees_with_variable_and_constructor_spelling() {
    let cell = record("Cell value");
    let variable = ChcExpr::Var(ChcVar::new("fill value", cell.clone()));
    assert_eq!(
        InvariantModel::expr_to_smtlib(&constant(ChcSort::BitVec(8), variable)),
        "((as const (Array (_ BitVec 8) |Cell value|)) |fill value|)"
    );
    let constructor = ChcExpr::FuncApp(
        "mk cell".into(),
        cell,
        vec![Arc::new(ChcExpr::BitVec(7, 8))],
    );
    let text = InvariantModel::expr_to_smtlib(&constant(ChcSort::BitVec(8), constructor));
    assert_eq!(
        text,
        "((as const (Array (_ BitVec 8) |Cell value|)) ((as |mk cell| |Cell value|) (_ bv7 8)))"
    );
    let expressions = parse_sexps(&text).unwrap();
    let key = parse_sexps("(_ BitVec 8)").unwrap();
    assert_eq!(expressions.len(), 1);
    assert_array_qualification(&expressions[0], &key[0], &symbol("Cell value"));
}

#[test]
fn both_named_key_and_cell_sorts_are_single_quoted_symbols() {
    for key in [
        record("Index record"),
        ChcSort::Uninterpreted("Index record".into()),
    ] {
        let value = ChcExpr::Var(ChcVar::new(
            "default",
            ChcSort::Uninterpreted("Cell sort".into()),
        ));
        let text = InvariantModel::expr_to_smtlib(&constant(key, value));
        assert_eq!(
            text,
            "((as const (Array |Index record| |Cell sort|)) default)"
        );
        let expressions = parse_sexps(&text).unwrap();
        assert_array_qualification(
            &expressions[0],
            &symbol("Index record"),
            &symbol("Cell sort"),
        );
    }
}

#[test]
fn nested_constant_array_sorts_preserve_every_quoted_leaf() {
    let inner = constant(
        ChcSort::Uninterpreted("Column key".into()),
        ChcExpr::Var(ChcVar::new("fill", record("Cell value"))),
    );
    let outer = constant(ChcSort::BitVec(64), inner);
    let text = InvariantModel::expr_to_smtlib(&outer);
    assert_eq!(text,
        "((as const (Array (_ BitVec 64) (Array |Column key| |Cell value|))) ((as const (Array |Column key| |Cell value|)) fill))");
    let expressions = parse_sexps(&text).unwrap();
    let key = parse_sexps("(_ BitVec 64)").unwrap();
    let cell = SExpr::List(vec![
        symbol("Array"),
        symbol("Column key"),
        symbol("Cell value"),
    ]);
    assert_array_qualification(&expressions[0], &key[0], &cell);
    assert_array_qualification(
        &elements(&expressions[0])[1],
        &symbol("Column key"),
        &symbol("Cell value"),
    );
}

#[test]
fn exact_source_form_keeps_datatype_identity_and_constant_array_arity() {
    let value = ChcExpr::FuncApp(
        "mk cell".into(),
        record("Cell value"),
        vec![Arc::new(ChcExpr::BitVec(7, 8))],
    );
    let expression = InvariantModel::expr_to_smtlib(&constant(ChcSort::BitVec(64), value));
    // A source-shaped script is parsed only as syntax, not solved or admitted
    // through the currently narrower quantified-source type boundary.
    let source = format!(
        "(set-logic HORN)
         (declare-datatype |Cell value| ((|mk cell| (|cell byte| (_ BitVec 8)))))
         (declare-fun P ((Array (_ BitVec 64) |Cell value|)) Bool)
         (assert (P {expression}))
         (assert (forall ((a (Array (_ BitVec 64) |Cell value|))) (=> (P a) false)))
         (check-sat)"
    );
    let commands = parse_sexps(&source).unwrap();
    assert_eq!(commands.len(), 6);
    let declared = &elements(&commands[1])[1];
    assert_eq!(declared, &symbol("Cell value"));
    let predicate_signature = elements(&elements(&commands[2])[2]);
    let array_sort = &predicate_signature[0];
    let assertion = elements(&commands[3]);
    assert_eq!(assertion.len(), 2);
    assert_eq!(assertion[0], symbol("assert"));
    let predicate = elements(&assertion[1]);
    assert_eq!(predicate.len(), 2);
    assert_eq!(predicate[0], symbol("P"));
    let qualifier = elements(&elements(&predicate[1])[0]);
    assert_eq!(&qualifier[2], array_sort);
    assert_eq!(&elements(array_sort)[2], declared);
}
