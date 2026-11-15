// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Parsed-declaration controls for lazy exact-carrier model decoding.

#![cfg(test)]
#![allow(clippy::unwrap_used)]

use ay_core::Sort;
use ay_frontend::{parse, sexp::parse_sexp, Context};

use super::super::{Decoder, ModelValue};

fn process(context: &mut Context, text: &str) {
    for command in parse(text).unwrap() {
        context.process_command(&command).unwrap();
    }
}

fn context(text: &str) -> Context {
    let mut context = Context::new();
    process(&mut context, text);
    context
}

fn decode(context: &Context, text: &str, sort: &Sort) -> Option<ModelValue> {
    Decoder::with_context(context).decode(&parse_sexp(text).unwrap(), sort)
}

fn core(context: &Context, name: &str) -> Sort {
    context.sort_definition(name).unwrap().clone()
}

fn carrier(sort: &Sort) -> &str {
    let Sort::Uninterpreted(carrier) = sort else {
        panic!("parsed datatype must retain a nominal engine carrier");
    };
    carrier
}

fn constructor(context: &Context, sort: &Sort, surface: &str) -> String {
    let identity = context
        .datatype_constructors(carrier(sort))
        .unwrap()
        .iter()
        .find(|identity| context.dt_surface_name(identity).unwrap_or(identity) == surface)
        .unwrap();
    context.output_symbol_name(identity).to_owned()
}

fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

fn record(constructor: &str, args: Vec<ModelValue>) -> ModelValue {
    ModelValue::Datatype {
        constructor: constructor.to_owned(),
        args,
    }
}

#[test]
fn parsed_record_metadata_decodes_arrays_without_builder_sort_sidecars() {
    let context = context(
        "(declare-datatype Row ((row (len (_ BitVec 64))
            (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))",
    );
    let sort = core(&context, "Outer");
    let text = "(outer (store ((as const (Array (_ BitVec 64) Row))
                  (row (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
                (_ bv33 64)
                (row (_ bv65 64) (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
                                       (_ bv64 64) #x09))))";
    let array = |default, stores| ModelValue::Array {
        default: Box::new(default),
        stores,
    };
    let empty = record("row", vec![word(0, 64), array(word(0, 8), vec![])]);
    let row = record(
        "row",
        vec![
            word(65, 64),
            array(word(7, 8), vec![(word(64, 64), word(9, 8))]),
        ],
    );
    assert_eq!(
        decode(&context, text, &sort),
        Some(record(
            "outer",
            vec![array(empty, vec![(word(33, 64), row)])]
        )),
    );
    assert_eq!(
        decode(&context, &text.replace("#x09", "#x0009"), &sort),
        None
    );
}

#[test]
fn overloaded_surface_constructor_is_selected_by_exact_requested_carrier() {
    for declarations in [
        "(declare-datatype A ((mk (field Bool))))
         (declare-datatype B ((mk (field (_ BitVec 8)))))",
        "(declare-datatype B ((mk (field (_ BitVec 8)))))
         (declare-datatype A ((mk (field Bool))))",
    ] {
        let context = context(declarations);
        let a = core(&context, "A");
        let b = core(&context, "B");
        assert_ne!(a, b);
        assert_eq!(constructor(&context, &a, "mk"), "mk");
        assert_eq!(constructor(&context, &b, "mk"), "mk");
        assert_eq!(
            decode(&context, "(mk true)", &a),
            Some(record("mk", vec![ModelValue::Bool(true)]))
        );
        assert_eq!(
            decode(&context, "(mk #x07)", &b),
            Some(record("mk", vec![word(7, 8)]))
        );
        assert_eq!(decode(&context, "(mk #x07)", &a), None);
        assert_eq!(decode(&context, "(mk true)", &b), None);
        assert_eq!(decode(&context, "((as mk B) true)", &a), None);
        assert_eq!(decode(&context, "((as mk A) #x07)", &b), None);
    }
}

#[test]
fn popped_record_carriers_keep_their_original_field_sorts_and_member_identity() {
    let mut context = context("(push 1)(declare-datatype R ((mkR (field Int))))");
    let old = core(&context, "R");
    process(
        &mut context,
        "(pop 1)(declare-datatype R ((mkR (field Bool))))",
    );
    let new = core(&context, "R");
    assert_ne!(old, new);
    let old_constructor = constructor(&context, &old, "mkR");
    let new_constructor = constructor(&context, &new, "mkR");
    assert_ne!(old_constructor, new_constructor);
    let old_value = format!("({old_constructor} 7)");
    let new_value = format!("({new_constructor} true)");
    assert_eq!(
        decode(&context, &old_value, &old),
        Some(record(&old_constructor, vec![ModelValue::Int(7.into())]))
    );
    assert_eq!(
        decode(&context, &new_value, &new),
        Some(record(&new_constructor, vec![ModelValue::Bool(true)]))
    );
    assert_eq!(decode(&context, &old_value, &new), None);
    assert_eq!(decode(&context, &new_value, &old), None);
    for (head, expected, wrong, argument) in [
        (&old_constructor, &old, &new, "7"),
        (&new_constructor, &new, &old, "true"),
    ] {
        let valid = format!("((as {head} {}) {argument})", carrier(expected));
        let crossed = format!("((as {head} {}) {argument})", carrier(wrong));
        assert!(decode(&context, &valid, expected).is_some());
        assert_eq!(decode(&context, &crossed, expected), None);
    }
}

#[test]
fn finite_recursive_constructor_values_and_array_fields_use_lazy_references() {
    let context = context(
        "(declare-datatype List ((nil) (cons (head (_ BitVec 8)) (tail List))))
         (declare-datatype Forest ((forest (trees (Array (_ BitVec 64) List)))))",
    );
    let list = core(&context, "List");
    let expected = record(
        "cons",
        vec![
            word(7, 8),
            record("cons", vec![word(9, 8), record("nil", vec![])]),
        ],
    );
    assert_eq!(
        decode(&context, "(cons #x07 (cons #x09 nil))", &list),
        Some(expected.clone())
    );
    let forest = core(&context, "Forest");
    assert_eq!(
        decode(
            &context,
            "(forest (store ((as const (Array (_ BitVec 64) List)) nil)
                                     (_ bv33 64) (cons #x07 (cons #x09 nil))))",
            &forest
        ),
        Some(record(
            "forest",
            vec![ModelValue::Array {
                default: Box::new(record("nil", vec![])),
                stores: vec![(word(33, 64), expected)],
            }]
        )),
    );
    for invalid in [
        "(cons #x07 true)",
        "(cons #x07 (as nil Forest))",
        "(cons #x07 (cons #x0009 nil))",
    ] {
        assert_eq!(decode(&context, invalid, &list), None, "{invalid}");
    }
    assert_eq!(decode(&context, "@List!0", &list), None);
}

#[test]
fn only_canonical_exact_carrier_abstract_atoms_are_uninterpreted_values() {
    let context = context("(declare-sort U 0)(declare-sort V 0)");
    let sort = core(&context, "U");
    for text in ["@U!0", "@U!12", "(as @U!12 U)"] {
        let atom = if text == "@U!0" { "@U!0" } else { "@U!12" };
        assert_eq!(
            decode(&context, text, &sort),
            Some(ModelValue::Uninterpreted(atom.into()))
        );
    }
    for invalid in [
        "@U!01",
        "@U!-1",
        "@V!0",
        "(as @U!0 V)",
        "(as @V!0 U)",
        "(f @U!0)",
        "opaque",
    ] {
        assert_eq!(decode(&context, invalid, &sort), None, "{invalid}");
    }
    assert_eq!(
        decode(
            &context,
            "@RoundingMode!0",
            &Sort::Uninterpreted("RoundingMode".into())
        ),
        None
    );
    let mut scoped = Context::new();
    process(&mut scoped, "(push 1)(declare-sort U 0)");
    let old = core(&scoped, "U");
    process(
        &mut scoped,
        "(pop 1)(declare-datatype U ((mkU (flag Bool))))",
    );
    let new = core(&scoped, "U");
    assert_ne!(old, new);
    let old_atom = format!("@{}!0", carrier(&old));
    assert_eq!(
        decode(&scoped, &old_atom, &old),
        Some(ModelValue::Uninterpreted(old_atom.clone()))
    );
    assert_eq!(decode(&scoped, "(mkU true)", &old), None);
    assert_eq!(decode(&scoped, &old_atom, &new), None);
    assert_eq!(
        decode(&scoped, "(mkU true)", &new),
        Some(record("mkU", vec![ModelValue::Bool(true)]))
    );
}

#[test]
fn parametric_carriers_remain_an_explicit_refusal() {
    let context = context(
        "(declare-datatypes ((Maybe 1)) ((par (T) ((none) (some (value T))))))
         (declare-const m (Maybe (_ BitVec 8)))",
    );
    let sort = context.symbol_sort("m").unwrap();
    assert!(context.is_parametric_datatype_instance(carrier(sort)));
    assert_eq!(decode(&context, "(some #x07)", sort), None);
    assert_eq!(decode(&context, "none", sort), None);
}

#[test]
fn registered_value_budget_refusals_are_sticky_but_not_global() {
    let context = context("(declare-datatype D ((done)))");
    let sort = core(&context, "D");
    let value = parse_sexp("done").unwrap();
    let mut work_limited = Decoder::with_context(&context);
    work_limited.work = 1;
    assert_eq!(work_limited.decode(&value, &sort), None);
    assert_eq!(
        work_limited.decode(&parse_sexp("true").unwrap(), &Sort::Bool),
        None
    );
    let mut copy_limited = Decoder::with_context(&context);
    copy_limited.bytes = 0;
    assert_eq!(copy_limited.decode(&value, &sort), None);
    assert_eq!(
        decode(&context, "done", &sort),
        Some(record("done", vec![]))
    );
}
