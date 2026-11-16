// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored typed-decoder regressions; no solver or retained compiler output.

#![cfg(test)]
#![allow(clippy::unwrap_used)]

use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ay_frontend::SExpr;
use num_bigint::BigInt;

use super::{parse_typed_value, Decoder};
use crate::api::types::ModelValue;

fn sexp(text: &str) -> SExpr {
    let mut values = ay_frontend::sexp::parse_sexps(text).unwrap();
    assert_eq!(values.len(), 1, "fixture must contain exactly one value");
    values.pop().unwrap()
}

fn decode(text: &str, sort: &Sort) -> Option<ModelValue> {
    parse_typed_value(&sexp(text), sort)
}

fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: BigInt::from(value),
        width,
    }
}

fn array(default: ModelValue, stores: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Array {
        default: Box::new(default),
        stores,
    }
}

fn record(constructor: &str, args: Vec<ModelValue>) -> ModelValue {
    ModelValue::Datatype {
        constructor: constructor.to_owned(),
        args,
    }
}

fn record_sort(name: &str, constructor: &str, fields: Vec<(&str, Sort)>) -> Sort {
    Sort::Datatype(DatatypeSort::new(
        name,
        vec![DatatypeConstructor::new(
            constructor,
            fields
                .into_iter()
                .map(|(name, sort)| DatatypeField::new(name, sort))
                .collect(),
        )],
    ))
}

fn inner_sort() -> Sort {
    record_sort(
        "Inner",
        "mkInner",
        vec![
            ("len", Sort::bitvec(64)),
            ("data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
        ],
    )
}

#[test]
fn nested_record_cells_keep_typed_defaults_indexed_keys_and_store_order() {
    let sort = record_sort(
        "Outer",
        "mkOuter",
        vec![
            ("len", Sort::bitvec(64)),
            ("data", Sort::array(Sort::bitvec(64), inner_sort())),
        ],
    );
    let text = "(mkOuter (_ bv34 64)
        (store ((as const (Array (_ BitVec 64) Inner))
            (mkInner (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
          (_ bv33 64)
          (mkInner (_ bv65 64)
            (store (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
                     (_ bv64 64) #x09) (_ bv64 64) #x07))))";
    let empty = record("mkInner", vec![word(0, 64), array(word(0, 8), vec![])]);
    let row = record(
        "mkInner",
        vec![
            word(65, 64),
            array(
                word(7, 8),
                vec![(word(64, 64), word(9, 8)), (word(64, 64), word(7, 8))],
            ),
        ],
    );
    assert_eq!(
        decode(text, &sort),
        Some(record(
            "mkOuter",
            vec![word(34, 64), array(empty, vec![(word(33, 64), row)])],
        )),
    );
}

#[test]
fn arrays_of_arrays_preserve_nested_defaults_and_repeated_outer_stores() {
    let row = Sort::array(Sort::bitvec(64), Sort::Bool);
    let sort = Sort::array(Sort::bitvec(64), row);
    let text = "(store
        (store ((as const (Array (_ BitVec 64) (Array (_ BitVec 64) Bool)))
                  ((as const (Array (_ BitVec 64) Bool)) false))
          (_ bv3 64) (store ((as const (Array (_ BitVec 64) Bool)) false) (_ bv4 64) true))
        (_ bv3 64) ((as const (Array (_ BitVec 64) Bool)) true))";
    let default = array(ModelValue::Bool(false), vec![]);
    let first = array(
        ModelValue::Bool(false),
        vec![(word(4, 64), ModelValue::Bool(true))],
    );
    assert_eq!(
        decode(text, &sort),
        Some(array(
            default,
            vec![
                (word(3, 64), first),
                (word(3, 64), array(ModelValue::Bool(true), vec![])),
            ],
        )),
    );
}

#[test]
fn exact_bv_literals_preserve_width_and_high_limbs() {
    for text in ["#xff", "#b11111111", "(_ bv255 8)"] {
        assert_eq!(decode(text, &Sort::bitvec(8)), Some(word(255, 8)));
    }
    let high = (BigInt::from(1u8) << 128usize) + BigInt::from(7u8);
    let text = format!("(_ bv{high} 129)");
    assert_eq!(
        decode(&text, &Sort::bitvec(129)),
        Some(ModelValue::BitVec {
            value: high,
            width: 129,
        }),
    );
}

#[test]
fn malformed_bv_values_never_relabel_or_truncate() {
    for text in [
        "#x0100",
        "#b1",
        "(_ bv7 64)",
        "(_ bv256 8)",
        "(_ bv-1 8)",
        "(_ bv1 0)",
        "7",
        "true",
        "(_ bv7 8 extra)",
    ] {
        assert_eq!(decode(text, &Sort::bitvec(8)), None, "{text}");
    }
    assert_eq!(decode("(_ bv0 0)", &Sort::bitvec(0)), None);
}

#[test]
fn arrays_authenticate_const_ascription_keys_cells_and_complete_structure() {
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    for text in [
        "((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)",
        "((as const (Array (_ BitVec 64) Bool)) #x00)",
        "((as const Bool) #x00)",
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) true)",
        "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x01 #x02)",
        "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) (_ bv1 64) #x0100)",
        "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) (_ bv1 64))",
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00 #x01)",
        "((as const (Array (_ BitVec 64) (_ BitVec 8)) extra) #x00)",
    ] {
        assert_eq!(decode(text, &sort), None, "{text}");
    }
}

#[test]
fn opaque_arrays_refuse_without_changing_legacy_fallback() {
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    for text in [
        "opaque_array",
        "(_ as-array f)",
        "(lambda ((i (_ BitVec 64))) #x00)",
        "(store opaque_array (_ bv1 64) #x07)",
    ] {
        let value = sexp(text);
        assert_eq!(parse_typed_value(&value, &sort), None, "{text}");
        assert!(matches!(
            crate::api::model_parse::parse_array_value(&value, &Sort::bitvec(8)),
            ModelValue::ArraySmtlib(_)
        ));
    }
}

#[test]
fn constructors_require_declared_name_arity_field_sorts_and_qualification() {
    let sort = record_sort(
        "Pair",
        "mkPair",
        vec![("flag", Sort::Bool), ("byte", Sort::bitvec(8))],
    );
    let expected = Some(record("mkPair", vec![ModelValue::Bool(true), word(7, 8)]));
    assert_eq!(decode("(mkPair true #x07)", &sort), expected);
    assert_eq!(decode("((as mkPair Pair) true #x07)", &sort), expected);
    for text in [
        "(otherPair true #x07)",
        "mkPair",
        "(mkPair true)",
        "(mkPair true #x07 #x08)",
        "(mkPair #x07 true)",
        "(mkPair true #x0007)",
        "((as mkPair Other) true #x07)",
        "((as otherPair Pair) true #x07)",
        "((as mkPair Pair extra) true #x07)",
    ] {
        assert_eq!(decode(text, &sort), None, "{text}");
    }
}

#[test]
fn nullary_and_quoted_constructor_names_remain_sort_authenticated() {
    let sort = Sort::Datatype(DatatypeSort::new(
        "Choice space",
        vec![DatatypeConstructor::unit("none space")],
    ));
    for text in ["|none space|", "(as |none space| |Choice space|)"] {
        assert_eq!(decode(text, &sort), Some(record("none space", vec![])));
    }
    assert_eq!(decode("(as |none space| Wrong)", &sort), None);
    assert_eq!(decode("(as wrong |Choice space|)", &sort), None);
}

/// Datatype `||` with the nullary constructor `||` and the constructor `mk`
/// whose one field is `||`.
fn empty_names() -> DatatypeSort {
    DatatypeSort::new(
        "",
        vec![
            DatatypeConstructor::unit(""),
            DatatypeConstructor::new("mk", vec![DatatypeField::new("", Sort::Int)]),
        ],
    )
}

#[test]
fn empty_datatype_constructor_and_field_names_decode_as_ordinary_names() {
    let sort = Sort::Datatype(empty_names());
    for text in ["||", "(as || ||)"] {
        assert_eq!(decode(text, &sort), Some(record("", vec![])), "{text}");
    }
    assert_eq!(
        decode("(mk 7)", &sort),
        Some(record("mk", vec![ModelValue::Int(BigInt::from(7))]))
    );
    assert_eq!(decode("(as || Wrong)", &sort), None);
    let mut duplicate = empty_names();
    duplicate.constructors.push(DatatypeConstructor::unit(""));
    let mut duplicate_field = empty_names();
    duplicate_field.constructors[1]
        .fields
        .push(DatatypeField::new("", Sort::Bool));
    let mut no_constructors = empty_names();
    no_constructors.constructors.clear();
    for sort in [duplicate, duplicate_field, no_constructors] {
        assert_eq!(
            decode("(mk 7)", &Sort::Datatype(sort.clone())),
            None,
            "{sort:?}"
        );
    }
}

#[test]
fn overwritten_nested_defaults_and_fields_are_still_validated() {
    let sort = Sort::array(Sort::bitvec(64), inner_sort());
    for text in [
        "((as const (Array (_ BitVec 64) Wrong))
          (mkInner (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))",
        "(store ((as const (Array (_ BitVec 64) Inner))
          (mkInner true ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
          (_ bv33 64) (mkInner (_ bv65 64)
            ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)))",
        "((as const (Array (_ BitVec 64) Inner))
          (mkInner (_ bv0 64) ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)))",
        "((as const (Array (_ BitVec 64) Inner))
          (mkInner (_ bv0 64) opaque_array))",
    ] {
        assert_eq!(decode(text, &sort), None, "{text}");
    }
}

#[test]
fn decoder_refusal_is_batch_sticky_and_fresh_retry_is_independent() {
    let mut decoder = Decoder::new();
    assert_eq!(
        decoder.decode(&sexp("#x07"), &Sort::bitvec(8)),
        Some(word(7, 8))
    );
    assert_eq!(decoder.decode(&sexp("#x0007"), &Sort::bitvec(8)), None);
    assert_eq!(decoder.decode(&sexp("#x08"), &Sort::bitvec(8)), None);
    assert_eq!(decode("#x08", &Sort::bitvec(8)), Some(word(8, 8)));
}
