// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Data-only fixtures: no solver call, model provenance or SAT authority.

use super::*;
use crate::api::TypedModelValueDecodeError;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};
use num_bigint::BigInt;

mod resources;

fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: BigInt::from(value),
        width,
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

#[test]
fn ordered_batch_preserves_exact_wide_bits_and_equivalent_literal_spellings() {
    let byte = Sort::bitvec(8);
    let wide = Sort::bitvec(136);
    let high = (BigInt::from(1u8) << 130usize) + BigInt::from(9u8);
    let decimal = format!("(_ bv{high} 136)");
    let binary = format!("#b{:0>136}", high.to_str_radix(2));
    let actual = ModelValue::decode_typed_literals(&[
        ("false", &Sort::Bool),
        ("#x09", &byte),
        ("#b00001001", &byte),
        ("(_ bv9 8)", &byte),
        (&decimal, &wide),
        (&binary, &wide),
    ])
    .unwrap();
    assert_eq!(
        actual,
        vec![
            ModelValue::Bool(false),
            word(9, 8),
            word(9, 8),
            word(9, 8),
            ModelValue::BitVec {
                value: high.clone(),
                width: 136
            },
            ModelValue::BitVec {
                value: high,
                width: 136
            },
        ]
    );
    assert_eq!(
        ModelValue::decode_typed_literals(&[]).unwrap(),
        [] as [ModelValue; 0]
    );
}

#[test]
fn complete_nested_record_arrays_keep_defaults_duplicates_and_high_key_bits() {
    let row = record_sort(
        "Inner",
        "mkInner",
        vec![
            ("len", Sort::bitvec(64)),
            ("data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
        ],
    );
    let sort = record_sort(
        "Outer record",
        "mkOuter",
        vec![
            ("len", Sort::bitvec(64)),
            ("data", Sort::array(Sort::bitvec(136), row)),
        ],
    );
    let high = (BigInt::from(1u8) << 130usize) + BigInt::from(9u8);
    let text = format!("((as mkOuter |Outer record|) (_ bv2 64)
      (store (store ((as const (Array (_ BitVec 136) Inner))
        ((as mkInner Inner) (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
        (_ bv9 136) (mkInner (_ bv65 64)
          (store (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
            (_ bv64 64) #x09) (_ bv64 64) #x07)))
        (_ bv{high} 136) (mkInner (_ bv1 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x09))))");
    let values = ModelValue::decode_typed_literals(&[(&text, &sort)]).unwrap();
    let ModelValue::Datatype { constructor, args } = &values[0] else {
        panic!("outer record")
    };
    assert_eq!(constructor, "mkOuter");
    assert_eq!(args[0], word(2, 64));
    let ModelValue::Array { default, stores } = &args[1] else {
        panic!("outer array")
    };
    let ModelValue::Datatype { constructor, args } = default.as_ref() else {
        panic!("complete default")
    };
    assert_eq!(constructor, "mkInner");
    assert_eq!(args[0], word(0, 64));
    assert_eq!(stores.len(), 2);
    assert_eq!(stores[0].0, word(9, 136));
    assert_eq!(
        stores[1].0,
        ModelValue::BitVec {
            value: high,
            width: 136
        }
    );
    let ModelValue::Datatype { args, .. } = &stores[0].1 else {
        panic!("first row")
    };
    assert_eq!(args[0], word(65, 64));
    let ModelValue::Array { default, stores } = &args[1] else {
        panic!("inner array")
    };
    assert_eq!(default.as_ref(), &word(7, 8));
    assert_eq!(
        stores,
        &vec![(word(64, 64), word(9, 8)), (word(64, 64), word(7, 8))]
    );
}

#[test]
fn caller_sorts_refuse_width_range_constructor_and_array_ascription_mutations() {
    let byte = Sort::bitvec(8);
    for text in [
        "#b1",
        "#x0100",
        "(_ bv256 8)",
        "(_ bv-1 8)",
        "(_ bv7 64)",
        "7",
        "true",
        "(|_| bv7 8)",
        "(_ |bv7| 8)",
    ] {
        assert_eq!(
            ModelValue::decode_typed_literals(&[(text, &byte)]),
            Err(TypedModelValueDecodeError)
        );
    }
    let array = Sort::array(Sort::bitvec(64), byte.clone());
    for text in [
        "((as const (Array (_ BitVec 32) (_ BitVec 8))) #x07)",
        "((as const (Array (_ BitVec 64) (_ BitVec 16))) #x0007)",
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x0007)",
        "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07) (_ bv0 32) #x09)",
        "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07) (_ bv0 64) #x0009)",
        "((|as| const (Array (_ BitVec 64) (_ BitVec 8))) #x07)",
    ] {
        assert!(ModelValue::decode_typed_literals(&[(text, &array)]).is_err());
    }
    let record = record_sort("R", "mkR", vec![("field", byte)]);
    for text in [
        "(other #x07)",
        "mkR",
        "(mkR #x07 #x09)",
        "(mkR true)",
        "((as mkR Wrong) #x07)",
    ] {
        assert!(ModelValue::decode_typed_literals(&[(text, &record)]).is_err());
    }
}

#[test]
fn no_opaque_values_open_expressions_or_trailing_commands_are_accepted() {
    let byte = Sort::bitvec(8);
    for text in [
        "unknown",
        "x",
        "(f #x00)",
        "(let ((x #x00)) x)",
        "(bvadd #x00 #x01)",
        "#x00 #x01",
        "#x00 (check-sat)",
        "",
        "((x #x00))",
    ] {
        assert!(
            ModelValue::decode_typed_literals(&[(text, &byte)]).is_err(),
            "{text}"
        );
    }
    let array = Sort::array(byte.clone(), byte);
    for text in [
        "@arr33",
        "(as-array f)",
        "(_ as-array f)",
        "(store @arr33 #x00 #x01)",
    ] {
        assert!(ModelValue::decode_typed_literals(&[(text, &array)]).is_err());
    }
    assert!(
        ModelValue::decode_typed_literals(&[("@U!0", &Sort::Uninterpreted("U".into()))]).is_err()
    );
    let incomplete = record_sort("R", "mkR", vec![("child", Sort::Uninterpreted("R".into()))]);
    assert!(ModelValue::decode_typed_literals(&[("(mkR @R!0)", &incomplete)]).is_err());
}

#[test]
fn primitive_sequence_fp_and_quoted_nullary_forms_keep_existing_exact_semantics() {
    let sequence = Sort::Seq(Box::new(Sort::bitvec(8)));
    let nullary = record_sort("Choice space", "none space", vec![]);
    let ordinary_quoted = record_sort(
        "record space",
        "bv_payload",
        vec![("field", Sort::bitvec(8))],
    );
    let values = ModelValue::decode_typed_literals(&[
        ("(- 7)", &Sort::Int),
        ("(/ 1.0 10.0)", &Sort::Real),
        ("\"a\"\"b\"", &Sort::String),
        (
            "(seq.++ (as seq.empty (Seq (_ BitVec 8))) (seq.unit #x07) (seq.unit #x09))",
            &sequence,
        ),
        (
            "(fp #b1 #xff #b00000000000000000000000)",
            &Sort::FloatingPoint(8, 24),
        ),
        ("(as |none space| |Choice space|)", &nullary),
        ("((as |bv_payload| |record space|) #x07)", &ordinary_quoted),
    ])
    .unwrap();
    assert_eq!(values[0], ModelValue::Int(BigInt::from(-7)));
    assert_eq!(
        values[1],
        ModelValue::Real(num_rational::BigRational::new(
            BigInt::from(1),
            BigInt::from(10)
        ))
    );
    assert_eq!(values[2], ModelValue::String("a\"b".into()));
    assert_eq!(values[3], ModelValue::Seq(vec![word(7, 8), word(9, 8)]));
    assert!(matches!(
        values[4],
        ModelValue::FloatingPoint {
            sign: true,
            exponent: 255,
            significand: 0,
            eb: 8,
            sb: 24
        }
    ));
    assert_eq!(
        values[5],
        ModelValue::Datatype {
            constructor: "none space".into(),
            args: vec![]
        }
    );
    assert_eq!(
        values[6],
        ModelValue::Datatype {
            constructor: "bv_payload".into(),
            args: vec![word(7, 8)],
        }
    );
}
