// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::{CancellationToken, ChcDtConstructor, ChcDtSelector, ChcProblem};
use ay_core::time::Instant;
use ay_frontend::sexp::{parse_sexps, SExpr};
use num_bigint::BigInt;
use std::sync::Arc;
use std::time::Duration;

fn registry() -> Registry {
    Registry::new(&ChcProblem::new()).unwrap()
}

fn array(cell: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(cell))
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

fn decoded(value: &ModelValue, sort: &ChcSort, registry: &Registry) -> Option<SmtValue> {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    decode(value, sort, registry, &control)
}

fn text(value: &SmtValue, sort: &ChcSort, registry: &Registry) -> Option<String> {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    literal(value, sort, registry, &control)
}

fn rows() -> Registry {
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def(
        "Cell row".into(),
        vec![(
            "mk row".into(),
            vec![
                ("length".into(), ChcSort::BitVec(64)),
                ("data".into(), array(ChcSort::BitVec(8))),
            ],
        )],
    );
    Registry::new(&declarations).unwrap()
}

fn row(length: u64, fill: u64) -> ModelValue {
    ModelValue::Datatype {
        constructor: "mk row".into(),
        args: vec![
            bv(length, 64),
            ModelValue::Array {
                default: Box::new(bv(fill, 8)),
                stores: vec![(bv(64, 64), bv(7, 8)), (bv(64, 64), bv(9, 8))],
            },
        ],
    }
}

#[test]
fn scalar_values_keep_exact_widths_and_unsigned_64_bit_endpoints() {
    let registry = registry();
    for value in [false, true] {
        let decoded = decoded(&ModelValue::Bool(value), &ChcSort::Bool, &registry).unwrap();
        assert_eq!(decoded, SmtValue::Bool(value));
        assert_eq!(
            text(&decoded, &ChcSort::Bool, &registry).unwrap(),
            value.to_string()
        );
    }
    for width in [1, 2, 8, 32, 64] {
        let maximum = u64::MAX >> (64 - width);
        for value in [0, 1, maximum] {
            let sort = ChcSort::BitVec(width);
            let decoded = decoded(&bv(value, width), &sort, &registry).unwrap();
            assert_eq!(decoded, SmtValue::BitVec(u128::from(value), width));
            assert_eq!(
                text(&decoded, &sort, &registry).unwrap(),
                format!("(_ bv{value} {width})")
            );
        }
    }
}

#[test]
fn malformed_bitvectors_are_not_truncated_masked_or_coerced() {
    let registry = registry();
    let sort = ChcSort::BitVec(8);
    for (value, width) in [
        (BigInt::from(-1), 8),
        (BigInt::from(256), 8),
        (BigInt::from(0), 0),
        (BigInt::from(0), 64),
        (BigInt::from(0), 65),
        (BigInt::from(1) << 100_000usize, 8),
    ] {
        assert!(decoded(&ModelValue::BitVec { value, width }, &sort, &registry).is_none());
    }
    for value in [
        SmtValue::BitVec(256, 8),
        SmtValue::BitVec(0, 0),
        SmtValue::BitVec(0, 64),
        SmtValue::Int(1),
        SmtValue::BigBitVec(Arc::new(0u8.into()), 8),
    ] {
        assert!(text(&value, &sort, &registry).is_none());
    }
    assert!(decoded(&bv(0, 0), &ChcSort::BitVec(0), &registry).is_none());
    assert!(decoded(
        &bv(0, crate::MAX_BITVECTOR_WIDTH + 1),
        &ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH + 1),
        &registry
    )
    .is_none());
    assert!(text(
        &SmtValue::BitVec(1u128 << 64, 64),
        &ChcSort::BitVec(64),
        &registry
    )
    .is_none());
}

#[test]
fn opaque_and_wrong_kind_values_never_gain_concrete_authority() {
    let registry = registry();
    for value in [
        ModelValue::Unknown,
        ModelValue::Int(0.into()),
        ModelValue::Real(num_rational::BigRational::from_integer(0.into())),
        ModelValue::String("true".into()),
        ModelValue::Uninterpreted("@value!0".into()),
        ModelValue::ArraySmtlib("((as const (Array (_ BitVec 64) Bool)) true)".into()),
        ModelValue::Seq(vec![]),
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0,
            significand: 0,
            eb: 8,
            sb: 24,
        },
    ] {
        assert!(decoded(&value, &ChcSort::Bool, &registry).is_none());
        assert!(decoded(&value, &array(ChcSort::Bool), &registry).is_none());
    }
    for value in [
        SmtValue::Opaque("true".into()),
        SmtValue::Int(0),
        SmtValue::Real(num_rational::BigRational::from_integer(0.into())),
    ] {
        assert!(text(&value, &ChcSort::Bool, &registry).is_none());
    }
    assert!(decoded(&ModelValue::Bool(true), &ChcSort::BitVec(1), &registry).is_none());
    assert!(decoded(&bv(1, 1), &ChcSort::Bool, &registry).is_none());
}

#[test]
fn constructor_identity_arity_and_every_field_are_authenticated() {
    let registry = rows();
    let sort = registry.lookup("Cell row").unwrap();
    for value in [
        ModelValue::Datatype {
            constructor: "other".into(),
            args: vec![bv(2, 64), bv(0, 8)],
        },
        ModelValue::Datatype {
            constructor: "mk row".into(),
            args: vec![bv(2, 64)],
        },
        ModelValue::Datatype {
            constructor: "mk row".into(),
            args: vec![bv(2, 64), bv(0, 8), bv(0, 8)],
        },
        ModelValue::Datatype {
            constructor: "mk row".into(),
            args: vec![bv(2, 64), ModelValue::Unknown],
        },
        ModelValue::Datatype {
            constructor: "mk row".into(),
            args: vec![
                bv(2, 8),
                ModelValue::Array {
                    default: Box::new(bv(0, 8)),
                    stores: vec![],
                },
            ],
        },
    ] {
        assert!(decoded(&value, sort, &registry).is_none());
    }
    let valid = decoded(&row(2, 3), sort, &registry).unwrap();
    let SmtValue::Datatype(name, fields) = valid else {
        panic!("record");
    };
    assert!(text(
        &SmtValue::Datatype("other".into(), fields.clone()),
        sort,
        &registry
    )
    .is_none());
    assert!(text(
        &SmtValue::Datatype(name.clone(), fields[..1].to_vec()),
        sort,
        &registry
    )
    .is_none());
    let mut bad = fields;
    bad[1] = SmtValue::Opaque("hidden array".into());
    assert!(text(&SmtValue::Datatype(name, bad), sort, &registry).is_none());
}

#[test]
fn forged_record_metadata_and_unsupported_sort_paths_are_rejected() {
    let registry = rows();
    let forged = ChcSort::Datatype {
        name: "Cell row".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "mk row".into(),
            selectors: vec![
                ChcDtSelector {
                    name: "length".into(),
                    sort: ChcSort::BitVec(64),
                },
                ChcDtSelector {
                    name: "data".into(),
                    sort: ChcSort::Bool,
                },
            ],
        }]),
    };
    let pretend = ModelValue::Datatype {
        constructor: "mk row".into(),
        args: vec![bv(2, 64), ModelValue::Bool(true)],
    };
    assert!(decoded(&pretend, &forged, &registry).is_none());
    assert!(text(
        &SmtValue::Datatype(
            "mk row".into(),
            vec![SmtValue::BitVec(2, 64), SmtValue::Bool(true)]
        ),
        &forged,
        &registry
    )
    .is_none());
    let invalid_sorts = [
        ChcSort::Int,
        ChcSort::Real,
        ChcSort::Uninterpreted("Cell row".into()),
        ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool)),
        array(array(array(ChcSort::Bool))),
    ];
    for sort in invalid_sorts {
        assert!(decoded(&ModelValue::Bool(false), &sort, &registry).is_none());
        assert!(text(&SmtValue::Bool(false), &sort, &registry).is_none());
    }
}

#[test]
fn complete_nested_record_arrays_preserve_cell_64_and_duplicate_store_order() {
    let registry = rows();
    let sort = array(registry.lookup("Cell row").unwrap().clone());
    let original = ModelValue::Array {
        default: Box::new(row(0, 4)),
        stores: vec![(bv(33, 64), row(1, 5)), (bv(33, 64), row(65, 6))],
    };
    let decoded = decoded(&original, &sort, &registry).unwrap();
    let SmtValue::ArrayMap { default, entries } = &decoded else {
        panic!("array");
    };
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].0, SmtValue::BitVec(33, 64));
    assert_eq!(entries[1].0, SmtValue::BitVec(33, 64));
    let SmtValue::Datatype(_, fields) = &entries[1].1 else {
        panic!("record");
    };
    assert_eq!(fields[0], SmtValue::BitVec(65, 64));
    let SmtValue::ArrayMap { entries: cells, .. } = &fields[1] else {
        panic!("data");
    };
    assert_eq!(
        cells,
        &vec![
            (SmtValue::BitVec(64, 64), SmtValue::BitVec(7, 8)),
            (SmtValue::BitVec(64, 64), SmtValue::BitVec(9, 8))
        ]
    );
    assert_ne!(&entries[0].1, &entries[1].1);
    assert_ne!(default.as_ref(), &entries[0].1);
    let literal = text(&decoded, &sort, &registry).unwrap();
    assert!(literal.starts_with("(store (store ((as const (Array (_ BitVec 64) |Cell row|))"));
    assert_eq!(literal.matches("((as |mk row| |Cell row|)").count(), 3);
    assert_eq!(literal.matches("(_ bv64 64) (_ bv9 8)").count(), 3);
    let script = format!("{}(declare-const snapshot (Array (_ BitVec 64) |Cell row|))\n(assert (= snapshot {literal}))\n(check-sat)", registry.declarations_smtlib().unwrap());
    ay_frontend::parse(&script).expect("quoted complete original datatype/array literal syntax");
}

fn list(expr: &SExpr) -> &[SExpr] {
    let SExpr::List(values) = expr else {
        panic!("list");
    };
    values
}

fn number(expr: &SExpr) -> u64 {
    let parts = list(expr);
    let SExpr::Symbol(value) = &parts[1] else {
        panic!("bv numeral");
    };
    value.strip_prefix("bv").unwrap().parse().unwrap()
}

fn read_literal(expr: &SExpr, index: u64) -> u64 {
    let parts = list(expr);
    if matches!(&parts[0], SExpr::Symbol(name) if name == "store") {
        if number(&parts[2]) == index {
            number(&parts[3])
        } else {
            read_literal(&parts[1], index)
        }
    } else {
        assert!(matches!(&list(&parts[0])[0], SExpr::Symbol(name) if name == "as"));
        number(&parts[1])
    }
}

#[test]
fn streamed_stores_have_last_write_semantics_without_deduplication() {
    let registry = registry();
    let sort = array(ChcSort::BitVec(8));
    let value = ModelValue::Array {
        default: Box::new(bv(4, 8)),
        stores: vec![(bv(64, 64), bv(7, 8)), (bv(64, 64), bv(9, 8))],
    };
    let value = decoded(&value, &sort, &registry).unwrap();
    let text = text(&value, &sort, &registry).unwrap();
    assert_eq!(text, "(store (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv4 8)) (_ bv64 64) (_ bv7 8)) (_ bv64 64) (_ bv9 8))");
    let parsed = parse_sexps(&text).unwrap();
    for index in [0, 63, 64, 65, u64::MAX] {
        assert_eq!(
            read_literal(&parsed[0], index),
            if index == 64 { 9 } else { 4 }
        );
    }
    assert_eq!(text.matches("(store ").count(), 2);
}

#[test]
fn all_defaults_keys_and_overwritten_cells_must_be_concrete_and_well_typed() {
    let registry = registry();
    let sort = array(ChcSort::BitVec(8));
    for (default, stores) in [
        (ModelValue::Unknown, vec![]),
        (bv(0, 64), vec![]),
        (bv(0, 8), vec![(bv(0, 8), bv(1, 8))]),
        (bv(0, 8), vec![(ModelValue::Int(0.into()), bv(1, 8))]),
        (
            bv(0, 8),
            vec![(bv(0, 64), ModelValue::Unknown), (bv(0, 64), bv(1, 8))],
        ),
    ] {
        assert!(decoded(
            &ModelValue::Array {
                default: Box::new(default),
                stores
            },
            &sort,
            &registry
        )
        .is_none());
    }
    let missing = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Opaque("default".into())),
        entries: vec![],
    };
    assert!(text(&missing, &sort, &registry).is_none());
    let bad_key = SmtValue::ArrayMap {
        default: Box::new(SmtValue::BitVec(0, 8)),
        entries: vec![(SmtValue::BitVec(0, 8), SmtValue::BitVec(1, 8))],
    };
    assert!(text(&bad_key, &sort, &registry).is_none());
    let constant = SmtValue::ConstArray(Box::new(SmtValue::BitVec(3, 8)));
    assert_eq!(
        text(&constant, &sort, &registry).unwrap(),
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv3 8))"
    );
}

#[test]
fn fixed_node_depth_copy_and_text_limits_refuse_before_partial_publication() {
    let registry = registry();
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let mut codec = Codec::new(&control);
    codec.nodes_left = 0;
    assert!(codec
        .decode(&ModelValue::Bool(true), &ChcSort::Bool, 0)
        .is_none());
    let mut codec = Codec::new(&control);
    codec.nodes_left = 1;
    codec.decoded_bytes = MAX_OUTPUT - std::mem::size_of::<SmtValue>();
    assert_eq!(
        codec.decode(&ModelValue::Bool(true), &ChcSort::Bool, 0),
        Some(SmtValue::Bool(true))
    );
    assert_eq!(codec.decoded_bytes, MAX_OUTPUT);
    let mut codec = Codec::new(&control);
    codec.decoded_bytes = MAX_OUTPUT;
    assert!(codec
        .decode(&ModelValue::Bool(true), &ChcSort::Bool, 0)
        .is_none());
    let mut codec = Codec::new(&control);
    assert!(codec
        .write(&SmtValue::Bool(true), &ChcSort::Bool, MAX_DEPTH + 1)
        .is_none());
    assert!(Codec::new(&control)
        .write(&SmtValue::Bool(true), &ChcSort::Bool, MAX_DEPTH)
        .is_some());
    let oversized = "x".repeat(MAX_OUTPUT + 1);
    assert!(Codec::new(&control).push(&oversized).is_none());
    let mut codec = Codec::new(&control);
    assert!(codec.push(&oversized[..MAX_OUTPUT]).is_some());
    assert_eq!(codec.text.len(), MAX_OUTPUT);
    assert!(codec.push("x").is_none());
    let sort = array(ChcSort::Bool);
    let value = ModelValue::Array {
        default: Box::new(ModelValue::Bool(false)),
        stores: vec![(bv(0, 64), ModelValue::Bool(true)); MAX_DEPTH],
    };
    assert!(decoded(&value, &sort, &registry).is_none());
    assert_eq!(
        decoded(&ModelValue::Bool(true), &ChcSort::Bool, &registry),
        Some(SmtValue::Bool(true))
    );
}

#[test]
fn shared_refusal_deadline_and_cancellation_are_sticky_with_fresh_retry() {
    let registry = registry();
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(control.bytes(usize::MAX).is_none());
    assert!(decode(&ModelValue::Bool(true), &ChcSort::Bool, &registry, &control).is_none());
    assert!(literal(&SmtValue::Bool(true), &ChcSort::Bool, &registry, &control).is_none());
    token.cancel();
    let cancelled = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(decode(
        &ModelValue::Bool(true),
        &ChcSort::Bool,
        &registry,
        &cancelled
    )
    .is_none());
    token.reset();
    assert!(literal(&SmtValue::Bool(true), &ChcSort::Bool, &registry, &cancelled).is_none());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(literal(&SmtValue::Bool(true), &ChcSort::Bool, &registry, &expired).is_none());
    assert_eq!(
        text(&SmtValue::Bool(true), &ChcSort::Bool, &registry).as_deref(),
        Some("true")
    );
}
