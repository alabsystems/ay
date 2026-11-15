// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::{CancellationToken, ChcProblem};
use ay_core::time::Instant;
use ay_frontend::sexp::{parse_sexps, SExpr};
use std::sync::Arc;
use std::time::Duration;

mod resources;

fn registry() -> Registry {
    Registry::new(&ChcProblem::new()).unwrap()
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn model(value: &BigUint, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: BigInt::from(value.clone()),
        width,
    }
}

fn decoded(value: &ModelValue, sort: &ChcSort, registry: &Registry) -> Option<SmtValue> {
    let token = CancellationToken::new();
    decode(
        value,
        sort,
        registry,
        &SourceControl::new(deadline(), &token),
    )
}

fn text(value: &SmtValue, sort: &ChcSort, registry: &Registry) -> Option<String> {
    let token = CancellationToken::new();
    literal(
        value,
        sort,
        registry,
        &SourceControl::new(deadline(), &token),
    )
}

fn number(expr: &SExpr) -> (BigUint, u32) {
    if let SExpr::Binary(text) = expr {
        let digits = text.strip_prefix("#b").unwrap();
        return (
            BigUint::parse_bytes(digits.as_bytes(), 2).unwrap(),
            digits.len() as u32,
        );
    }
    let [marker, value, width] = expr.as_list().unwrap() else {
        panic!("indexed BV literal")
    };
    assert!(marker.is_symbol("_"));
    let digits = value.as_symbol().unwrap().strip_prefix("bv").unwrap();
    (
        BigUint::parse_bytes(digits.as_bytes(), 10).unwrap(),
        width.as_numeral().unwrap().parse().unwrap(),
    )
}

#[test]
fn unsigned_72_128_and_136_bit_values_roundtrip_without_high_bit_loss() {
    let registry = registry();
    for width in [72, 128, 136] {
        let top = BigUint::from(1u8) << (width - 1) as usize;
        let maximum = (BigUint::from(1u8) << width as usize) - BigUint::from(1u8);
        for value in [BigUint::from(0u8), BigUint::from(1u8), top, maximum] {
            let sort = ChcSort::BitVec(width);
            let decoded = decoded(&model(&value, width), &sort, &registry).unwrap();
            if width <= 128 {
                assert_eq!(decoded, SmtValue::BitVec(value.to_u128().unwrap(), width));
            } else {
                assert!(
                    matches!(&decoded, SmtValue::BigBitVec(actual, w) if actual.as_ref() == &value && *w == width)
                );
            }
            let rendered = text(&decoded, &sort, &registry).unwrap();
            assert_eq!(number(&parse_sexps(&rendered).unwrap()[0]), (value, width));
            assert_eq!(rendered.starts_with("#b"), width > 128);
            if width > 128 {
                assert_eq!(rendered.len(), width as usize + 2);
            }
        }
    }
}

#[test]
fn wrong_width_sign_range_and_noncanonical_carriers_are_refused() {
    let registry = registry();
    for width in [72, 128, 136] {
        let sort = ChcSort::BitVec(width);
        for (value, recorded) in [
            (BigInt::from(-1), width),
            (BigInt::from(1u8) << width as usize, width),
            (BigInt::from(0), width - 1),
            (BigInt::from(0), width + 1),
        ] {
            assert!(decoded(
                &ModelValue::BitVec {
                    value,
                    width: recorded
                },
                &sort,
                &registry
            )
            .is_none());
        }
        let wrong_carrier = if width <= 128 {
            SmtValue::BigBitVec(Arc::new(BigUint::from(0u8)), width)
        } else {
            SmtValue::BitVec(0, width)
        };
        assert!(text(&wrong_carrier, &sort, &registry).is_none());
        assert!(text(
            &SmtValue::BigBitVec(Arc::new(BigUint::from(1u8) << width as usize), width),
            &sort,
            &registry
        )
        .is_none());
    }
    // Signed -1 is not accepted as an all-ones spelling; the exact unsigned
    // maximum at width128 is nevertheless valid without evaluating 1<<128.
    assert_eq!(
        text(
            &SmtValue::BitVec(u128::MAX, 128),
            &ChcSort::BitVec(128),
            &registry
        )
        .unwrap(),
        format!("(_ bv{} 128)", u128::MAX)
    );
    assert!(text(
        &SmtValue::BitVec(1u128 << 72, 72),
        &ChcSort::BitVec(72),
        &registry
    )
    .is_none());
}

fn array(key: u32, cell: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(key)), Box::new(cell))
}

fn row(fill: &BigUint, index: &BigUint) -> ModelValue {
    ModelValue::Datatype {
        constructor: "mk wide".into(),
        args: vec![
            model(&(BigUint::from(1u8) << 71usize), 72),
            ModelValue::Array {
                default: Box::new(model(&BigUint::from(0u8), 136)),
                stores: vec![
                    (model(index, 128), model(&BigUint::from(5u8), 136)),
                    (model(index, 128), model(fill, 136)),
                ],
            },
        ],
    }
}

fn selected<'a>(expr: &'a SExpr, key: &BigUint) -> &'a SExpr {
    let parts = expr.as_list().unwrap();
    if parts[0].is_symbol("store") {
        if &number(&parts[2]).0 == key {
            &parts[3]
        } else {
            selected(&parts[1], key)
        }
    } else {
        assert!(parts[0].as_list().unwrap()[0].is_symbol("as"));
        &parts[1]
    }
}

#[test]
fn nested_record_arrays_keep_high_keys_defaults_and_repeated_store_order() {
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def(
        "Wide row".into(),
        vec![(
            "mk wide".into(),
            vec![
                ("length".into(), ChcSort::BitVec(72)),
                ("cells".into(), array(128, ChcSort::BitVec(136))),
            ],
        )],
    );
    let registry = Registry::new(&declarations).unwrap();
    let sort = array(136, registry.lookup("Wide row").unwrap().clone());
    let key = (BigUint::from(1u8) << 135usize) + BigUint::from(3u8);
    let other = BigUint::from(3u8); // identical low128 bits, distinct full key
    let inner = (BigUint::from(1u8) << 127usize) + BigUint::from(9u8);
    let fill = (BigUint::from(1u8) << 134usize) + BigUint::from(7u8);
    let original = ModelValue::Array {
        default: Box::new(row(&BigUint::from(0u8), &inner)),
        stores: vec![
            (model(&key, 136), row(&BigUint::from(1u8), &inner)),
            (model(&other, 136), row(&BigUint::from(2u8), &inner)),
            (model(&key, 136), row(&fill, &inner)),
        ],
    };
    let value = decoded(&original, &sort, &registry).unwrap();
    let SmtValue::ArrayMap { entries, .. } = &value else {
        panic!("array")
    };
    assert_eq!(entries.len(), 3);
    assert_eq!(entries[0].0, entries[2].0);
    assert_ne!(entries[0].0, entries[1].0);
    let rendered = text(&value, &sort, &registry).unwrap();
    assert_eq!(rendered.matches("(store ").count(), 11);
    let parsed = parse_sexps(&rendered).unwrap();
    for (outer, expected) in [
        (key, fill),
        (other, BigUint::from(2u8)),
        (BigUint::from(4u8), BigUint::from(0u8)),
    ] {
        let row = selected(&parsed[0], &outer).as_list().unwrap();
        assert!(row[0].as_list().unwrap()[0].is_symbol("as"));
        assert_eq!(number(&row[1]), (BigUint::from(1u8) << 71usize, 72));
        assert_eq!(number(selected(&row[2], &inner)), (expected, 136));
        assert_eq!(
            number(selected(&row[2], &BigUint::from(0u8))),
            (BigUint::from(0u8), 136)
        );
    }
}

#[test]
fn overwritten_wide_entries_and_defaults_are_still_fully_authenticated() {
    let registry = registry();
    let sort = array(136, ChcSort::BitVec(136));
    let zero = BigUint::from(0u8);
    let valid = model(&zero, 136);
    for (default, stores) in [
        (ModelValue::Unknown, vec![]),
        (valid.clone(), vec![(model(&zero, 128), valid.clone())]),
        (
            valid.clone(),
            vec![
                (valid.clone(), ModelValue::Unknown),
                (valid.clone(), valid.clone()),
            ],
        ),
        (
            valid.clone(),
            vec![(
                valid.clone(),
                ModelValue::BitVec {
                    value: BigInt::from(-1),
                    width: 136,
                },
            )],
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
    assert!(text(
        &SmtValue::ArrayMap {
            default: Box::new(SmtValue::BigBitVec(Arc::new(zero), 136)),
            entries: vec![(SmtValue::BitVec(0, 136), SmtValue::Opaque("hidden".into()))],
        },
        &sort,
        &registry
    )
    .is_none());
}
