// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{bool_value, null, u32_value};
use super::*;
use crate::bundle::retained::{control, TransportOutcome};
use ay_core::{time::Instant, BitVecSort, Sort};
use serde::Deserialize;
use serde_json::value::RawValue;
use std::{cell::Cell, time::Duration};

fn end() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn raw(text: &str) -> RawSlice<'_> {
    RawSlice::from_raw(serde_json::from_str::<&RawValue>(text).unwrap())
}

fn checked<'a, T>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    control::run(end(), &mut |_, _| true, |control| {
        decode(raw(text), control)
    })
}

fn required<'a>(
    value: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    value
        .ok_or(TransportError::InvalidShape("missing required field"))
        .or_else(|error| control.fail(error))
}

fn bitvec(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<BitVecSort, TransportError> {
    let fields = structure(raw, &["width"], UnknownFields::Reject, control)?;
    Ok(BitVecSort::new(u32_value(
        required(fields.values[0], control)?,
        control,
    )?))
}

#[test]
fn exact_tuple_is_heap_free_and_preserves_null_and_borrowed_subranges() {
    for text in [
        "[7,true]",
        "[ 7 , true ]",
        "[7]",
        "[7,true,0]",
        "null",
        "{}",
    ] {
        let actual = checked(text, |raw, control| {
            let values = tuple::<2>(raw, control)?;
            Ok((
                u32_value(required(values[0], control)?, control)?,
                bool_value(required(values[1], control)?, control)?,
            ))
        });
        let expected = serde_json::from_str::<(u32, bool)>(text);
        assert_eq!(actual.result.ok(), expected.ok(), "{text}");
        assert_eq!(actual.usage.charged_bytes, 0);
    }
    let empty = checked("[]", tuple::<0>);
    assert!(empty.result.is_ok());
    assert_eq!(empty.usage.charged_bytes, 0);
    let text = "[null,{\"nested\":[\" },] \",true]}]";
    let fields = checked(text, tuple::<2>).result.unwrap();
    assert_eq!(fields[0].unwrap().as_str(), "null");
    assert_eq!(fields[1].unwrap().as_str(), "{\"nested\":[\" },] \",true]}");
    for field in fields.into_iter().flatten() {
        assert!(
            (text.as_ptr() as usize..text.as_ptr() as usize + text.len())
                .contains(&(field.as_str().as_ptr() as usize))
        );
    }
}

#[test]
fn actual_bitvec_sort_struct_object_and_sequence_forms_match_legacy_serde() {
    for text in [
        r#"{"width":8}"#,
        r#"{"\u0077idth":0}"#,
        "[32]",
        "[]",
        "[32,1]",
        "{}",
        r#"{"width":null}"#,
        r#"{"width":8,"extra":0}"#,
        r#"{"width":8,"\u0077idth":8}"#,
        "false",
        r#"{"width":-0}"#,
    ] {
        let actual = checked(text, bitvec);
        let expected = serde_json::from_str::<BitVecSort>(text);
        assert_eq!(actual.result.is_ok(), expected.is_ok(), "{text}");
        assert_eq!(actual.result.ok(), expected.ok(), "{text}");
    }
}

#[derive(Debug, Deserialize, PartialEq)]
struct Legacy {
    required: u32,
    optional: Option<u32>,
    #[serde(default)]
    tail: bool,
}

fn legacy(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<Legacy, TransportError> {
    let fields = structure(
        raw,
        &["required", "optional", "tail"],
        UnknownFields::Ignore,
        control,
    )?;
    let required_value = u32_value(required(fields.values[0], control)?, control)?;
    let optional = match fields.values[1] {
        Some(raw) if raw.as_str() == "null" => {
            null(raw, control)?;
            None
        }
        Some(raw) => Some(u32_value(raw, control)?),
        None if fields.form == Form::Object => None,
        None => return control.fail(TransportError::InvalidShape("short struct sequence")),
    };
    let tail = match fields.values[2] {
        Some(raw) => bool_value(raw, control)?,
        None => false,
    };
    Ok(Legacy {
        required: required_value,
        optional,
        tail,
    })
}

#[test]
fn form_preservation_keeps_map_option_default_distinct_from_short_sequence() {
    for text in [
        r#"{"required":3}"#,
        r#"{"required":3,"optional":null}"#,
        r#"{"required":3,"optional":4,"tail":true}"#,
        r#"{"required":3,"unknown":{"skipped":[1,null]}}"#,
        "[3]",
        "[3,null]",
        "[3,4,true]",
        "[3,null,false,7]",
        "{}",
        r#"{"required":3,"optional":null,"optional":4}"#,
    ] {
        let actual = checked(text, legacy);
        let expected = serde_json::from_str::<Legacy>(text);
        assert_eq!(actual.result.is_ok(), expected.is_ok(), "{text}");
        assert_eq!(actual.result.ok(), expected.ok(), "{text}");
    }
    let map = checked("{}", |raw, control| {
        structure(raw, &["width"], UnknownFields::Reject, control)
    })
    .result
    .unwrap();
    let seq = checked("[]", |raw, control| {
        structure(raw, &["width"], UnknownFields::Reject, control)
    })
    .result
    .unwrap();
    assert_eq!(map.form, Form::Object);
    assert_eq!(seq.form, Form::Sequence);
    assert!(map.values[0].is_none() && seq.values[0].is_none());
}

#[test]
fn object_cursor_keeps_escaped_keys_and_nested_string_delimiters_exact() {
    let text = r#"{ "\u0061" : "comma,} and \" quote", "b": [{"é":" },] "}], "c":null }"#;
    let outcome = checked(text, |raw, control| {
        structure(raw, &["a", "b", "c"], UnknownFields::Reject, control)
    });
    let fields = outcome.result.unwrap();
    assert_eq!(
        fields.values[0].unwrap().as_str(),
        r#""comma,} and \" quote""#
    );
    assert_eq!(fields.values[1].unwrap().as_str(), r#"[{"é":" },] "}]"#);
    assert_eq!(fields.values[2].unwrap().as_str(), "null");
    assert!(outcome.usage.charged_bytes >= 8); // encoded a(6), b(1), c(1)
    assert_eq!(outcome.usage.returned_owned_bytes, 0); // Keys were temporary.
}

fn simple_sort(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<Sort, TransportError> {
    let tag = tagged(
        raw,
        &["Bool", "BitVec", "FloatingPoint", "Uninterpreted"],
        control,
    )?;
    match tag.index {
        0 => {
            if let Some(body) = tag.payload {
                null(body, control)?;
            }
            Ok(Sort::Bool)
        }
        1 => Ok(Sort::BitVec(bitvec(
            required(tag.payload, control)?,
            control,
        )?)),
        2 => {
            let pair = tuple::<2>(required(tag.payload, control)?, control)?;
            Ok(Sort::FloatingPoint(
                u32_value(required(pair[0], control)?, control)?,
                u32_value(required(pair[1], control)?, control)?,
            ))
        }
        3 => Ok(Sort::Uninterpreted(owned_string(
            required(tag.payload, control)?,
            control,
        )?)),
        _ => control.fail(TransportError::InvalidShape("unexpected variant index")),
    }
}

#[test]
fn actual_sort_unit_newtype_and_tuple_variants_match_legacy_serde() {
    for text in [
        r#""Bool""#,
        r#""\u0042ool""#,
        r#"{"Bool":null}"#,
        r#"{"Bool":false}"#,
        r#""BitVec""#,
        r#"{"\u0042itVec":{"width":8}}"#,
        r#"{"BitVec":[8]}"#,
        r#"{"FloatingPoint":[8,24]}"#,
        r#"{"FloatingPoint":[8]}"#,
        r#"{"Uninterpreted":"λ"}"#,
        r#"{"Uninterpreted":null}"#,
        "{}",
        r#"{"Bool":null,"Bool":null}"#,
        r#"{"Bogus":null}"#,
        "[]",
        "0",
    ] {
        let actual = checked(text, simple_sort);
        let expected = serde_json::from_str::<Sort>(text);
        assert_eq!(actual.result.is_ok(), expected.is_ok(), "{text}");
        assert_eq!(actual.result.ok(), expected.ok(), "{text}");
    }
    let string = checked(r#""Bool""#, |raw, control| tagged(raw, &["Bool"], control))
        .result
        .unwrap();
    let object = checked(r#"{"Bool":null}"#, |raw, control| {
        tagged(raw, &["Bool"], control)
    })
    .result
    .unwrap();
    assert!(string.payload.is_none());
    assert_eq!(object.payload.unwrap().as_str(), "null");
}

#[test]
fn rejected_names_are_precapped_but_ignored_long_names_keep_legacy_semantics() {
    let long_key = "q".repeat(2048);
    let text = format!(r#"{{"{long_key}":{{"ignored":[1]}},"required":3}}"#);
    let ignored = checked(&text, legacy);
    assert_eq!(
        ignored.result.unwrap(),
        serde_json::from_str::<Legacy>(&text).unwrap()
    );
    assert!(ignored.usage.charged_bytes >= long_key.len());
    let rejected = checked(&text, |raw, control| {
        structure(raw, &["required"], UnknownFields::Reject, control)
    });
    assert!(matches!(
        rejected.result,
        Err(TransportError::Limit {
            resource: "encoded field name bytes",
            ..
        })
    ));
    assert_eq!(rejected.usage.charged_bytes, 0);
    let variant = format!("\"{long_key}\"");
    let rejected = checked(&variant, |raw, control| tagged(raw, &["Bool"], control));
    assert!(matches!(rejected.result, Err(TransportError::Limit { .. })));
    assert_eq!(rejected.usage.charged_bytes, 0);
    for text in [
        r#"{"\ud800":0,"required":3}"#,
        r#"{"\udc00":0,"required":3}"#,
    ] {
        assert!(serde_json::from_str::<Legacy>(text).is_err());
        assert!(checked(text, legacy).result.is_err());
    }
}

#[test]
fn exact_work_and_metadata_capacity_limits_and_one_short_controls_are_distinct() {
    let text = r#"{"\u0077idth":8}"#;
    let baseline = checked(text, bitvec);
    assert!(baseline.result.is_ok());
    let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
    assert!(work > 0 && bytes >= 10);
    for (max_work, max_bytes, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(max_work as u64, max_bytes)?;
            bitvec(raw(text), control)
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
    let tuple = checked("[8]", bitvec);
    assert!(tuple.result.is_ok());
    assert_eq!(tuple.usage.charged_bytes, 0);
}

#[test]
fn every_success_and_duplicate_failure_callback_refuses_through_cleanup() {
    for (text, accepted) in [
        (r#"{"width":8}"#, true),
        (r#"{"width":8,"\u0077idth":8}"#, false),
    ] {
        let calls = Cell::new(0);
        let baseline = control::run(
            end(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| bitvec(raw(text), control),
        );
        assert_eq!(baseline.result.is_ok(), accepted);
        let total = calls.get();
        assert!(total > 5);
        for stop in 1..=total {
            calls.set(0);
            let outcome = control::run(
                end(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| bitvec(raw(text), control),
            );
            assert!(matches!(outcome.result, Err(TransportError::Refused)));
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(outcome.usage, baseline.usage);
            }
        }
    }
}

#[test]
fn original_deadline_and_caught_metadata_callback_panic_remain_terminal() {
    let outcome = control::run(
        Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
        &mut |_, _| -> bool { panic!("expired") },
        |control| bitvec(raw(r#"{"width":8}"#), control),
    );
    assert!(matches!(outcome.result, Err(TransportError::Deadline)));
    let calls = Cell::new(0);
    let outcome = control::run(
        end(),
        &mut |_, bytes| {
            calls.set(calls.get() + 1);
            assert!(bytes == 0, "metadata allocation");
            true
        },
        |control| {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                bitvec(raw(r#"{"width":8}"#), control)
            }));
            assert!(caught.is_err());
            let before = calls.get();
            assert!(matches!(
                bitvec(raw("[8]"), control),
                Err(TransportError::Refused)
            ));
            assert_eq!(calls.get(), before);
            Ok(())
        },
    );
    assert!(matches!(outcome.result, Err(TransportError::Refused)));
}

#[test]
fn consecutive_compound_reads_cannot_renew_metadata_storage_grants() {
    let text = r#"{"width":8}"#;
    let bytes = checked(text, bitvec).usage.charged_bytes;
    let outcome = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(u64::MAX, bytes)?;
        assert_eq!(bitvec(raw(text), control)?.width, 8);
        let error = bitvec(raw(text), control).unwrap_err();
        assert!(matches!(error, TransportError::Limit { .. }));
        let usage = control.usage;
        assert_eq!(bitvec(raw("[8]"), control).unwrap_err(), error);
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
}
