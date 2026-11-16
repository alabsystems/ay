// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only RawValue parsing stands for the caller's prior input admission.
//! This qualifies the typed Sort leaf, not a complete owning bundle decoder.

use super::read;
use crate::bundle::retained::{control, owned_values::RawSlice, TransportError, TransportOutcome};
use ay_core::{time::Instant, Sort};
use serde_json::value::RawValue;
use std::time::Duration;

const WORK: u64 = 1_000_000;
const STORAGE: usize = 1024 * 1024;
const MIXED: &str = r#"{"Array":[{"Seq":{"Uninterpreted":"\u03bb"}},{"BitVec":{"width":8}}]}"#;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn attempt(
    text: &str,
    work: u64,
    storage: usize,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> TransportOutcome<Sort> {
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    control::run(deadline, progress, |control| {
        control.constrain(work, storage)?;
        // Returned owner settlement belongs to the future enclosing decoder.
        read(RawSlice::from_raw(raw), control)
    })
}

fn decoded(text: &str) -> TransportOutcome<Sort> {
    attempt(text, WORK, STORAGE, end(), &mut |_, _| true)
}

fn accepts(text: &str) {
    let expected: Sort = serde_json::from_str(text).unwrap();
    let actual = decoded(text).result.unwrap();
    assert_eq!(actual, expected, "{text}");
    assert_eq!(
        serde_json::to_string(&actual).unwrap(),
        serde_json::to_string(&expected).unwrap(),
        "{text}"
    );
}

fn rejects(text: &str) {
    assert!(serde_json::from_str::<Sort>(text).is_err(), "{text}");
    let outcome = decoded(text);
    assert!(outcome.result.is_err(), "{text}");
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn every_canonical_sort_variant_matches_the_existing_owned_serde_type() {
    for text in [
        r#""Bool""#,
        r#""Int""#,
        r#""Real""#,
        r#"{"BitVec":{"width":8}}"#,
        r#"{"Array":{"index_sort":"Int","element_sort":"Bool"}}"#,
        r#""String""#,
        r#""RegLan""#,
        r#"{"FloatingPoint":[8,24]}"#,
        r#"{"Uninterpreted":"U"}"#,
        r#"{"Datatype":{"name":"D","constructors":[{"name":"C","fields":[{"name":"x","sort":"Bool"}]}]}}"#,
        r#"{"Seq":"Char"}"#,
        r#""Char""#,
        r#"{"FiniteDomain":["F",19]}"#,
        r#"{"TypeVar":"T"}"#,
    ] {
        accepts(text);
    }
}

#[test]
fn unit_variants_accept_null_object_form_but_not_other_payloads() {
    for name in ["Bool", "Int", "Real", "String", "RegLan", "Char"] {
        accepts(&format!(r#"{{"{name}":null}}"#));
        for payload in ["[]", "{}", "false", "0", r#""""#] {
            rejects(&format!(r#"{{"{name}":{payload}}}"#));
        }
    }
}

#[test]
fn every_helper_accepts_positional_arrays_and_reordered_object_fields() {
    for text in [
        r#"{"BitVec":[7]}"#,
        r#"{"Array":["Bool","Int"]}"#,
        r#"{"Array":{"element_sort":"Int","index_sort":"Bool"}}"#,
        r#"{"Datatype":["D",[["C",[["x",{"Seq":"Char"}]]]]]}"#,
        r#"{"Datatype":{"constructors":[{"fields":[{"sort":"Bool","name":"x"}],"name":"C"}],"name":"D"}}"#,
        r#"{"Datatype":["D",[{"fields":[["x",{"Array":["Int","Bool"]}]],"name":"C"}]]}"#,
        MIXED,
    ] {
        accepts(text);
    }
}

#[test]
fn escaped_variant_and_field_names_and_unicode_payloads_preserve_values() {
    for text in [
        r#""\u0042ool""#,
        r#"{"\u0042ool":null}"#,
        r#"{"Bit\u0056ec":{"w\u0069dth":8}}"#,
        r#"{"Array":{"index\u005fsort":"Int","element_sort":"Bool"}}"#,
        r#"{"Datatype":{"na\u006de":"λ","constructors":[{"name":"C\u0000","fields":[{"name":"\uD83D\uDE00","sort":"Char"}]}]}}"#,
        r#"{"Uninterpreted":"\"\\\/\b\f\n\r\t\u0000\uDBFF\uDFFF"}"#,
        r#"{"TypeVar":"é∑😀"}"#,
        r#"{"FiniteDomain":["\uD800\uDC00",1]}"#,
    ] {
        accepts(text);
    }
}

#[test]
fn transport_does_not_invent_semantic_width_cardinality_or_name_validation() {
    for text in [
        r#"{"BitVec":{"width":0}}"#,
        r#"{"BitVec":[4294967295]}"#,
        r#"{"FloatingPoint":[0,0]}"#,
        r#"{"FloatingPoint":[4294967295,4294967295]}"#,
        r#"{"FiniteDomain":["",0]}"#,
        r#"{"FiniteDomain":["F",18446744073709551615]}"#,
        r#"{"Uninterpreted":""}"#,
        r#"{"TypeVar":""}"#,
        r#"{"Datatype":["",[]]}"#,
        r#"{"Datatype":["D",[["C",[["x","Bool"],["x","Int"]]],["C",[]]]]}"#,
    ] {
        accepts(text);
    }
}

#[test]
fn enum_shape_numeric_identifiers_and_newtype_shortcuts_are_rejected() {
    for text in [
        "null",
        "true",
        "0",
        "13",
        "14",
        "-1",
        "[]",
        "{}",
        r#""0""#,
        r#"{"0":null}"#,
        r#""bool""#,
        r#""Unknown""#,
        r#"["Bool"]"#,
        r#"{"Bool":null,"Int":null}"#,
        r#"{"Bool":null,"Bool":null}"#,
        r#""BitVec""#,
        r#""Array""#,
        r#""FloatingPoint""#,
        r#""Uninterpreted""#,
        r#""Datatype""#,
        r#""Seq""#,
        r#""FiniteDomain""#,
        r#""TypeVar""#,
        r#"{"BitVec":8}"#,
        r#"{"Array":null}"#,
        r#"{"Seq":null}"#,
        r#"{"Seq":["Bool"]}"#,
        r#"{"Uninterpreted":["U"]}"#,
        r#"{"TypeVar":false}"#,
        r#"{"FloatingPoint":{"0":8,"1":24}}"#,
        r#"{"FiniteDomain":{"name":"F","size":1}}"#,
    ] {
        rejects(text);
    }
}

#[test]
fn helper_sequences_and_tuple_variants_require_exact_lengths_and_types() {
    for text in [
        r#"{"BitVec":[]}"#,
        r#"{"BitVec":[8,9]}"#,
        r#"{"Array":[]}"#,
        r#"{"Array":["Bool"]}"#,
        r#"{"Array":["Bool","Int","Real"]}"#,
        r#"{"FloatingPoint":[]}"#,
        r#"{"FloatingPoint":[8]}"#,
        r#"{"FloatingPoint":[8,24,1]}"#,
        r#"{"FiniteDomain":["F"]}"#,
        r#"{"FiniteDomain":["F",1,2]}"#,
        r#"{"Datatype":[]}"#,
        r#"{"Datatype":["D"]}"#,
        r#"{"Datatype":["D",[],0]}"#,
        r#"{"Datatype":["D",[[]]]}"#,
        r#"{"Datatype":["D",[["C"]]]}"#,
        r#"{"Datatype":["D",[["C",[],0]]]}"#,
        r#"{"Datatype":["D",[["C",[[]]]]]}"#,
        r#"{"Datatype":["D",[["C",[["x"]]]]]}"#,
        r#"{"Datatype":["D",[["C",[["x","Bool",0]]]]]}"#,
        r#"{"Datatype":["D",null]}"#,
        r#"{"Datatype":["D",[["C",null]]]}"#,
        r#"{"Datatype":["D",[["C",[[null,"Bool"]]]]]}"#,
    ] {
        rejects(text);
    }
}

#[test]
fn helper_objects_reject_missing_unknown_duplicate_and_escaped_duplicate_fields() {
    for text in [
        r#"{"BitVec":{}}"#,
        r#"{"BitVec":{"0":8}}"#,
        r#"{"BitVec":{"width":8,"extra":0}}"#,
        r#"{"BitVec":{"width":8,"w\u0069dth":9}}"#,
        r#"{"Array":{"index_sort":"Bool"}}"#,
        r#"{"Array":{"element_sort":"Bool"}}"#,
        r#"{"Array":{"index_sort":"Bool","element_sort":"Int","extra":0}}"#,
        r#"{"Array":{"index_sort":"Bool","index_sort":"Int","element_sort":"Int"}}"#,
        r#"{"Datatype":{"name":"D"}}"#,
        r#"{"Datatype":{"constructors":[]}}"#,
        r#"{"Datatype":{"name":"D","constructors":[],"extra":0}}"#,
        r#"{"Datatype":{"name":"D","na\u006de":"E","constructors":[]}}"#,
        r#"{"Datatype":["D",[{"name":"C"}]]}"#,
        r#"{"Datatype":["D",[{"fields":[]}]]}"#,
        r#"{"Datatype":["D",[{"name":"C","fields":[],"extra":0}]]}"#,
        r#"{"Datatype":["D",[{"name":"C","fields":[],"fields":[]}]]}"#,
        r#"{"Datatype":["D",[["C",[{"name":"x"}]]]]}"#,
        r#"{"Datatype":["D",[["C",[{"sort":"Bool"}]]]]}"#,
        r#"{"Datatype":["D",[["C",[{"name":"x","sort":"Bool","extra":0}]]]]}"#,
        r#"{"Datatype":["D",[["C",[{"name":"x","sort":"Bool","sort":"Int"}]]]]}"#,
    ] {
        rejects(text);
    }
}

#[test]
fn scalar_ranges_and_invalid_unicode_refuse_like_serde() {
    for number in ["-0", "-1", "1.0", "1e0", "4294967296", "null", r#""8""#] {
        rejects(&format!(r#"{{"BitVec":{{"width":{number}}}}}"#));
        rejects(&format!(r#"{{"FloatingPoint":[{number},24]}}"#));
        rejects(&format!(r#"{{"FloatingPoint":[8,{number}]}}"#));
    }
    for number in ["-0", "-1", "1.0", "1e0", "18446744073709551616", "null"] {
        rejects(&format!(r#"{{"FiniteDomain":["F",{number}]}}"#));
    }
    for text in [
        r#""\uD800""#,
        r#"{"\uDC00":null}"#,
        r#"{"BitVec":{"\uD800":8}}"#,
        r#"{"Uninterpreted":"\uD800"}"#,
        r#"{"TypeVar":"\uDC00"}"#,
        r#"{"FiniteDomain":["\uD800x",1]}"#,
        r#"{"Datatype":["\uD800",[]]}"#,
    ] {
        rejects(text);
    }
}

#[test]
fn mixed_recursive_sorts_preserve_every_nested_owner_value() {
    let mut text = r#"{"Datatype":["D",[["C",[["value",{"BitVec":[17]}]]]]]}"#.to_owned();
    for depth in 0..12 {
        accepts(&text);
        text = if depth % 2 == 0 {
            format!(r#"{{"Seq":{text}}}"#)
        } else {
            format!(r#"{{"Array":["Int",{text}]}}"#)
        };
    }
}

#[test]
fn independent_sort_entry_also_refuses_excessive_recursive_depth() {
    // Full bundle input admission rejects this excess before typed decoding.
    // Exercise the leaf's defensive recursion cap independently as well.
    let mut text = r#""Bool""#.to_owned();
    for _ in 0..crate::bundle::retained::lexical::OUTER_DEPTH {
        text = format!(r#"{{"Seq":{text}}}"#);
    }
    accepts(&text);
    text = format!(r#"{{"Seq":{text}}}"#);
    assert!(serde_json::from_str::<Sort>(&text).is_err());
    let outcome = decoded(&text);
    assert!(matches!(
        outcome.result,
        Err(TransportError::Limit {
            resource: "owning sort depth",
            ..
        })
    ));
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn exact_work_and_storage_succeed_and_one_short_or_zero_refuses() {
    let full = decoded(MIXED);
    assert!(full.result.is_ok());
    let work = full.usage.charged_work as u64;
    let bytes = full.usage.charged_bytes;
    assert!(work > 1 && bytes > 1);
    let exact = attempt(MIXED, work, bytes, end(), &mut |_, _| true);
    assert_eq!(exact.result, full.result);
    assert_eq!(exact.usage.charged_work, full.usage.charged_work);
    assert_eq!(exact.usage.charged_bytes, bytes);
    for (work, bytes) in [(work - 1, bytes), (0, bytes), (work, bytes - 1), (work, 0)] {
        let short = attempt(MIXED, work, bytes, end(), &mut |_, _| true);
        assert!(matches!(short.result, Err(TransportError::Limit { .. })));
        assert_eq!(short.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn every_success_and_partial_failure_callback_can_refuse_without_publication() {
    for text in [MIXED, r#"{"Array":[{"Uninterpreted":"owned"},null]}"#] {
        let mut total = 0;
        let baseline = attempt(text, WORK, STORAGE, end(), &mut |_, _| {
            total += 1;
            true
        });
        assert_eq!(
            baseline.result.is_ok(),
            serde_json::from_str::<Sort>(text).is_ok()
        );
        assert!(total > 3);
        for stop in 1..=total {
            let mut calls = 0;
            let outcome = attempt(text, WORK, STORAGE, end(), &mut |_, _| {
                calls += 1;
                calls != stop
            });
            assert_eq!(outcome.result, Err(TransportError::Refused));
            assert_eq!(calls, stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(outcome.usage.charged_work, baseline.usage.charged_work);
                assert_eq!(outcome.usage.charged_bytes, baseline.usage.charged_bytes);
            }
        }
    }
}

#[test]
fn expired_original_deadline_precedes_valid_and_invalid_sort_work() {
    for text in [MIXED, "null", r#"{"Datatype":{}}"#] {
        let mut calls = 0;
        let outcome = attempt(
            text,
            WORK,
            STORAGE,
            Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
            &mut |_, _| {
                calls += 1;
                true
            },
        );
        assert_eq!(outcome.result, Err(TransportError::Deadline));
        assert_eq!(calls, 0);
        assert_eq!(outcome.usage.charged_work, 0);
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn dropping_a_sort_does_not_renew_shared_work_or_storage_credit() {
    let full = decoded(MIXED);
    assert!(full.result.is_ok());
    let raw: &RawValue = serde_json::from_str(MIXED).unwrap();
    for (work, bytes) in [
        (full.usage.charged_work as u64, STORAGE),
        (WORK, full.usage.charged_bytes),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(work, bytes)?;
            let first = read(RawSlice::from_raw(raw), control)?;
            assert_eq!(Some(&first), full.result.as_ref().ok());
            drop(first);
            let error = read(RawSlice::from_raw(raw), control).unwrap_err();
            assert!(matches!(error, TransportError::Limit { .. }));
            let usage = control.usage;
            assert_eq!(read(RawSlice::from_raw(raw), control), Err(error));
            assert_eq!(control.usage, usage);
            Ok(()) // Catching a refusal cannot restore publication authority.
        });
        assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
    }
}

#[test]
fn malformed_sort_failure_cannot_fall_back_to_a_valid_sort_on_the_same_control() {
    let invalid: &RawValue = serde_json::from_str(r#"{"Array":["Bool",null]}"#).unwrap();
    let valid: &RawValue = serde_json::from_str(MIXED).unwrap();
    let outcome = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(WORK, STORAGE)?;
        let error = read(RawSlice::from_raw(invalid), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(read(RawSlice::from_raw(valid), control), Err(error));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(outcome.result.is_err());
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}
