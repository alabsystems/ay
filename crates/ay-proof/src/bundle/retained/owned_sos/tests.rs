// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Leaf parity under test-only prior RawValue admission, not theorem acceptance.

use super::*;
use crate::bundle::retained::{control, RawValue, TransportOutcome};
use ay_core::{time::Instant, ProofStep};
use serde::{de::DeserializeOwned, Serialize};
use std::{cell::Cell, fmt::Debug, time::Duration};

const ZERO: &str = r#"{"numerator":[0,[]],"denominator":[1,[1]]}"#;
const SAMPLE: &str = r#"[[],[],[],[[1,[2]],[1,[3]]]]"#;

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
fn array(item: &str, count: usize) -> String {
    format!("[{}]", vec![item; count].join(","))
}
fn document(basis: &str, gram: &str, terms: &str, rhs: &str) -> String {
    format!(r#"{{"basis":{basis},"gram":{gram},"terms":{terms},"rhs":{rhs}}}"#)
}
fn parity<'a, T: DeserializeOwned + Serialize + PartialEq + Debug>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) {
    let expected = serde_json::from_str::<T>(text);
    let actual = checked(text, decode).result;
    assert_eq!(actual.is_ok(), expected.is_ok(), "{text}");
    if let (Ok(actual), Ok(expected)) = (actual, expected) {
        assert_eq!(actual, expected);
        assert_eq!(
            serde_json::to_vec(&actual).unwrap(),
            serde_json::to_vec(&expected).unwrap()
        );
    }
}

#[test]
fn certificate_map_sequence_and_escaped_fields_match_core_wire_values() {
    let term = format!(r#"{{"origin":{{"Product":{{"left":0,"right":1}}}},"multiplier":{ZERO}}}"#);
    let map = document(
        "[[],[3],[3,4]]",
        &array(&array(ZERO, 3), 3),
        &array(&term, 1),
        ZERO,
    );
    parity(&map, certificate);
    parity(&map.replace("\"basis\"", r#""ba\u0073is""#), certificate);
    for text in [SAMPLE, r#"[[[]],[[[[0,[]],[1,[1]]]]],[],[[0,[]],[1,[1]]]]"#] {
        parity(text, certificate);
    }
}

#[test]
fn transport_preserves_zero_negative_denominators_and_noncanonical_semantic_shapes() {
    for text in [
        r#"[[1,[2]],[0,[]]]"#,
        r#"[[1,[2]],[-1,[4]]]"#,
        r#"[[1,[2]],[1,[4]]]"#,
    ] {
        parity(text, rational);
        let value = checked(text, rational).result.unwrap();
        if text.contains("[0,[]]") || text.contains("[-1,[4]]") {
            assert!(value.validate_shape().is_err());
        }
    }
    for text in [
        document("[]", "[]", "[]", ZERO),
        document("[[2,1],[2,1]]", "[[],[]]", "[]", ZERO),
        document("[[]]", "[]", "[]", ZERO),
    ] {
        parity(&text, certificate);
        assert!(checked(&text, certificate)
            .result
            .unwrap()
            .validate_shape()
            .is_err());
    }
    let text = document(
        "[[]]",
        &array(&array(ZERO, 1), 1),
        &format!(
            r#"[{{"origin":{{"ClauseLiteral":{{"position":4294967295}}}},"multiplier":{ZERO}}}]"#
        ),
        ZERO,
    );
    parity(&text, certificate);
    assert!(checked(&text, certificate)
        .result
        .unwrap()
        .validate_shape()
        .is_err());
}

#[test]
fn canonical_integer_signs_and_exact_32_word_boundary_match_sos_not_general_bigint() {
    let full = array("4294967295", 32);
    for numer in [
        "[0,[]]".to_owned(),
        "[1,[1]]".to_owned(),
        "[-1,[0,1]]".to_owned(),
        format!("[1,{full}]"),
        format!("[-1,{full}]"),
    ] {
        parity(&format!("[{numer},[1,[1]]]"), rational);
    }
    for numer in [
        "[1,[]]".to_owned(),
        "[-1,[]]".to_owned(),
        "[0,[1]]".to_owned(),
        "[0,[0]]".to_owned(),
        "[1,[1,0]]".to_owned(),
        "[-1,[0,0]]".to_owned(),
        "[2,[1]]".to_owned(),
        "[-0,[]]".to_owned(),
        "[1,[4294967296]]".to_owned(),
        "[1,[-1]]".to_owned(),
        "[1,[1.0]]".to_owned(),
        "[1,[null]]".to_owned(),
        format!("[1,{}]", array("1", 33)),
    ] {
        let text = format!("[{numer},[1,[1]]]");
        assert!(serde_json::from_str::<NraSosRational>(&text).is_err());
        assert!(checked(&text, rational).result.is_err());
    }
}

#[test]
fn canonical_prepass_and_second_bigint_pass_are_both_charged_without_refund() {
    let text = "[1,[7]]";
    let ordinary = checked(text, owned_bignum::bigint);
    let strict = checked(text, integer);
    assert_eq!(strict.result, ordinary.result);
    assert_eq!(
        strict.usage.charged_bytes,
        ordinary.usage.charged_bytes + size_of::<u32>()
    );
    assert!(strict.usage.charged_work > ordinary.usage.charged_work);
    let result = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(u64::MAX, strict.usage.charged_bytes - 1)?;
        integer(raw(text), control)
    });
    assert!(matches!(result.result, Err(TransportError::Limit { .. })));
    let bad = checked("[2,[1]]", integer);
    assert!(matches!(
        bad.result,
        Err(TransportError::InvalidShape("invalid SOS integer sign"))
    ));
    assert_eq!(bad.usage.charged_bytes, size_of::<u32>()); // bounded tuple parsed before sign check
}

#[test]
fn exact_sos_outer_inner_and_clause_wire_bounds_are_accepted() {
    let full_basis = array("[0,1]", 45);
    let full_gram = array(&array(ZERO, 45), 45);
    let term = format!(r#"[{{"Product":[0,1]}},{ZERO}]"#);
    let full_terms = array(&term, 400);
    assert_eq!(checked(&full_basis, basis).result.unwrap().len(), 45);
    assert_eq!(checked(&full_gram, gram).result.unwrap().len(), 45);
    assert_eq!(checked(&full_terms, terms).result.unwrap().len(), 400);
    parity(&document(&full_basis, "[]", "[]", ZERO), certificate);
    parity(&document("[]", &full_gram, "[]", ZERO), certificate);
    parity(&document("[]", "[]", &full_terms, ZERO), certificate);
    let full_clause = array("4294967295", 1024);
    let actual = checked(&full_clause, clause).result.unwrap();
    let proof = format!(
        r#"{{"NraSos":{{"clause":{full_clause},"certificate":{}}}}}"#,
        document("[]", "[]", "[]", ZERO)
    );
    let expected: ProofStep = serde_json::from_str(&proof).unwrap();
    if let ProofStep::NraSos { clause, .. } = expected {
        assert_eq!(actual, clause);
    } else {
        panic!("wrong variant");
    }
}

#[test]
fn excess_rows_terms_words_and_clause_refuse_before_any_child_owner() {
    macro_rules! no_owner {
        ($text:expr,$decode:path) => {{
            let text = $text;
            let result = checked(&text, $decode);
            assert!(matches!(
                result.result,
                Err(TransportError::Limit {
                    resource: "owned vector elements",
                    ..
                })
            ));
            assert_eq!(result.usage.charged_bytes, 0);
        }};
    }
    // Invalid children deliberately ensure the count refusal wins BEFORE a
    // typed child decoder (or its buffers) can run.
    no_owner!(array("null", 46), basis);
    no_owner!(array("null", 46), gram);
    no_owner!(array("null", 401), terms);
    no_owner!(array("null", 1025), clause);
    no_owner!(format!("[1,{}]", array("null", 33)), integer);
    let too_wide = checked("[[0,1,2]]", basis);
    assert!(matches!(too_wide.result, Err(TransportError::Limit { .. })));
    assert_eq!(too_wide.usage.charged_bytes, size_of::<Vec<TermId>>());
    let too_wide = checked(&array(&array("null", 46), 1), gram);
    assert!(matches!(too_wide.result, Err(TransportError::Limit { .. })));
    assert_eq!(
        too_wide.usage.charged_bytes,
        size_of::<Vec<NraSosRational>>()
    );
}

#[test]
fn origin_map_sequence_and_u32_positions_match_transport_not_source_binding() {
    for text in [
        r#"{"ClauseLiteral":{"position":4294967295}}"#,
        r#"{"ClauseLiteral":[0]}"#,
        r#"{"Product":{"right":0,"left":4294967295}}"#,
        r#"{"Product":[0,4294967295]}"#,
        r#"{"Pro\u0064uct":{"l\u0065ft":1,"right":2}}"#,
        r#""ClauseLiteral""#,
        r#"{"Product":[1]}"#,
        r#"{"Product":[1,2,3]}"#,
        r#"{"ClauseLiteral":{"position":1,"position":2}}"#,
        r#"{"Product":{"left":1,"right":2,"extra":0}}"#,
        r#"{"ClauseLiteral":{"position":-0}}"#,
        r#"{"ClauseLiteral":{"position":4294967296}}"#,
    ] {
        parity(text, origin);
    }
}

#[test]
fn certificate_and_rational_missing_unknown_duplicate_null_fields_refuse() {
    for text in [
        "null",
        "{}",
        "[]",
        r#"{"basis":[],"gram":[],"terms":[]}"#,
        r#"[[],[],[],[[0,[]],[1,[1]]],0]"#,
    ] {
        assert!(serde_json::from_str::<NraSosCertificate>(text).is_err());
        assert!(checked(text, certificate).result.is_err());
    }
    let valid = document("[]", "[]", "[]", ZERO);
    for text in [
        valid.replace("\"basis\":[]", "\"basis\":null"),
        valid.replacen('{', "{\"unknown\":0,", 1),
        valid.replacen('{', "{\"basis\":[],", 1),
    ] {
        assert!(serde_json::from_str::<NraSosCertificate>(&text).is_err());
        assert!(checked(&text, certificate).result.is_err());
    }
    for text in [
        r#"{"numerator":[0,[]]}"#,
        r#"{"denominator":[1,[1]]}"#,
        r#"{"numerator":[0,[]],"denominator":[1,[1]],"extra":0}"#,
        r#"{"numerator":[0,[]],"numerator":[0,[]],"denominator":[1,[1]]}"#,
        "[]",
        "[[0,[]]]",
        "[[0,[]],[1,[1]],0]",
    ] {
        assert!(serde_json::from_str::<NraSosRational>(text).is_err());
        assert!(checked(text, rational).result.is_err());
    }
}

#[test]
fn exact_work_bytes_and_consecutive_certificate_grants_remain_cumulative() {
    let full = checked(SAMPLE, certificate);
    assert!(full.result.is_ok());
    let (work, bytes) = (full.usage.charged_work, full.usage.charged_bytes);
    for (w, b, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let result = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(w as u64, b)?;
            certificate(raw(SAMPLE), control)
        });
        assert_eq!(result.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(result.result, Err(TransportError::Limit { .. })));
        }
    }
    let result = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(work as u64, bytes)?;
        drop(certificate(raw(SAMPLE), control)?);
        certificate(raw(SAMPLE), control)
    });
    assert!(matches!(result.result, Err(TransportError::Limit { .. })));
}

#[test]
fn every_success_and_partial_integer_error_poll_refuses_after_cleanup() {
    for (text, accepted) in [(SAMPLE, true), ("[[],[],[],[[1,[2]],[1,[0]]]]", false)] {
        let calls = Cell::new(0);
        let full = control::run(
            end(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| certificate(raw(text), control),
        );
        assert_eq!(full.result.is_ok(), accepted);
        let total = calls.get();
        for stop in 1..=total {
            calls.set(0);
            let result = control::run(
                end(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| certificate(raw(text), control),
            );
            assert_eq!(result.result, Err(TransportError::Refused));
            assert_eq!(calls.get(), stop);
            assert_eq!(result.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(result.usage, full.usage);
            }
        }
    }
}

#[test]
fn original_deadline_and_canonical_failure_cannot_be_retried_or_published() {
    let expired = control::run(
        Instant::now() - Duration::from_secs(1),
        &mut |_, _| -> bool { panic!("expired") },
        |control| certificate(raw(SAMPLE), control),
    );
    assert_eq!(expired.result, Err(TransportError::Deadline));
    let result = control::run(end(), &mut |_, _| true, |control| {
        let error = integer(raw("[1,[1,0]]"), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(certificate(raw(SAMPLE), control), Err(error));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(
        result.result,
        Err(TransportError::InvalidShape(
            "noncanonical SOS integer limbs"
        ))
    ));
}
