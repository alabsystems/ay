// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Leaf parity and controls, not semantic annotation or complete bundle acceptance.
//! RawValue parsing here stands for prior whole-input/depth admission.

use super::*;
use crate::bundle::retained::{control, RawValue, TransportOutcome};
use ay_core::time::Instant;
use serde::{de::DeserializeOwned, Serialize};
use std::{cell::Cell, fmt::Debug, time::Duration};

const MIXED: &str =
    r#"{"CuttingPlane":{"farkas":{"coefficients":[[2,4],[-6,-8],[0,-7],[2,4]]},"divisor":-3}}"#;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn raw(text: &str) -> RawSlice<'_> {
    RawSlice::from_raw(serde_json::from_str::<&RawValue>(text).unwrap())
}

fn checked<'a, T>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> TransportOutcome<T> {
    control::run(deadline(), &mut |_, _| true, |control| {
        decode(raw(text), control)
    })
}

fn accepts<'a, T: DeserializeOwned + Serialize + PartialEq + Debug>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) {
    let expected: T = serde_json::from_str(text).unwrap();
    let actual = checked(text, decode).result.unwrap();
    assert_eq!(actual, expected, "{text}");
    // Rational equality alone would hide reduction or denominator-sign changes.
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(&expected).unwrap(),
        "{text}"
    );
}

fn rejects<'a, T: DeserializeOwned>(
    text: &'a str,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) {
    assert!(serde_json::from_str::<T>(text).is_err(), "{text}");
    let outcome = checked(text, decode);
    assert!(outcome.result.is_err(), "{text}");
    assert_eq!(outcome.usage.returned_owned_bytes, 0);
}

#[test]
fn farkas_map_and_exact_sequence_preserve_raw_coefficients_and_extremes() {
    for text in [
        r#"{"coefficients":[]}"#,
        "[[]]",
        r#"{"coefficients":[[2,4],[-6,-8],[0,-7],[2,4]]}"#,
        "[[[2,4],[-6,-8],[0,-7],[2,4]]]",
        r#"{"coefficients":[[-9223372036854775808,-1],[9223372036854775807,-9223372036854775808]]}"#,
        r#"{"coeff\u0069cients":[[1,2]]}"#,
    ] {
        accepts(text, farkas);
    }
}

#[test]
fn cutting_plane_shapes_keep_invalid_semantic_divisors_for_later_validation() {
    for text in [
        r#"{"farkas":{"coefficients":[[2,4]]},"divisor":3}"#,
        r#"{"divisor":0,"farkas":[[[1,-2]]]}"#,
        r#"{"div\u0069sor":-3,"far\u006bas":{"coefficients":[]}}"#,
        "[[[[2,4],[-6,-8]]],0]",
        r#"[{"coefficients":[[0,-7]]},-9223372036854775808]"#,
        r#"{"farkas":{"coefficients":[]},"divisor":9223372036854775807}"#,
    ] {
        accepts(text, cutting_plane);
        accepts(&format!(r#"{{"CuttingPlane":{text}}}"#), lia);
    }
}

#[test]
fn all_four_lia_variants_accept_only_their_legacy_enum_forms() {
    for variant in ["BoundsGap", "Divisibility", "LinearIdentity"] {
        accepts(&format!("\"{variant}\""), lia);
        accepts(&format!(r#"{{"{variant}":null}}"#), lia);
        for payload in ["[]", "{}", "0", "false", r#""""#] {
            rejects(&format!(r#"{{"{variant}":{payload}}}"#), lia);
        }
    }
    for text in [
        MIXED,
        r#""Bounds\u0047ap""#,
        r#"{"Divis\u0069bility":null}"#,
        r#"{"Cutting\u0050lane":[[[]],1]}"#,
    ] {
        accepts(text, lia);
    }
}

#[test]
fn farkas_missing_duplicate_unknown_null_and_malformed_rational_fields_refuse() {
    for text in [
        "null",
        "0",
        "[]",
        "{}",
        r#"{"coefficients":null}"#,
        r#"{"coefficients":[],"extra":0}"#,
        r#"{"coefficients":[],"coefficients":[]}"#,
        r#"{"coefficients":[],"coeff\u0069cients":[]}"#,
        "[[],0]",
        r#"{"coefficients":[null]}"#,
        r#"{"coefficients":[1]}"#,
        r#"{"coefficients":[[1]]}"#,
        r#"{"coefficients":[[1,2,3]]}"#,
        r#"{"coefficients":[[1,0]]}"#,
        r#"{"coefficients":[[1,-0]]}"#,
        r#"{"coefficients":[[1,2.0]]}"#,
        r#"{"coefficients":[[1e0,2]]}"#,
        r#"{"coefficients":[["1",2]]}"#,
        r#"{"coefficients":[[9223372036854775808,1]]}"#,
        r#"{"coefficients":[[1,-9223372036854775809]]}"#,
    ] {
        rejects(text, farkas);
    }
}

#[test]
fn cutting_plane_requires_both_unique_known_fields_and_exact_integer_divisor() {
    for text in [
        "null",
        "[]",
        "{}",
        r#"{"farkas":{"coefficients":[]}}"#,
        r#"{"divisor":1}"#,
        r#"{"farkas":null,"divisor":1}"#,
        r#"{"farkas":{},"divisor":1}"#,
        r#"{"farkas":{"coefficients":[]},"divisor":null}"#,
        r#"{"farkas":{"coefficients":[]},"divisor":1,"unknown":0}"#,
        r#"{"farkas":{"coefficients":[]},"divisor":1,"divisor":2}"#,
        r#"{"farkas":{"coefficients":[]},"farkas":{"coefficients":[]},"divisor":1}"#,
        "[[[]]]",
        "[[[]],1,0]",
        "[[[]],-0]",
        "[[[]],1.0]",
        "[[[]],1e0]",
        "[[[]],true]",
        "[[[]],9223372036854775808]",
        "[[[]],-9223372036854775809]",
    ] {
        rejects(text, cutting_plane);
        rejects(&format!(r#"{{"CuttingPlane":{text}}}"#), lia);
    }
}

#[test]
fn lia_unknown_duplicate_nullable_numeric_and_newtype_shortcuts_refuse() {
    for text in [
        "null",
        "true",
        "0",
        "[]",
        "{}",
        r#""0""#,
        r#"{"0":null}"#,
        r#""Unknown""#,
        r#"{"Unknown":null}"#,
        r#""CuttingPlane""#,
        r#"{"CuttingPlane":null}"#,
        r#"{"BoundsGap":null,"BoundsGap":null}"#,
        r#"{"BoundsGap":null,"LinearIdentity":null}"#,
        r#"["BoundsGap"]"#,
        r#"{"LinearIdentity":0}"#,
    ] {
        rejects(text, lia);
    }
}

#[test]
fn exact_short_and_zero_limits_cover_coefficient_ownership() {
    let baseline = checked(MIXED, lia);
    assert!(baseline.result.is_ok());
    let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
    assert!(work > 0 && bytes >= 4 * size_of::<num_rational::Rational64>());
    for (max_work, max_bytes, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let outcome = control::run(deadline(), &mut |_, _| true, |control| {
            control.constrain(max_work as u64, max_bytes)?;
            lia(raw(MIXED), control)
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if !accepted {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
    let empty = checked("[[]]", farkas);
    assert!(empty.result.unwrap().coefficients.is_empty());
    assert_eq!(empty.usage.charged_bytes, 0);
}

#[test]
fn two_annotations_share_cumulative_limits_without_releasing_prior_owners() {
    let baseline = checked(MIXED, lia);
    assert!(baseline.result.is_ok());
    let (work, bytes) = (baseline.usage.charged_work, baseline.usage.charged_bytes);
    for (max_work, max_bytes, accepted) in [
        (work * 2, bytes * 2, true),
        (work * 2 - 1, bytes * 2, false),
        (work * 2, bytes * 2 - 1, false),
    ] {
        let outcome = control::run(deadline(), &mut |_, _| true, |control| {
            control.constrain(max_work as u64, max_bytes)?;
            let first = lia(raw(MIXED), control)?;
            let second = lia(raw(MIXED), control)?;
            Ok((first, second))
        });
        assert_eq!(outcome.result.is_ok(), accepted);
        if accepted {
            assert_eq!(outcome.usage.charged_work, work * 2);
            assert_eq!(outcome.usage.charged_bytes, bytes * 2);
        } else {
            assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        }
    }
}

#[test]
fn every_success_and_partial_error_poll_including_cleanup_is_terminal() {
    for text in [
        r#""BoundsGap""#,
        r#"{"Divisibility":null}"#,
        r#""LinearIdentity""#,
        MIXED,
        r#"{"CuttingPlane":{"farkas":{"coefficients":[[1,2],[3,0]]},"divisor":1}}"#,
    ] {
        let calls = Cell::new(0);
        let baseline = control::run(
            deadline(),
            &mut |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            |control| lia(raw(text), control),
        );
        assert_eq!(
            baseline.result.is_ok(),
            serde_json::from_str::<LiaAnnotation>(text).is_ok()
        );
        let total = calls.get();
        assert!(total > 2);
        for stop in 1..=total {
            calls.set(0);
            let outcome = control::run(
                deadline(),
                &mut |_, _| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                },
                |control| lia(raw(text), control),
            );
            assert_eq!(outcome.result, Err(TransportError::Refused));
            assert_eq!(calls.get(), stop);
            assert_eq!(outcome.usage.returned_owned_bytes, 0);
            if stop == total {
                assert_eq!(outcome.usage, baseline.usage);
            }
        }
    }
}

#[test]
fn original_deadline_and_sticky_decode_error_prevent_later_acceptance() {
    let expired = control::run(
        Instant::now() - Duration::from_secs(1),
        &mut |_, _| -> bool { panic!("expired before progress") },
        |control| lia(raw(MIXED), control),
    );
    assert_eq!(expired.result, Err(TransportError::Deadline));
    assert_eq!(expired.usage.charged_work, 0);
    assert_eq!(expired.usage.charged_bytes, 0);
    let sticky = control::run(deadline(), &mut |_, _| true, |control| {
        let error = farkas(raw(r#"{"coefficients":[[1,2],[3,0]]}"#), control).unwrap_err();
        let usage = control.usage;
        assert_eq!(lia(raw(MIXED), control), Err(error));
        assert_eq!(control.usage, usage);
        Ok(())
    });
    assert!(matches!(
        sticky.result,
        Err(TransportError::InvalidShape(_))
    ));
}
