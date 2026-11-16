// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! RawValue parsing here is a test-only stand-in for prior input admission.
//! These tests qualify the leaf contract, not the complete owning decoder.

use super::*;
use crate::bundle::retained::{control, TransportOutcome};
use ay_core::time::Instant;
use serde_json::value::RawValue;
use std::{mem::size_of, time::Duration};

const WORK: u64 = 1_000_000;
const STORAGE: usize = 1024 * 1024;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn attempt(
    text: &str,
    work: u64,
    storage: usize,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> TransportOutcome<String> {
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    control::run(deadline, progress, |control| {
        control.constrain(work, storage)?;
        let value = owned_string(RawSlice::from_raw(raw), control)?;
        // The operation owner, not the leaf, records returned owner capacity.
        control.usage.returned_owned_bytes = value.capacity();
        Ok(value)
    })
}

fn decoded(text: &str) -> TransportOutcome<String> {
    attempt(text, WORK, STORAGE, end(), &mut |_, _| true)
}

#[test]
fn literal_unicode_all_escapes_and_surrogate_pairs_match_serde_string() {
    for text in [
        "\"\"",
        r#""plain ASCII""#,
        "\"λ∑😀é\"",
        r#""\"\\\/\b\f\n\r\t""#,
        r#""\u0000\u001f\u007f\u0080\u07FF\u0800\uD7FF\uE000\uFFFF""#,
        r#""\uD800\uDC00\uDBFF\uDFFF\uD83D\uDE00""#,
    ] {
        let expected: String = serde_json::from_str(text).unwrap();
        let outcome = decoded(text);
        let actual = outcome.result.unwrap();
        assert_eq!(actual, expected);
        assert_eq!(outcome.usage.charged_bytes, actual.capacity());
        assert_eq!(outcome.usage.returned_owned_bytes, actual.capacity());
    }
    assert_eq!(decoded(r#""\u0000""#).result.unwrap().as_bytes(), &[0]);
}

#[test]
fn raw_json_surrogate_tokens_refuse_where_serde_string_refuses() {
    // RawValue skips escaped code units without constructing a Rust String;
    // these are valid raw tokens but invalid scalar-value string contents.
    for text in [
        r#""\uD800""#,
        r#""\uDBFF""#,
        r#""\uDC00""#,
        r#""\uDFFF""#,
        r#""\uD800x""#,
        r#""\uD800\u0041""#,
        r#""\uD800\n""#,
        r#""\uDC00\uD800""#,
    ] {
        assert!(serde_json::from_str::<String>(text).is_err());
        let outcome = decoded(text);
        assert_eq!(outcome.result, Err(TransportError::InvalidJson));
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn admitted_non_string_json_refuses_without_allocating_output() {
    for text in ["null", "false", "true", "0", "1.0", "[]", "{}"] {
        assert!(serde_json::from_str::<String>(text).is_err());
        let outcome = decoded(text);
        assert_eq!(
            outcome.result,
            Err(TransportError::InvalidShape("expected a string"))
        );
        assert_eq!(outcome.usage.charged_bytes, 0);
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn encoded_content_is_reserved_before_decode_with_exact_and_short_storage_controls() {
    let text = r#""\u0061\u0062""#;
    let mut reservations = Vec::new();
    let full = attempt(text, WORK, STORAGE, end(), &mut |_, bytes| {
        if bytes > 0 {
            reservations.push(bytes);
        }
        true
    });
    assert_eq!(full.result.as_deref(), Ok("ab"));
    assert_eq!(reservations[0], text.len() - 2);
    let capacity = full.result.unwrap().capacity();
    assert_eq!(full.usage.charged_bytes, capacity);
    assert!(capacity >= text.len() - 2);
    assert_eq!(
        attempt(text, WORK, capacity, end(), &mut |_, _| true)
            .result
            .as_deref(),
        Ok("ab")
    );
    for limit in [capacity - 1, text.len() - 3, 2] {
        let short = attempt(text, WORK, limit, end(), &mut |_, _| true);
        assert!(matches!(short.result, Err(TransportError::Limit { .. })));
        assert_eq!(short.usage.returned_owned_bytes, 0);
    }
    let empty = attempt("\"\"", WORK, 0, end(), &mut |_, _| true);
    assert_eq!(empty.result.as_deref(), Ok(""));
    assert_eq!(empty.usage.charged_bytes, 0);
}

#[test]
fn exact_work_passes_and_one_short_or_zero_refuses() {
    let text = r#""a\uD83D\uDE00λ""#;
    let full = decoded(text);
    assert!(full.result.is_ok());
    let work = full.usage.charged_work as u64;
    assert_eq!(
        attempt(text, work, STORAGE, end(), &mut |_, _| true).result,
        full.result
    );
    for limit in [work - 1, 0] {
        let short = attempt(text, limit, STORAGE, end(), &mut |_, _| true);
        assert!(matches!(short.result, Err(TransportError::Limit { .. })));
        assert_eq!(short.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn every_success_and_invalid_unicode_cleanup_callback_can_refuse_publication() {
    for text in [r#""plain""#, r#""\uD83D\uDE00""#, r#""\uD800""#] {
        let mut total = 0;
        let baseline = attempt(text, WORK, STORAGE, end(), &mut |_, _| {
            total += 1;
            true
        });
        assert_eq!(
            baseline.result.is_ok(),
            serde_json::from_str::<String>(text).is_ok()
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
fn expired_original_deadline_precedes_input_errors_and_callbacks() {
    for text in [r#""valid""#, r#""\uD800""#, "null"] {
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
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn dropping_the_first_string_does_not_renew_work_or_storage_credit() {
    let text = r#""\u0061\u0062""#;
    let full = decoded(text);
    assert!(full.result.is_ok());
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    for (work, bytes) in [
        (full.usage.charged_work as u64, STORAGE),
        (WORK, full.usage.charged_bytes),
    ] {
        let outcome = control::run(end(), &mut |_, _| true, |control| {
            control.constrain(work, bytes)?;
            let first = owned_string(RawSlice::from_raw(raw), control)?;
            assert_eq!(first, "ab");
            drop(first);
            let error = owned_string(RawSlice::from_raw(raw), control).unwrap_err();
            assert!(matches!(error, TransportError::Limit { .. }));
            let usage = control.usage;
            assert_eq!(owned_string(RawSlice::from_raw(raw), control), Err(error));
            assert_eq!(control.usage, usage);
            Ok(()) // The caught refusal must still defeat outer publication.
        });
        assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
        assert_eq!(outcome.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn large_escaped_token_matches_serde_without_decoded_capacity_shrink() {
    let text = format!("\"{}\"", r"\u0000\u03bb\uD83D\uDE00".repeat(2048));
    let outcome = decoded(&text);
    let value = outcome.result.unwrap();
    assert_eq!(value, "\0λ😀".repeat(2048));
    assert_eq!(value, serde_json::from_str::<String>(&text).unwrap());
    assert!(value.capacity() >= text.len() - 2);
    assert_eq!(outcome.usage.charged_bytes, value.capacity());
}

#[test]
fn nested_vector_composition_accounts_slots_and_each_string_owner_once() {
    let text = r#"[["λ","\u0000"],[],["\uD83D\uDE00","a,b]{}"]]"#;
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    let outcome = control::run(end(), &mut |_, _| true, |control| {
        control.constrain(WORK, STORAGE)?;
        super::super::vector(RawSlice::from_raw(raw), 3, control, |child, control| {
            super::super::vector(child, 3, control, owned_string)
        })
    });
    let result = outcome.result.unwrap();
    assert_eq!(
        result,
        serde_json::from_str::<Vec<Vec<String>>>(text).unwrap()
    );
    let slots = result.capacity() * size_of::<Vec<String>>()
        + result
            .iter()
            .map(|row| row.capacity() * size_of::<String>())
            .sum::<usize>();
    let strings = result.iter().flatten().map(String::capacity).sum::<usize>();
    assert_eq!(outcome.usage.charged_bytes, slots + strings);
}
