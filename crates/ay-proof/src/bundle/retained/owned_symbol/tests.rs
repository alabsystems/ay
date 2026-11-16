// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! RawValue parsing is test-only prior admission, not the owning wire reader.
//! Arc assertions pin logical requested layout, not allocator capacity or RSS.

use super::read;
use crate::bundle::retained::{control, owned_values::RawSlice, TransportError, TransportOutcome};
use ay_core::{time::Instant, Symbol};
use serde_json::value::RawValue;
use std::{
    cell::Cell,
    mem::{align_of, size_of},
    sync::atomic::AtomicUsize,
    time::Duration,
};

const WORK: u64 = 1_000_000;
const STORAGE: usize = 1024 * 1024;
const INDEXED: &str = r#"{"Indexed":["extract\u0000λ",[0,4294967295,7,7,4]]}"#;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn attempt(
    text: &str,
    work: u64,
    bytes: usize,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> TransportOutcome<Symbol> {
    let raw: &RawValue = serde_json::from_str(text).unwrap();
    control::run(deadline, progress, |control| {
        control.constrain(work, bytes)?;
        read(RawSlice::from_raw(raw), control)
    })
}

fn decoded(text: &str) -> TransportOutcome<Symbol> {
    attempt(text, WORK, STORAGE, end(), &mut |_, _| true)
}

fn accepts(text: &str) {
    let expected: Symbol = serde_json::from_str(text).unwrap();
    let actual = decoded(text).result.unwrap();
    assert_eq!(actual, expected, "{text}");
    assert_eq!(
        serde_json::to_string(&actual).unwrap(),
        serde_json::to_string(&expected).unwrap()
    );
}

fn rejects(text: &str) {
    assert!(serde_json::from_str::<Symbol>(text).is_err(), "{text}");
    let result = decoded(text);
    assert!(result.result.is_err(), "{text}");
    assert_eq!(result.usage.returned_owned_bytes, 0);
}

#[test]
fn named_and_indexed_unicode_empty_and_escaped_names_match_legacy_serde() {
    for text in [
        r#"{"Named":"plain"}"#,
        r#"{"Named":""}"#,
        r#"{"Named":"λé😀\u0000"}"#,
        r#"{"Na\u006ded":"\uD83D\uDE00"}"#,
        r#"{"Named":"\"\\\/\b\f\n\r\t"}"#,
        r#"{"Indexed":["extract",[7,4]]}"#,
        r#"{"Indexed":["",[]]}"#,
        r#"{"\u0049ndexed":["\u0000",[0,4294967295]]}"#,
        INDEXED,
    ] {
        accepts(text);
    }
}

#[test]
fn index_order_duplicates_and_empty_index_variant_are_not_normalized() {
    let left = decoded(r#"{"Indexed":["x",[7,4,7]]}"#).result.unwrap();
    let right = decoded(r#"{"Indexed":["x",[4,7,7]]}"#).result.unwrap();
    assert_ne!(left, right);
    if let Symbol::Indexed(name, indices) = left {
        assert_eq!(name.as_str(), "x");
        assert_eq!(indices, [7, 4, 7]);
    } else {
        panic!("indexed variant lost");
    }
    assert_ne!(
        decoded(r#"{"Named":"x"}"#).result.unwrap(),
        decoded(r#"{"Indexed":["x",[]]}"#).result.unwrap()
    );
}

#[test]
fn malformed_enum_and_exact_tuple_shapes_refuse_like_serde() {
    for text in [
        "null",
        "0",
        "1",
        "-1",
        "true",
        "[]",
        "{}",
        r#""Named""#,
        r#""Indexed""#,
        r#"{"Named":null}"#,
        r#"{"Named":1}"#,
        r#"{"Named":["x"]}"#,
        r#"{"Named":{"name":"x"}}"#,
        r#"{"named":"x"}"#,
        r#"{"Unknown":"x"}"#,
        r#"{"0":"x"}"#,
        r#"{"Named":"x","Named":"x"}"#,
        r#"{"Named":"x","Indexed":["x",[]]}"#,
        r#"{"Indexed":null}"#,
        r#"{"Indexed":[]}"#,
        r#"{"Indexed":["x"]}"#,
        r#"{"Indexed":["x",[],0]}"#,
        r#"{"Indexed":[null,[]]}"#,
        r#"{"Indexed":["x",null]}"#,
        r#"{"Indexed":{"name":"x","indices":[]}}"#,
    ] {
        rejects(text);
    }
}

#[test]
fn index_integer_boundaries_and_invalid_name_surrogates_match_serde() {
    for value in [
        "-0",
        "-1",
        "1.0",
        "1e0",
        "4294967296",
        "null",
        "true",
        r#""7""#,
    ] {
        rejects(&format!(r#"{{"Indexed":["owned",[0,{value},1]]}}"#));
    }
    for text in [
        r#"{"Named":"\uD800"}"#,
        r#"{"Named":"\uDC00"}"#,
        r#"{"Indexed":["\uD800x",[]]}"#,
        r#"{"\uD800":"x"}"#,
    ] {
        rejects(text);
    }
    accepts(r#"{"Indexed":["\uDBFF\uDFFF",[0,4294967295]]}"#);
}

#[test]
fn shared_name_reservation_includes_header_and_alignment_even_when_empty() {
    let alignment = align_of::<AtomicUsize>();
    let header = 2 * size_of::<AtomicUsize>();
    for length in [0, 1, alignment, alignment + 1, 8, 9] {
        let name = "a".repeat(length);
        let text = format!(r#"{{"Named":"{name}"}}"#);
        let mut reservations = Vec::new();
        let outcome = attempt(&text, WORK, STORAGE, end(), &mut |_, bytes| {
            if bytes != 0 {
                reservations.push(bytes);
            }
            true
        });
        assert_eq!(outcome.result.unwrap().name(), name);
        let expected_arc = (header + length).div_ceil(alignment) * alignment;
        assert_eq!(reservations.last().copied(), Some(expected_arc));
        assert!(expected_arc >= header + length);
        assert_eq!(
            outcome.usage.charged_bytes,
            reservations.iter().sum::<usize>()
        );
        // Earlier charges retain the variant String and name String while the
        // Arc copy is admitted. No refund can collapse this to text bytes only.
        assert!(outcome.usage.charged_bytes >= "Named".len() + length + expected_arc);
    }
}

#[test]
fn arc_layout_uses_decoded_utf8_length_not_encoded_escape_length() {
    let text = r#"{"Named":"\u0061\u0062\u03bb"}"#;
    let expected = "abλ";
    let header = 2 * size_of::<AtomicUsize>();
    let alignment = align_of::<AtomicUsize>();
    let expected_arc = (header + expected.len()).div_ceil(alignment) * alignment;
    let mut reservations = Vec::new();
    let outcome = attempt(text, WORK, STORAGE, end(), &mut |_, bytes| {
        if bytes > 0 {
            reservations.push(bytes);
        }
        true
    });
    assert_eq!(outcome.result.unwrap().name(), expected);
    assert_eq!(reservations.last().copied(), Some(expected_arc));
    assert!(reservations.contains(&18)); // Three six-byte encoded escapes.
    assert!(outcome.usage.charged_bytes >= 5 + 18 + expected_arc);
}

#[test]
fn exact_work_and_storage_pass_and_each_one_short_or_zero_refuses() {
    let full = decoded(INDEXED);
    assert!(full.result.is_ok());
    let (work, bytes) = (full.usage.charged_work as u64, full.usage.charged_bytes);
    let exact = attempt(INDEXED, work, bytes, end(), &mut |_, _| true);
    assert_eq!(exact.result, full.result);
    assert_eq!(exact.usage, full.usage);
    for (work, bytes) in [(work - 1, bytes), (work, bytes - 1), (0, bytes), (work, 0)] {
        let short = attempt(INDEXED, work, bytes, end(), &mut |_, _| true);
        assert!(matches!(short.result, Err(TransportError::Limit { .. })));
        assert_eq!(short.usage.returned_owned_bytes, 0);
    }
}

#[test]
fn every_success_and_partial_owner_failure_callback_can_refuse_publication() {
    for text in [INDEXED, r#"{"Indexed":["owned",[0,true]]}"#] {
        let mut total = 0;
        let full = attempt(text, WORK, STORAGE, end(), &mut |_, _| {
            total += 1;
            true
        });
        assert_eq!(
            full.result.is_ok(),
            serde_json::from_str::<Symbol>(text).is_ok()
        );
        assert!(total > 5);
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
                assert_eq!(outcome.usage, full.usage);
            }
        }
    }
}

#[test]
fn expired_original_deadline_refuses_before_valid_or_malformed_symbol_work() {
    for text in [INDEXED, "null", r#"{"Named":"\uD800"}"#] {
        let outcome = attempt(
            text,
            WORK,
            STORAGE,
            Instant::now().checked_sub(Duration::from_secs(1)).unwrap(),
            &mut |_, _| -> bool { panic!("expired before callback") },
        );
        assert_eq!(outcome.result, Err(TransportError::Deadline));
        assert_eq!(outcome.usage.charged_work, 0);
        assert_eq!(outcome.usage.charged_bytes, 0);
    }
}

#[test]
fn dropping_symbol_does_not_refund_work_string_slots_or_arc_reservation() {
    let full = decoded(INDEXED);
    assert!(full.result.is_ok());
    let raw: &RawValue = serde_json::from_str(INDEXED).unwrap();
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
            Ok(())
        });
        assert!(matches!(outcome.result, Err(TransportError::Limit { .. })));
    }
}

#[test]
fn caught_arc_admission_callback_panic_is_sticky_before_public_constructor() {
    let raw: &RawValue = serde_json::from_str(r#"{"Named":"abcdefgh"}"#).unwrap();
    let header = 2 * size_of::<AtomicUsize>();
    let alignment = align_of::<AtomicUsize>();
    let arc_bytes = (header + 8).div_ceil(alignment) * alignment;
    let calls = Cell::new(0);
    let outcome = control::run(
        end(),
        &mut |_, bytes| {
            calls.set(calls.get() + 1);
            assert!(bytes != arc_bytes, "Arc admission refused by panic");
            true
        },
        |control| {
            control.constrain(WORK, STORAGE)?;
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                read(RawSlice::from_raw(raw), control)
            }));
            assert!(caught.is_err());
            let before = calls.get();
            assert_eq!(
                read(RawSlice::from_raw(raw), control),
                Err(TransportError::Refused)
            );
            assert_eq!(calls.get(), before);
            Ok(())
        },
    );
    assert_eq!(outcome.result, Err(TransportError::Refused));
}
