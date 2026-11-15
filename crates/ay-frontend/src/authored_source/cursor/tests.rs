// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::authored_source::AuthoredSource;
use ay_core::original_query::{QueryError, StopReason};
use std::cell::Cell;
use std::ops::ControlFlow;

#[test]
fn raw_order_spans_quotation_and_complete_original_bytes_match_legacy_capture() {
    let input = "; original\n(assert |true|)\r\n(assert false) \"a\"\"b\" |λ\\|x| #x0A #b01 0.00";
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(100_000, &mut poll);
    let expected = AuthoredSource::capture(input, &mut work).unwrap();
    let mut cursor = SourceCursor::new(input, &mut work).unwrap();
    assert!(std::ptr::eq(cursor.original().as_ptr(), input.as_ptr()));
    assert_eq!(cursor.original(), input);
    let mut actual = Vec::new();
    while let Some(token) = cursor.next_token().unwrap() {
        assert_eq!(&input[token.span.clone()], token.raw);
        actual.push(token);
    }
    assert_eq!(actual, expected.tokens().cloned().collect::<Vec<_>>());
    assert_eq!(cursor.token_count(), expected.token_count());
    assert_eq!(cursor.position(), input.len());
    assert!(cursor.next_token().unwrap().is_none());
}

#[test]
fn original_owner_receives_actual_byte_metadata_and_bookkeeping_units_without_storage() {
    let units = Cell::new(0usize);
    let storage = Cell::new(0usize);
    let mut admission = |work, bytes| {
        units.set(units.get() + work);
        storage.set(storage.get() + bytes);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(100_000, &mut admission);
    let input = "; comment\ntrue |λ| \"a\"\"b\"";
    let mut cursor = SourceCursor::new(input, &mut work).unwrap();
    while cursor.next_token().unwrap().is_some() {}
    cursor.charge_work(7).unwrap();
    assert_eq!(units.get(), input.len() + cursor.token_count() + 7);
    assert_eq!(storage.get(), 0);
}

#[test]
fn metadata_one_short_stops_the_same_adapter_before_yield_or_reconstruction() {
    let calls = Cell::new(0);
    let mut admission = |_, _| {
        calls.set(calls.get() + 1);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(4, &mut admission);
    {
        let mut cursor = SourceCursor::new("true", &mut work).unwrap();
        assert_eq!(
            cursor.next_token().unwrap_err(),
            AuthoredSourceError::Control(QueryError::Exhausted),
        );
        assert_eq!(cursor.position(), 4);
        assert_eq!(cursor.token_count(), 0);
        let stopped_calls = calls.get();
        assert_eq!(
            cursor.next_token().unwrap_err(),
            AuthoredSourceError::Control(QueryError::Exhausted),
        );
        assert_eq!(calls.get(), stopped_calls);
    }
    let stopped_calls = calls.get();
    assert!(matches!(
        SourceCursor::new("", &mut work),
        Err(AuthoredSourceError::Control(QueryError::Exhausted)),
    ));
    assert_eq!(calls.get(), stopped_calls);
    assert_eq!(work.remaining(), 0);
}

#[test]
fn malformed_suffix_is_sticky_without_recovery_or_further_owner_calls() {
    let calls = Cell::new(0);
    let mut admission = |_, _| {
        calls.set(calls.get() + 1);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(100_000, &mut admission);
    let mut cursor = SourceCursor::new("true 00 false", &mut work).unwrap();
    assert_eq!(cursor.next_token().unwrap().unwrap().raw, "true");
    let error = cursor.next_token().unwrap_err();
    assert!(matches!(
        error,
        AuthoredSourceError::Lexical { offset: 7, .. }
    ));
    let stopped_calls = calls.get();
    assert_eq!(cursor.next_token().unwrap_err(), error);
    assert_eq!(cursor.charge_work(0).unwrap_err(), error);
    assert_eq!(calls.get(), stopped_calls);
    assert_eq!(cursor.token_count(), 1);
    assert_eq!(cursor.original(), "true 00 false");
}

fn stopped_inside(input: &str, reason: StopReason) {
    let calls = Cell::new(0);
    let mut admission = |_, _| {
        calls.set(calls.get() + 1);
        if calls.get() == 256 {
            Err(QueryError::Interrupted(reason))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(100_000, &mut admission);
    let mut cursor = SourceCursor::new(input, &mut work).unwrap();
    let expected = AuthoredSourceError::Control(QueryError::Interrupted(reason));
    assert_eq!(cursor.next_token().unwrap_err(), expected);
    assert_eq!(cursor.next_token().unwrap_err(), expected);
    assert_eq!(calls.get(), 256);
    assert_eq!(cursor.token_count(), 0);
    assert!(cursor.position() < input.len());
}

#[test]
fn the_original_owner_is_polled_inside_long_comments_strings_quotes_and_numerals() {
    stopped_inside(
        &format!(";{}\ntrue", "x".repeat(2_048)),
        StopReason::Cancelled,
    );
    stopped_inside(&format!("\"{}\"", "x".repeat(2_048)), StopReason::Deadline);
    stopped_inside(&format!("|{}|", "x".repeat(2_048)), StopReason::Cancelled);
    stopped_inside(&"1".repeat(2_048), StopReason::Deadline);
}

#[test]
fn deadline_at_eof_refuses_even_after_the_last_token_reaches_input_length() {
    let calls = Cell::new(0);
    let mut admission = |_, _| {
        calls.set(calls.get() + 1);
        if calls.get() == 7 {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(100_000, &mut admission);
    let mut cursor = SourceCursor::new("true", &mut work).unwrap();
    assert_eq!(cursor.next_token().unwrap().unwrap().raw, "true");
    assert_eq!(cursor.position(), cursor.original().len());
    let expected = AuthoredSourceError::Control(QueryError::Interrupted(StopReason::Deadline));
    assert_eq!(cursor.next_token().unwrap_err(), expected);
    assert_eq!(cursor.next_token().unwrap_err(), expected);
    assert_eq!(calls.get(), 7);
}

#[test]
fn healthy_cursor_reborrowing_does_not_reset_the_original_aggregate_grant() {
    let remaining = Cell::new(6usize);
    let terminal = Cell::new(false);
    let mut admission = |units, bytes| {
        assert_eq!(bytes, 0);
        if terminal.get() {
            return Err(QueryError::Exhausted);
        }
        let Some(next) = remaining.get().checked_sub(units) else {
            terminal.set(true);
            return Err(QueryError::Exhausted);
        };
        remaining.set(next);
        Ok(())
    };
    {
        let mut work = WorkBudget::with_admission(100_000, &mut admission);
        {
            let mut first = SourceCursor::new("true", &mut work).unwrap();
            assert!(first.next_token().unwrap().is_some());
            assert!(first.next_token().unwrap().is_none());
        }
        let mut second = SourceCursor::new("x", &mut work).unwrap();
        assert_eq!(
            second.next_token().unwrap_err(),
            AuthoredSourceError::Control(QueryError::Exhausted),
        );
    }
    // A reconstructed local adapter is not a new original owner or grant.
    let mut work = WorkBudget::with_admission(100_000, &mut admission);
    assert!(matches!(
        SourceCursor::new("", &mut work),
        Err(AuthoredSourceError::Control(QueryError::Exhausted)),
    ));
    assert_eq!(remaining.get(), 0);
    assert!(terminal.get());
}

#[test]
fn empty_and_comment_only_sources_finish_without_owned_token_storage() {
    for input in ["", ";comment", " \t;comment\r\n "] {
        let units = Cell::new(0usize);
        let mut admission = |work, storage| {
            assert_eq!(storage, 0);
            units.set(units.get() + work);
            Ok(())
        };
        let mut work = WorkBudget::with_admission(100_000, &mut admission);
        let mut cursor = SourceCursor::new(input, &mut work).unwrap();
        assert!(cursor.next_token().unwrap().is_none());
        assert_eq!(cursor.token_count(), 0);
        assert_eq!(cursor.position(), input.len());
        assert_eq!(units.get(), input.len());
    }
}
