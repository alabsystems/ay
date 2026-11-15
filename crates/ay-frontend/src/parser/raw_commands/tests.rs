// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{QueryError, StopReason};
use std::cell::Cell;
use std::ops::ControlFlow;

fn admission_counts(input: &str) -> (usize, usize, usize, usize) {
    let calls = Cell::new(0usize);
    let units = Cell::new(0usize);
    let mut admission = |debit, storage| {
        assert_eq!(storage, 0);
        calls.set(calls.get() + 1);
        units.set(units.get() + debit);
        Ok(())
    };
    let mut work = WorkBudget::with_admission(1_000_000, &mut admission);
    let mut frames = RawCommandCursor::new(input, &mut work).expect("bounded raw-frame fixture");
    let constructor_calls = calls.get();
    let constructor_units = units.get();
    while frames
        .next_frame()
        .expect("bounded raw-frame fixture")
        .is_some()
    {}
    (
        constructor_calls,
        constructor_units,
        calls.get(),
        units.get(),
    )
}

#[test]
fn exact_order_ranges_and_complete_trivia_remain_borrowed_without_normalization() {
    let first = r#"(assert (= |λ\|x| "a""b()"))"#;
    let input = format!("; original\n{first}\r\n; repeated\n{first}\n(exit)(check-sat)");
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(100_000, &mut poll);
    let mut cursor = RawCommandCursor::new(&input, &mut work).expect("bounded raw-frame fixture");
    assert!(std::ptr::eq(cursor.original().as_ptr(), input.as_ptr()));
    let mut frames = Vec::new();
    while let Some(frame) = cursor.next_frame().expect("bounded raw-frame fixture") {
        assert_eq!(&input[frame.span.clone()], frame.raw);
        assert!(std::ptr::eq(
            frame.raw.as_ptr(),
            input.as_ptr().wrapping_add(frame.span.start),
        ));
        frames.push(frame);
    }
    assert_eq!(
        frames.iter().map(|frame| frame.raw).collect::<Vec<_>>(),
        [first, first, "(exit)", "(check-sat)"],
    );
    assert_eq!(frames[0].tokens.start, 0);
    for pair in frames.windows(2) {
        assert_eq!(pair[0].tokens.end, pair[1].tokens.start);
        assert!(pair[0].span.end <= pair[1].span.start);
    }
    assert_eq!(cursor.original(), input);
}

#[test]
fn malformed_complete_framing_never_exposes_an_earlier_valid_command() {
    for input in [
        "(check-sat) stray (check-sat)",
        "(check-sat) )",
        "(check-sat) (assert",
        "(check-sat) 00",
        "(check-sat) \"unterminated",
        ")",
    ] {
        let mut poll = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(100_000, &mut poll);
        // No cursor/frame result exists on failed complete preflight.
        assert!(
            RawCommandCursor::new(input, &mut work).is_err(),
            "{input:?}"
        );
    }
}

#[test]
fn framing_success_is_explicitly_not_native_command_grammar_or_proof_authority() {
    let input = "(assert) (unrecognized-command x) ()";
    assert!(crate::parse(input).is_err());
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(100_000, &mut poll);
    let mut cursor = RawCommandCursor::new(input, &mut work).expect("bounded raw-frame fixture");
    let mut count = 0;
    while cursor
        .next_frame()
        .expect("bounded raw-frame fixture")
        .is_some()
    {
        count += 1;
    }
    assert_eq!(count, 3);
}

#[test]
fn every_preflight_and_final_owner_observation_can_refuse_before_cursor_publication() {
    let input = "(assert false) ; tail\n(check-sat)";
    let (constructor_calls, _, _, _) = admission_counts(input);
    for stop_at in 1..=constructor_calls {
        let calls = Cell::new(0usize);
        let mut admission = |_, storage| {
            assert_eq!(storage, 0);
            calls.set(calls.get() + 1);
            if calls.get() == stop_at {
                Err(QueryError::Interrupted(StopReason::Deadline))
            } else {
                Ok(())
            }
        };
        let mut work = WorkBudget::with_admission(100_000, &mut admission);
        assert_eq!(
            RawCommandCursor::new(input, &mut work)
                .err()
                .expect("bounded raw-frame fixture"),
            RawCommandError::Source(AuthoredSourceError::Control(QueryError::Interrupted(
                StopReason::Deadline
            ),)),
        );
        assert_eq!(calls.get(), stop_at);
        assert_eq!(
            work.charge(0).expect_err("original owner refusal"),
            QueryError::Interrupted(StopReason::Deadline),
        );
        assert_eq!(calls.get(), stop_at);
    }
}

#[test]
fn every_replay_and_terminal_owner_stop_is_sticky_without_implicit_error_eof() {
    let input = "(assert false)(check-sat)";
    let (constructor_calls, _, total_calls, _) = admission_counts(input);
    for stop_at in constructor_calls + 1..=total_calls {
        let calls = Cell::new(0usize);
        let mut admission = |_, storage| {
            assert_eq!(storage, 0);
            calls.set(calls.get() + 1);
            if calls.get() == stop_at {
                Err(QueryError::Interrupted(StopReason::Cancelled))
            } else {
                Ok(())
            }
        };
        let mut work = WorkBudget::with_admission(100_000, &mut admission);
        let mut cursor =
            RawCommandCursor::new(input, &mut work).expect("bounded raw-frame fixture");
        let error = loop {
            match cursor.next_frame() {
                Ok(Some(_)) => {}
                Ok(None) => panic!("a refused observation must not become EOF"),
                Err(error) => break error,
            }
        };
        assert_eq!(
            error,
            RawCommandError::Source(AuthoredSourceError::Control(QueryError::Interrupted(
                StopReason::Cancelled
            ),)),
        );
        assert_eq!(
            cursor.next_frame().expect_err("original owner refusal"),
            error
        );
        assert_eq!(calls.get(), stop_at);
    }
}

#[test]
fn one_short_preflight_work_stays_spent_on_the_same_adapter() {
    let input = "(check-sat)";
    let (_, required_units, _, _) = admission_counts(input);
    let calls = Cell::new(0usize);
    let mut admission = |_, storage| {
        assert_eq!(storage, 0);
        calls.set(calls.get() + 1);
        Ok(())
    };
    let mut work = WorkBudget::with_admission((required_units - 1) as u64, &mut admission);
    assert_eq!(
        RawCommandCursor::new(input, &mut work)
            .err()
            .expect("bounded raw-frame fixture"),
        RawCommandError::Source(AuthoredSourceError::Control(QueryError::Exhausted)),
    );
    let stopped_calls = calls.get();
    assert_eq!(
        RawCommandCursor::new("()", &mut work)
            .err()
            .expect("bounded raw-frame fixture"),
        RawCommandError::Source(AuthoredSourceError::Control(QueryError::Exhausted)),
    );
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn preflight_and_replay_debit_one_original_aggregate_owner_without_storage() {
    let input = "(reset)(reset-assertions)(check-sat)";
    let (_, admitted_units, _, _) = admission_counts(input);
    let remaining = Cell::new(admitted_units);
    let terminal = Cell::new(false);
    let mut admission = |units, storage| {
        assert_eq!(storage, 0);
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
        let mut work = WorkBudget::with_admission(1_000_000, &mut admission);
        let mut cursor =
            RawCommandCursor::new(input, &mut work).expect("bounded raw-frame fixture");
        assert_eq!(remaining.get(), 0);
        assert_eq!(
            cursor.next_frame().expect_err("original owner refusal"),
            RawCommandError::Source(AuthoredSourceError::Control(QueryError::Exhausted)),
        );
    }
    // Even a new local adapter is not a new grant from this original owner.
    let mut work = WorkBudget::with_admission(1_000_000, &mut admission);
    assert_eq!(
        RawCommandCursor::new("()", &mut work)
            .err()
            .expect("bounded raw-frame fixture"),
        RawCommandError::Source(AuthoredSourceError::Control(QueryError::Exhausted)),
    );
    assert!(terminal.get());
    assert_eq!(remaining.get(), 0);
}

#[test]
fn original_deadline_during_replay_is_not_renewed_by_source_reset_commands() {
    let expired = Cell::new(false);
    let mut admission = |_, storage| {
        assert_eq!(storage, 0);
        if expired.get() {
            Err(QueryError::Interrupted(StopReason::Deadline))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(100_000, &mut admission);
    let mut cursor = RawCommandCursor::new("(reset)(reset-assertions)(check-sat)", &mut work)
        .expect("bounded raw-frame fixture");
    expired.set(true);
    let expected = RawCommandError::Source(AuthoredSourceError::Control(QueryError::Interrupted(
        StopReason::Deadline,
    )));
    assert_eq!(
        cursor.next_frame().expect_err("original owner refusal"),
        expected
    );
    assert_eq!(
        cursor.next_frame().expect_err("original owner refusal"),
        expected
    );
}

#[test]
fn long_tokens_and_comments_observe_the_original_owner_inside_preflight() {
    for input in [
        format!(";{}\n(check-sat)", "x".repeat(4_096)),
        format!("(echo \"{}\")", "x".repeat(4_096)),
        format!("(declare-const |{}| Bool)", "x".repeat(4_096)),
        format!("(assert {})", "(".repeat(4_096)),
    ] {
        let calls = Cell::new(0usize);
        let mut admission = |_, storage| {
            assert_eq!(storage, 0);
            calls.set(calls.get() + 1);
            if calls.get() == 256 {
                Err(QueryError::Interrupted(StopReason::Cancelled))
            } else {
                Ok(())
            }
        };
        let mut work = WorkBudget::with_admission(100_000, &mut admission);
        assert_eq!(
            RawCommandCursor::new(&input, &mut work)
                .err()
                .expect("bounded raw-frame fixture"),
            RawCommandError::Source(AuthoredSourceError::Control(QueryError::Interrupted(
                StopReason::Cancelled
            ),)),
        );
        assert_eq!(calls.get(), 256);
    }
}

#[test]
fn empty_and_comment_only_framing_finishes_only_through_owner_polled_eof() {
    for input in ["", ";comment", " \t;comment\r\n "] {
        let units = Cell::new(0usize);
        let mut admission = |debit, storage| {
            assert_eq!(storage, 0);
            units.set(units.get() + debit);
            Ok(())
        };
        let mut work = WorkBudget::with_admission(100_000, &mut admission);
        let mut cursor =
            RawCommandCursor::new(input, &mut work).expect("bounded raw-frame fixture");
        assert!(cursor
            .next_frame()
            .expect("bounded raw-frame fixture")
            .is_none());
        // Two actual scans; a fixed eight-unit framing step precedes each EOF.
        assert_eq!(units.get(), 2 * (input.len() + 8));
    }
}
