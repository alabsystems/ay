// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;
use crate::clause_trace::originals::{OriginalArena, OriginalControl};

fn originals() -> OriginalArena {
    OriginalArena {
        literals: vec![pos(0), pos(0).negated()],
        offsets: vec![0, 1],
        ids: vec![1, 2],
    }
}

#[test]
fn pending_original_transfer_preserves_interleaved_events_and_independent_replay() {
    let source = originals();
    let mut trace = ClauseTrace::new();
    let _ = ay_core::misc_cli_flags();
    assert!(trace.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    assert!(trace.note_ledger_original(1, source.retained_bytes().unwrap()));
    let owner = test_owner(1_000_000, 1_000_000);
    trace
        .prepare_counted_add(10, &[pos(0)], false, &[1], &owner)
        .unwrap()
        .commit();
    assert!(trace.note_ledger_original(2, source.retained_bytes().unwrap()));
    trace
        .prepare_counted_add(11, &[], false, &[10, 2], &owner)
        .unwrap()
        .commit();
    owner.check().unwrap();
    assert!(trace.finish_original_transfer(source, 1, &mut |_| true));
    assert_eq!(
        rows(&trace),
        [
            (1, vec![pos(0)], true, vec![]),
            (10, vec![pos(0)], false, vec![1]),
            (2, vec![pos(0).negated()], true, vec![]),
            (11, vec![], false, vec![10, 2]),
        ]
    );
    crate::validate_clause_trace_resolution(
        &trace,
        1,
        &crate::ResolutionValidationLimits::unbounded(),
    )
    .unwrap();
}

#[test]
fn transferred_original_ids_and_bypassed_original_events_are_refused() {
    let source = originals();
    let mut trace = ClauseTrace::new();
    let _ = ay_core::misc_cli_flags();
    assert!(trace.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    assert!(trace.note_ledger_original(1, source.retained_bytes().unwrap()));
    assert!(trace.note_ledger_original(2, source.retained_bytes().unwrap()));
    assert!(trace.finish_original_transfer(source, 1, &mut |_| true));
    let before = rows(&trace);
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(trace
        .prepare_counted_add(2, &[pos(0)], false, &[], &owner)
        .is_err());
    assert_eq!(rows(&trace), before);
    assert!(owner.check().is_err());

    let mut pending = ClauseTrace::new();
    assert!(pending.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(pending
        .prepare_counted_add(1, &[pos(0)], true, &[], &owner)
        .is_err());
    assert!(pending.is_empty());
    assert!(!pending.original_control().unwrap().open());
    assert!(owner.check().is_err());
}
