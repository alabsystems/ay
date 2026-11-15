// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;
use crate::{validate_clause_trace_resolution, ResolutionValidationLimits};

#[path = "tests/metering.rs"]
mod metering;
#[path = "tests/refusals.rs"]
mod refusals;

fn x() -> Literal {
    Literal::positive(Variable(0))
}

fn arena() -> OriginalArena {
    OriginalArena {
        literals: vec![x(), x().negated()],
        offsets: vec![0, 1],
        ids: vec![1, 2],
    }
}

fn pending(originals: &OriginalArena) -> ClauseTrace {
    let mut trace = ClauseTrace::new();
    assert!(trace.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    assert!(trace.note_ledger_original(1, originals.retained_bytes().unwrap()));
    trace.add_clause_with_hint_slices(10, &[x()], false, &[1]);
    assert!(trace.note_ledger_original(2, originals.retained_bytes().unwrap()));
    trace.add_clause_with_hint_slices(11, &[], false, &[10, 2]);
    trace
}

fn rows(trace: &ClauseTrace) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    trace
        .entries()
        .iter()
        .map(|row| {
            (
                row.id,
                row.clause.to_vec(),
                row.is_original,
                row.resolution_hints.to_vec(),
            )
        })
        .collect()
}

fn legacy() -> ClauseTrace {
    let mut trace = ClauseTrace::new();
    trace.add_clause_with_hint_slices(1, &[x()], true, &[]);
    trace.add_clause_with_hint_slices(10, &[x()], false, &[1]);
    trace.add_clause_with_hint_slices(2, &[x().negated()], true, &[]);
    trace.add_clause_with_hint_slices(11, &[], false, &[10, 2]);
    trace
}

#[test]
fn reserved_ids_preserve_exact_legacy_event_order_and_native_replay() {
    let originals = arena();
    let mut trace = pending(&originals);
    assert!(trace.finish_original_transfer(originals, 1, &mut |_| true));
    let expected = rows(&legacy());
    assert_eq!(rows(&trace), expected);
    assert_eq!(trace.len(), 4);
    for (index, expected) in expected.iter().enumerate() {
        let actual = trace.entries().get(index).unwrap();
        assert_eq!(
            (
                actual.id,
                actual.clause,
                actual.is_original,
                actual.resolution_hints
            ),
            (
                expected.0,
                expected.1.as_slice(),
                expected.2,
                expected.3.as_slice()
            )
        );
    }
    assert!(trace.entries().get(4).is_none());
    assert_eq!(trace.entries().last().unwrap().id, 11);
    validate_clause_trace_resolution(&trace, 1, &ResolutionValidationLimits::unbounded()).unwrap();
}

#[test]
fn transfer_preserves_all_three_allocation_identities_and_exact_capacities() {
    let originals = arena();
    let pointers = (
        originals.literals.as_ptr(),
        originals.offsets.as_ptr(),
        originals.ids.as_ptr(),
    );
    let bytes = originals.retained_bytes().unwrap();
    let mut trace = pending(&originals);
    assert_eq!(trace.meta.len(), 2, "no EntryMeta per original");
    assert_eq!(trace.lit_pool, [x()], "only the derived unit was copied");
    assert!(trace.finish_original_transfer(originals, 1, &mut |_| true));
    let moved = trace.originals.arena.as_ref().unwrap();
    assert_eq!(
        pointers,
        (
            moved.literals.as_ptr(),
            moved.offsets.as_ptr(),
            moved.ids.as_ptr()
        )
    );
    assert_eq!(trace.owned_original_bytes(), bytes);
    assert_eq!(
        trace.used_bytes(),
        bytes
            + trace.meta.capacity() * size_of::<super::super::EntryMeta>()
            + trace.lit_pool.capacity() * size_of::<Literal>()
            + trace.hint_pool.capacity() * size_of::<u64>()
    );
}

#[test]
fn forward_hint_is_not_hidden_by_sorting_reserved_ids() {
    let originals = arena();
    let mut trace = pending(&originals);
    assert!(trace.set_resolution_hints(10, vec![2]));
    assert!(!trace.finish_original_transfer(originals, 1, &mut |_| true));
    assert!(trace.proof_work_exhausted());
}

#[test]
fn malformed_prefixes_and_duplicate_or_unbound_ids_are_rejected() {
    for kind in 0..7 {
        let mut originals = arena();
        let mut trace = pending(&originals);
        match kind {
            0 => trace.meta[0].original_prefix_len = 3,
            1 => trace.meta[1].original_prefix_len = 0,
            2 => originals.ids[0] = 0,
            3 => originals.ids[1] = 1,
            4 => trace.meta[1].id = 10,
            5 => trace.meta[0].id = 2,
            _ => originals.offsets[1] = u32::MAX,
        }
        assert!(
            !trace.finish_original_transfer(originals, 1, &mut |_| true),
            "kind {kind}"
        );
    }
}

#[test]
fn original_after_terminal_and_empty_original_never_publish() {
    let originals = arena();
    let mut trace = pending(&originals);
    trace.meta[1].original_prefix_len = 1;
    assert!(!trace.finish_original_transfer(originals, 1, &mut |_| true));
    let mut originals = arena();
    originals.offsets[1] = 0;
    let mut trace = pending(&originals);
    assert!(!trace.finish_original_transfer(originals, 1, &mut |_| true));
}

#[test]
fn original_capacities_reduce_growth_and_replay_memory_not_just_reported_len() {
    let originals = arena();
    let bytes = originals.retained_bytes().unwrap();
    let mut trace = ClauseTrace::new();
    assert!(trace.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    trace.budget_bytes = bytes;
    assert!(trace.note_ledger_original(1, bytes));
    trace.add_clause_with_hint_slices(10, &[x()], false, &[1]);
    assert!(
        trace.is_truncated(),
        "moved originals leave no growth credit"
    );
    assert_eq!(trace.meta.capacity(), 0);
}

#[test]
fn exhausted_snapshot_counts_pending_originals_without_copying_them() {
    let originals = arena();
    let mut trace = pending(&originals);
    trace.mark_proof_work_exhausted();
    trace.snapshot_before_exhaustion_clear();
    let before = trace.exhaustion_snapshot().unwrap();
    assert_eq!(
        (before.originals, before.learned, before.entries),
        (2, 2, 4)
    );
    trace.clear_entries();
    assert!(trace.original_transfer_pending());
    assert!(trace.proof_work_exhausted());
    assert!(!trace.finish_original_transfer(originals, 1, &mut |_| true));
}

#[test]
fn retirement_interleaving_survives_pending_original_arena_transfer() {
    let originals = arena();
    let mut trace = ClauseTrace::new();
    trace.set_event_capture(super::super::ClauseEventCapture::Lifecycle);
    assert!(trace.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    assert!(trace.note_ledger_original(1, originals.retained_bytes().unwrap()));
    trace.record_deletion(1, &[x()]);
    assert!(trace.note_ledger_original(2, originals.retained_bytes().unwrap()));
    trace.add_clause_with_hint_slices(11, &[], false, &[1, 2]);
    assert!(trace.finish_original_transfer(originals, 1, &mut |_| true));
    let events: Vec<_> = trace.events().collect();
    assert_eq!(events.len(), 4);
    assert_eq!(events[0].id, 1);
    assert_eq!(events[1].origin, super::super::ClauseEventOrigin::Deleted);
    assert_eq!(events[2].id, 2);
    assert_eq!(events[3].id, 11);
    assert_eq!(trace.len(), 3);
}
