// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;

#[test]
fn replay_preflight_borrows_large_mismatch_payload_and_never_advances_it() {
    let ids: Vec<_> = (0..4096).collect();
    let pointer = ids.as_ptr();
    let replay = ReplayTrace::decision_test_new(vec![TraceEvent::Reduce { clause_ids: ids }]);
    let owner = test_owner(1, 0);
    assert!(replay.admit_decision(1, &owner).is_err());
    assert_eq!(replay.cursor, 0);
    match &replay.events[0] {
        TraceEvent::Reduce { clause_ids } => assert_eq!(clause_ids.as_ptr(), pointer),
        _ => unreachable!(),
    }
    assert!(matches!(
        owner.check(),
        Err(CountedAdmissionError::Original(_))
    ));
}

#[test]
fn replay_success_and_end_mismatch_preserve_exact_position() {
    let mut replay = ReplayTrace::decision_test_new(vec![TraceEvent::Decide { lit_dimacs: -7 }]);
    let owner = test_owner(1, 0);
    assert_eq!(replay.admit_decision(-7, &owner), Ok(()));
    assert_eq!(replay.cursor, 0);
    assert!(replay.commit_admitted_decision(-7));
    assert_eq!(replay.cursor, 1);
    assert!(!replay.commit_admitted_decision(-7));
    let mismatch_owner = test_owner(1, 0);
    assert!(replay.admit_decision(1, &mismatch_owner).is_err());
    assert_eq!(replay.cursor, 1);
}

#[test]
fn actual_trace_buffer_and_periodic_flush_match_ordinary_without_growth() {
    for (pending, count) in [(0, 0), (14, 0), (3, 1023)] {
        let file = tempfile::tempfile().unwrap();
        let mut actual = DecisionTraceWriter {
            writer: BufWriter::with_capacity(16, file),
            event_count: count,
        };
        let file = tempfile::tempfile().unwrap();
        let mut expected = DecisionTraceWriter {
            writer: BufWriter::with_capacity(16, file),
            event_count: count,
        };
        actual.writer.write_all(&vec![9; pending]).unwrap();
        expected.writer.write_all(&vec![9; pending]).unwrap();
        let before = actual.decision_test_snapshot();
        let owner = test_owner(10_000, 5);
        actual.admit_decision(&owner).unwrap();
        assert_eq!(actual.decision_test_snapshot(), before);
        let event = TraceEvent::Decide { lit_dimacs: -123 };
        actual.write_event(&event).unwrap();
        expected.write_event(&event).unwrap();
        assert_eq!(
            actual.decision_test_snapshot(),
            expected.decision_test_snapshot()
        );
        assert_eq!(actual.writer.capacity(), 16);
        actual.finish().unwrap();
        expected.finish().unwrap();
        actual.writer.get_mut().rewind().unwrap();
        expected.writer.get_mut().rewind().unwrap();
        let mut actual_bytes = Vec::new();
        let mut expected_bytes = Vec::new();
        actual
            .writer
            .get_mut()
            .read_to_end(&mut actual_bytes)
            .unwrap();
        expected
            .writer
            .get_mut()
            .read_to_end(&mut expected_bytes)
            .unwrap();
        assert_eq!(actual_bytes, expected_bytes);
        assert_eq!(&actual_bytes[pending..], &[TAG_DECIDE, 133, 255, 255, 255]);
        assert_eq!(owner.usage().unwrap().storage_remaining, 0);
    }
}

#[test]
fn trace_exact_and_short_costs_leave_buffer_and_counter_untouched() {
    let mut writer = DecisionTraceWriter {
        writer: BufWriter::with_capacity(16, tempfile::tempfile().unwrap()),
        event_count: 1023,
    };
    writer.writer.write_all(&[4; 10]).unwrap();
    let before = writer.decision_test_snapshot();
    let generous = test_owner(1_000, 1_000);
    writer.admit_decision(&generous).unwrap();
    let usage = generous.usage().unwrap();
    for (work, storage, admitted) in [
        (usage.work_admitted, 5, true),
        (usage.work_admitted - 1, 5, false),
        (usage.work_admitted, 4, false),
    ] {
        let owner = test_owner(work, storage);
        assert_eq!(writer.admit_decision(&owner).is_ok(), admitted);
        assert_eq!(writer.decision_test_snapshot(), before);
    }
}

#[test]
fn retiring_exact_descriptor_discards_buffer_without_implicit_flush() {
    let file = tempfile::tempfile().unwrap();
    let retained = file.try_clone().unwrap();
    let mut writer = DecisionTraceWriter {
        writer: BufWriter::with_capacity(16, file),
        event_count: 0,
    };
    writer
        .write_event(&TraceEvent::Decide { lit_dimacs: 2 })
        .unwrap();
    assert_eq!(writer.writer.buffer().len(), 5);
    writer.discard_without_flush();
    assert_eq!(retained.metadata().unwrap().len(), 0);
}
