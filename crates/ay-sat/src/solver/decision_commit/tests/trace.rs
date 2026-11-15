// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::{DecisionTraceWriter, ReplayTrace};

mod unwind;

fn traced_fixture(path: &std::path::Path) -> Solver {
    let mut s = fixture();
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold.replay_trace = Some(ReplayTrace::decision_test_new(vec![TraceEvent::Decide {
        lit_dimacs: 4,
    }]));
    s
}

fn cursor(s: &Solver) -> usize {
    s.cold.replay_trace.as_ref().unwrap().decision_test_cursor()
}

#[test]
fn actual_trace_and_replay_match_ordinary_decision_bytes_and_capacity() {
    let directory = tempfile::tempdir().unwrap();
    let ordinary_path = directory.path().join("ordinary");
    let counted_path = directory.path().join("counted");
    let mut ordinary = traced_fixture(&ordinary_path);
    let mut counted = traced_fixture(&counted_path);
    let capacity = counted
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot()
        .2;
    attach(&mut counted, &test_owner(10_000, 10_000));
    ordinary.decide(lit(3));
    assert_eq!(counted.decide_counted(lit(3)), Ok(()));
    assert_eq!(state(&counted), state(&ordinary));
    assert_eq!(cursor(&counted), 1);
    assert_eq!(cursor(&ordinary), 1);
    let actual = counted
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    let expected = ordinary
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    assert_eq!(actual, expected);
    assert_eq!(actual, (1, vec![1, 4, 0, 0, 0], capacity));
    counted
        .cold
        .decision_trace
        .as_mut()
        .unwrap()
        .finish()
        .unwrap();
    ordinary
        .cold
        .decision_trace
        .as_mut()
        .unwrap()
        .finish()
        .unwrap();
    assert_eq!(
        std::fs::read(counted_path).unwrap(),
        std::fs::read(ordinary_path).unwrap()
    );
}

#[test]
fn preflight_refusal_retires_pending_writer_before_solver_drop_can_flush() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("pending");
    let mut s = traced_fixture(&path);
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    assert_eq!(
        s.cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot()
            .1
            .len(),
        5
    );
    let written = std::fs::metadata(&path).unwrap().len();
    assert_eq!(written, 9);
    let before = state(&s);
    attach(&mut s, &test_owner(0, 0));
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), before);
    assert_eq!(cursor(&s), 0);
    assert!(s.cold.decision_trace.is_none());
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), written);
}

#[test]
fn replay_mismatch_refuses_without_assignment_or_trace_and_stays_terminal() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("mismatch");
    let mut s = traced_fixture(&path);
    s.cold.replay_trace = Some(ReplayTrace::decision_test_new(vec![TraceEvent::Reduce {
        clause_ids: (0..4096).collect(),
    }]));
    let before = state(&s);
    let owner = test_owner(10_000, 10_000);
    attach(&mut s, &owner);
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), before);
    assert_eq!(cursor(&s), 0);
    assert!(s.cold.decision_trace.is_none());
    assert!(matches!(
        owner.check(),
        Err(CountedAdmissionError::Original(_))
    ));
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), before);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn actual_file_write_failure_leaves_a_complete_assignment_and_retires_writer() {
    let file = tempfile::NamedTempFile::new().unwrap();
    let read_only = std::fs::File::open(file.path()).unwrap();
    let mut expected = fixture();
    expected.decide(lit(3));
    let mut s = fixture();
    s.cold.decision_trace = Some(DecisionTraceWriter::decision_test_read_only(read_only));
    s.cold.replay_trace = Some(ReplayTrace::decision_test_new(vec![TraceEvent::Decide {
        lit_dimacs: 4,
    }]));
    let owner = test_owner(10_000, 10_000);
    attach(&mut s, &owner);
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), state(&expected));
    assert_eq!(cursor(&s), 1);
    assert!(s.cold.decision_trace.is_none());
    assert!(matches!(
        owner.check(),
        Err(CountedAdmissionError::Original(_))
    ));
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), state(&expected));
    drop(s);
    assert_eq!(file.as_file().metadata().unwrap().len(), 0);
}

#[test]
fn every_trace_observer_cut_preserves_replay_position_and_retires_without_flush() {
    let directory = tempfile::tempdir().unwrap();
    let mut baseline = traced_fixture(&directory.path().join("baseline"));
    let calls = Arc::new(AtomicUsize::new(0));
    attach(
        &mut baseline,
        &controls::observing_owner(usize::MAX, &calls),
    );
    assert_eq!(baseline.decide_counted(lit(3)), Ok(()));
    let total = calls.load(Ordering::SeqCst);
    for stop_at in 0..total {
        let path = directory.path().join(format!("cut-{stop_at}"));
        let mut s = traced_fixture(&path);
        let before = state(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        attach(&mut s, &controls::observing_owner(stop_at, &calls));
        assert_eq!(s.decide_counted(lit(3)), Err(SatUnknownReason::Interrupted));
        let committed = stop_at + 1 == total;
        assert_eq!(state(&s), if committed { state(&baseline) } else { before });
        assert_eq!(cursor(&s), usize::from(committed));
        assert!(s.cold.decision_trace.is_none());
        drop(s);
        assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    }
}

#[test]
fn actual_triage_output_is_paid_before_assignment_and_short_grants_refuse() {
    let mut flags = ay_core::misc_cli_flags().clone();
    flags.ab_triage_var = Some(4);
    let _scope = ay_core::misc_test_override::set(flags);
    let mut baseline = fixture();
    let owner = test_owner(10_000, 10_000);
    attach(&mut baseline, &owner);
    assert_eq!(baseline.decide_counted(lit(3)), Ok(()));
    let used = owner.usage().unwrap();
    assert!(used.storage_admitted >= 512);
    for (work, storage, admitted) in [
        (used.work_admitted, used.storage_admitted, true),
        (used.work_admitted - 1, used.storage_admitted, false),
        (used.work_admitted, used.storage_admitted - 1, false),
    ] {
        let mut s = fixture();
        let before = state(&s);
        attach(&mut s, &test_owner(work, storage));
        if admitted {
            assert_eq!(s.decide_counted(lit(3)), Ok(()));
            assert_eq!(state(&s), state(&baseline));
        } else {
            assert_eq!(
                s.decide_counted(lit(3)),
                Err(SatUnknownReason::ResourceBudget)
            );
            assert_eq!(state(&s), before);
        }
    }
}

#[cfg(ay_logging)]
#[test]
fn actual_logging_is_paid_and_retained_by_counted_decisions() {
    let mut baseline = fixture();
    baseline.log_enabled = true;
    let owner = test_owner(10_000, 10_000);
    attach(&mut baseline, &owner);
    assert_eq!(baseline.decide_counted(lit(3)), Ok(()));
    let used = owner.usage().unwrap();
    assert!(used.storage_admitted >= 512);
    let mut refused = fixture();
    refused.log_enabled = true;
    let before = state(&refused);
    attach(
        &mut refused,
        &test_owner(used.work_admitted, used.storage_admitted - 1),
    );
    assert_eq!(
        refused.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&refused), before);
    assert!(refused.log_enabled);
}
