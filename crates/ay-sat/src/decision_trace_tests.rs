// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_trace_binary_round_trip_all_event_types() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("decision.trace");

    let mut writer =
        DecisionTraceWriter::new(path.to_str().expect("utf8 path")).expect("create trace writer");
    let expected = vec![
        TraceEvent::Decide { lit_dimacs: 1 },
        TraceEvent::Propagate {
            lit_dimacs: -2,
            clause_id: 11,
        },
        TraceEvent::Conflict { clause_id: 11 },
        TraceEvent::Learn { clause_id: 12 },
        TraceEvent::Restart,
        TraceEvent::Reduce {
            clause_ids: vec![7, 8, 9],
        },
        TraceEvent::Inprocess { pass_code: 4 },
        TraceEvent::Result {
            outcome: SolveOutcome::Unsat,
        },
    ];
    for event in &expected {
        writer.write_event(event).expect("write event");
    }
    assert_eq!(writer.finish().expect("flush trace"), expected.len() as u64);

    let loaded = read_trace(path.to_str().expect("utf8 path")).expect("read trace");
    assert_eq!(loaded, expected);
}

#[test]
fn test_replay_trace_detects_divergence() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("decision.trace");

    let mut writer =
        DecisionTraceWriter::new(path.to_str().expect("utf8 path")).expect("create trace writer");
    writer
        .write_event(&TraceEvent::Decide { lit_dimacs: 3 })
        .expect("write event");
    writer
        .write_event(&TraceEvent::Result {
            outcome: SolveOutcome::Sat,
        })
        .expect("write event");
    writer.finish().expect("flush trace");

    let mut replay =
        ReplayTrace::from_file(path.to_str().expect("utf8 path")).expect("load replay trace");
    let mismatch = replay
        .expect(&TraceEvent::Decide { lit_dimacs: -3 })
        .expect_err("expected mismatch");
    assert_eq!(mismatch.position, 0);
    assert_eq!(
        mismatch.expected,
        Some(TraceEvent::Decide { lit_dimacs: 3 })
    );
}
