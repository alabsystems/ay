// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

#[test]
fn test_replay_trace_round_trip_empty() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("trace.ayrt");

    // Write empty trace
    let mut writer = ReplayTraceWriter::new(&path, 10).unwrap();
    let count = writer.finish();
    assert_eq!(count, 0);

    // Read back
    let mut reader = ReplayTraceReader::open(&path).unwrap();
    assert_eq!(reader.num_vars(), 10);
    let events = reader.read_all().unwrap();
    assert!(events.is_empty());
}

#[test]
fn test_replay_trace_round_trip_events() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("trace.ayrt");

    let lit_x0 = Literal::positive(Variable(0));
    let lit_x1_neg = Literal::negative(Variable(1));
    let lit_x2 = Literal::positive(Variable(2));

    // Write events
    let mut writer = ReplayTraceWriter::new(&path, 5).unwrap();
    writer.write_decide(lit_x0);
    writer.write_decide(lit_x1_neg);
    writer.write_conflict(42);
    writer.write_learn(3, &[lit_x2, lit_x0]);
    writer.write_restart();
    writer.write_reduce_db(17);
    let count = writer.finish();
    assert_eq!(count, 6);

    // Read back and verify
    let mut reader = ReplayTraceReader::open(&path).unwrap();
    assert_eq!(reader.num_vars(), 5);

    let events = reader.read_all().unwrap();
    assert_eq!(events.len(), 6);
    assert_eq!(events[0], TraceEvent::Decide(lit_x0));
    assert_eq!(events[1], TraceEvent::Decide(lit_x1_neg));
    assert_eq!(events[2], TraceEvent::Conflict(42));
    assert_eq!(
        events[3],
        TraceEvent::Learn {
            lbd: 3,
            clause: vec![lit_x2, lit_x0],
        }
    );
    assert_eq!(events[4], TraceEvent::Restart);
    assert_eq!(events[5], TraceEvent::ReduceDb(17));
    assert_eq!(reader.events_read(), 6);
}

#[test]
fn test_replay_trace_invalid_magic() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("bad.ayrt");
    std::fs::write(&path, b"NOPE\x01\x05\x00\x00\x00").unwrap();

    let err = ReplayTraceReader::open(&path).unwrap_err();
    assert!(err.to_string().contains("invalid replay trace magic"));
}

#[test]
fn test_replay_trace_file_size_estimate() {
    // Verify the ~100 bytes/conflict size estimate from the issue.
    // Per conflict: 1 Decide (5B) + 1 Conflict (5B) + 1 Learn (5B + avg 10 lits * 4B = 45B)
    // ≈ 55 bytes. With restarts every ~100 conflicts and DB reductions, average ~60-70B.
    // Well under the 200MB budget for 1M conflicts.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("size_test.ayrt");

    let lit = Literal::positive(Variable(0));
    let clause: Vec<Literal> = (0..10).map(|i| Literal::positive(Variable(i))).collect();

    let mut writer = ReplayTraceWriter::new(&path, 100).unwrap();
    // Simulate 1000 conflicts
    for _ in 0..1000 {
        writer.write_decide(lit);
        writer.write_conflict(0);
        writer.write_learn(3, &clause);
    }
    // Add some restarts and reductions
    for _ in 0..10 {
        writer.write_restart();
        writer.write_reduce_db(50);
    }
    writer.finish();

    let size = std::fs::metadata(&path).unwrap().len();
    // 1000 conflicts should be well under 200KB
    assert!(
        size < 200_000,
        "trace size {size} exceeds 200KB for 1000 conflicts"
    );
    // Extrapolation: 1M conflicts ≈ size * 1000 < 200MB
    let estimated_1m = size * 1000;
    assert!(
        estimated_1m < 200_000_000,
        "estimated 1M-conflict trace size {estimated_1m} exceeds 200MB"
    );
}
