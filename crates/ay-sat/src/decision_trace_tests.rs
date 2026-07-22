// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn replay_load_error(path: &str) -> io::Error {
    ReplayTrace::from_file(path)
        .err()
        .expect("replay load unexpectedly succeeded")
}

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

#[test]
fn test_replay_trace_rejects_oversized_reduce_before_allocation() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("oversized_reduce.trace");
    let mut bytes = Vec::from(*MAGIC);
    bytes.push(VERSION);
    bytes.push(TAG_REDUCE);
    bytes.extend_from_slice(&u32::MAX.to_le_bytes());
    std::fs::write(&path, bytes).expect("write malformed trace");

    let error = replay_load_error(path.to_str().expect("utf8 path"));
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(
        error.to_string().contains("reduction contains"),
        "unexpected error: {error}"
    );
}

#[test]
fn test_replay_trace_rejects_trailing_data_after_result() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("trailing.trace");
    let path_str = path.to_str().expect("utf8 path");
    let mut writer = DecisionTraceWriter::new(path_str).expect("create trace writer");
    writer
        .write_event(&TraceEvent::Result {
            outcome: SolveOutcome::Sat,
        })
        .expect("write result");
    writer.finish().expect("flush trace");
    drop(writer);

    let mut file = OpenOptions::new()
        .append(true)
        .open(&path)
        .expect("open trace for append");
    file.write_all(&[TAG_RESTART])
        .expect("append trailing byte");
    file.flush().expect("flush trailing byte");

    let error = replay_load_error(path_str);
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(
        error.to_string().contains("trailing data"),
        "unexpected error: {error}"
    );
}

#[test]
fn test_replay_trace_byte_limit_is_enforced() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("byte_limit.trace");
    let path_str = path.to_str().expect("utf8 path");
    write_minimal_trace(path_str, TraceOutcome::Unknown).expect("write trace");
    let length = std::fs::metadata(&path).expect("trace metadata").len();
    let limits = ReplayLimits {
        max_bytes: length - 1,
        ..REPLAY_LIMITS
    };

    let error = read_trace_with_limits(path_str, limits).expect_err("byte limit must be enforced");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(
        error.to_string().contains("replay byte limit"),
        "unexpected error: {error}"
    );
}

#[test]
fn test_replay_trace_event_limit_is_enforced() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("event_limit.trace");
    let path_str = path.to_str().expect("utf8 path");
    let mut writer = DecisionTraceWriter::new(path_str).expect("create trace writer");
    writer
        .write_event(&TraceEvent::Restart)
        .expect("write restart");
    writer
        .write_event(&TraceEvent::Result {
            outcome: SolveOutcome::Unknown,
        })
        .expect("write result");
    writer.finish().expect("flush trace");
    drop(writer);
    let limits = ReplayLimits {
        max_events: 1,
        ..REPLAY_LIMITS
    };

    let error = read_trace_with_limits(path_str, limits).expect_err("event limit must be enforced");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(
        error.to_string().contains("more than 1 events"),
        "unexpected error: {error}"
    );
}

#[test]
fn test_replay_trace_requires_terminal_result() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("incomplete.trace");
    let path_str = path.to_str().expect("utf8 path");
    let mut writer = DecisionTraceWriter::new(path_str).expect("create trace writer");
    writer
        .write_event(&TraceEvent::Restart)
        .expect("write restart");
    writer.finish().expect("flush trace");
    drop(writer);

    assert_eq!(
        read_trace(path_str).expect("partial trace remains inspectable"),
        vec![TraceEvent::Restart]
    );
    let error = replay_load_error(path_str);
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(
        error.to_string().contains("missing its terminal result"),
        "unexpected error: {error}"
    );
}

#[cfg(unix)]
#[test]
fn test_replay_trace_rejects_fifo_without_blocking() {
    use std::time::{Duration, Instant};

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("replay.fifo");
    let status = std::process::Command::new("mkfifo")
        .arg(&path)
        .status()
        .expect("run mkfifo");
    assert!(status.success(), "mkfifo failed with {status}");

    let started = Instant::now();
    let error = replay_load_error(path.to_str().expect("utf8 path"));
    assert!(
        started.elapsed() < Duration::from_secs(1),
        "FIFO rejection unexpectedly blocked"
    );
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
}

#[cfg(unix)]
#[test]
fn test_replay_trace_rejects_device() {
    let error = replay_load_error("/dev/null");
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
}

#[cfg(unix)]
#[test]
fn test_replay_trace_rejects_symlink() {
    use std::os::unix::fs::symlink;

    let dir = tempfile::tempdir().expect("tempdir");
    let target = dir.path().join("target.trace");
    let link = dir.path().join("link.trace");
    write_minimal_trace(target.to_str().expect("utf8 path"), TraceOutcome::Unknown)
        .expect("write trace");
    symlink(&target, &link).expect("create symlink");

    let error = replay_load_error(link.to_str().expect("utf8 path"));
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
}

#[cfg(unix)]
#[test]
fn test_reserved_trace_lifecycle_rejects_tampering_and_releases_every_reservation() {
    use std::io::Write as _;
    use std::os::unix::fs::PermissionsExt as _;

    let dir = tempfile::tempdir().expect("tempdir");
    let tampered_path = dir.path().join("tampered.trace");
    let tampered_path_str = tampered_path.to_str().expect("utf8 path");
    reserve_decision_trace(tampered_path_str).expect("reserve same-run trace");
    assert_eq!(
        std::fs::metadata(&tampered_path)
            .expect("reserved trace metadata")
            .permissions()
            .mode()
            & 0o077,
        0,
        "decision trace must not grant group or other permissions"
    );

    OpenOptions::new()
        .write(true)
        .open(&tampered_path)
        .expect("open trace for in-place tampering")
        .write_all(b"X")
        .expect("tamper with trace magic");
    let error = finish_reserved_decision_trace(tampered_path_str, TraceOutcome::Unsat)
        .expect_err("in-place tampering must invalidate same-run output");
    assert!(
        error.to_string().contains("magic mismatch"),
        "unexpected in-place tampering error: {error}"
    );

    let replaced_path = dir.path().join("replaced-before-finish.trace");
    let replaced_path_str = replaced_path.to_str().expect("utf8 replacement path");
    reserve_decision_trace(replaced_path_str).expect("reserve trace to replace");
    std::fs::remove_file(&replaced_path).expect("unlink reserved trace name");
    let stale = b"AYDTRC1\0\x01\x08\x01";
    std::fs::write(&replaced_path, stale).expect("replace with stale valid trace");

    let error = finish_reserved_decision_trace(replaced_path_str, TraceOutcome::Unsat)
        .expect_err("replacement must not authenticate as same-run output");
    assert!(
        error.to_string().contains("replaced"),
        "unexpected replacement error: {error}"
    );
    assert_eq!(
        std::fs::read(&replaced_path).expect("read replacement"),
        stale,
        "failed authentication must not rewrite the replacement"
    );

    let retained_after_mismatch = dir.path().join("retained-after-path-mismatch.trace");
    let retained_after_mismatch_str = retained_after_mismatch
        .to_str()
        .expect("utf8 retained mismatch path");
    let wrong_path = dir.path().join("wrong-path.trace");
    reserve_decision_trace(retained_after_mismatch_str)
        .expect("reserve trace before mismatched finish path");
    let error = finish_reserved_decision_trace(
        wrong_path.to_str().expect("utf8 wrong path"),
        TraceOutcome::Unsat,
    )
    .expect_err("mismatched finish path must not consume the reservation");
    assert!(
        error.to_string().contains("differs from reserved path"),
        "unexpected mismatched path error: {error}"
    );
    finish_reserved_decision_trace(retained_after_mismatch_str, TraceOutcome::Unsat)
        .expect("the correctly named finish must retain authority");
    assert_eq!(
        std::fs::read(&retained_after_mismatch).expect("read retained mismatch trace"),
        b"AYDTRC1\0\x01\x08\x01"
    );

    let first_finished = dir.path().join("first-finished.trace");
    let first_finished_str = first_finished.to_str().expect("utf8 first path");
    reserve_decision_trace(first_finished_str).expect("reserve first successful trace");
    finish_reserved_decision_trace(first_finished_str, TraceOutcome::Unknown)
        .expect("finish first successful trace");
    assert_eq!(
        std::fs::read(&first_finished).expect("read first successful trace"),
        b"AYDTRC1\0\x01\x08\x02"
    );

    let second_finished = dir.path().join("second-finished.trace");
    let second_finished_str = second_finished.to_str().expect("utf8 second path");
    reserve_decision_trace(second_finished_str).expect("reserve second successful trace");
    finish_reserved_decision_trace(second_finished_str, TraceOutcome::Unsat)
        .expect("finish second successful trace");
    assert_eq!(
        std::fs::read(&second_finished).expect("read second successful trace"),
        b"AYDTRC1\0\x01\x08\x01"
    );

    let retained_finished = dir.path().join("retained-finished.trace");
    let retained_finished_str = retained_finished.to_str().expect("utf8 retained path");
    reserve_decision_trace(retained_finished_str).expect("reserve retained trace");
    let mut retained =
        finish_reserved_decision_trace_retained(retained_finished_str, TraceOutcome::Unsat)
            .expect("settle retained trace");
    retained
        .validate()
        .expect("same-run retained trace must validate");
    retained.commit();
    drop(retained);
    assert_eq!(
        std::fs::read(&retained_finished).expect("read committed retained trace"),
        b"AYDTRC1\0\x01\x08\x01"
    );

    let replaced_after_settle = dir.path().join("replaced-after-settle.trace");
    let replaced_after_settle_str = replaced_after_settle
        .to_str()
        .expect("utf8 post-settlement path");
    let displaced_after_settle = dir.path().join("same-run-settled.trace");
    reserve_decision_trace(replaced_after_settle_str).expect("reserve rollback trace");
    let retained =
        finish_reserved_decision_trace_retained(replaced_after_settle_str, TraceOutcome::Unsat)
            .expect("settle rollback trace");
    std::fs::rename(&replaced_after_settle, &displaced_after_settle)
        .expect("displace same-run settled trace");
    std::fs::write(&replaced_after_settle, b"foreign replacement")
        .expect("write foreign trace replacement");
    retained
        .validate()
        .expect_err("replacement must revoke retained trace authority");
    drop(retained);
    assert_eq!(
        std::fs::read(&displaced_after_settle).expect("read invalidated same-run trace"),
        b""
    );
    assert_eq!(
        std::fs::read(&replaced_after_settle).expect("read foreign replacement"),
        b"foreign replacement"
    );

    let invalidated_path = dir.path().join("invalidated.trace");
    let invalidated_path_str = invalidated_path.to_str().expect("utf8 invalidation path");
    reserve_decision_trace(invalidated_path_str).expect("reserve trace to invalidate");
    invalidate_reserved_decision_trace(invalidated_path_str).expect("invalidate retained trace");
    assert!(
        invalidated_path.exists(),
        "invalidation must not unlink the path"
    );
    assert_eq!(
        std::fs::metadata(&invalidated_path)
            .expect("invalidated metadata")
            .len(),
        0,
        "invalidated trace must be non-replayable"
    );
    invalidate_reserved_decision_trace(invalidated_path_str)
        .expect("repeated invalidation of an empty trace is idempotent");

    let invalidate_replaced_path = dir.path().join("replaced-before-invalidation.trace");
    let invalidate_replaced_str = invalidate_replaced_path
        .to_str()
        .expect("utf8 replaced invalidation path");
    let displaced_invalidation_path = dir.path().join("same-run-before-invalidation.trace");
    reserve_decision_trace(invalidate_replaced_str).expect("reserve trace before replacement");
    let mut writer =
        DecisionTraceWriter::new(invalidate_replaced_str).expect("claim trace before replacement");
    writer
        .write_event(&TraceEvent::Result {
            outcome: SolveOutcome::Unsat,
        })
        .expect("write terminal trace before replacement");
    writer.finish().expect("flush trace before replacement");
    drop(writer);
    std::fs::rename(&invalidate_replaced_path, &displaced_invalidation_path)
        .expect("displace same-run trace before invalidation");
    let replacement = b"replacement must not be truncated";
    std::fs::write(&invalidate_replaced_path, replacement).expect("install replacement");
    let error = invalidate_reserved_decision_trace(invalidate_replaced_str)
        .expect_err("replacement must fail authenticated invalidation");
    assert!(
        error.to_string().contains("replaced"),
        "unexpected invalidation replacement error: {error}"
    );
    assert_eq!(
        std::fs::read(&invalidate_replaced_path).expect("read invalidation replacement"),
        replacement,
        "authenticated invalidation changed a replacement"
    );
    assert_eq!(
        std::fs::read(&displaced_invalidation_path).expect("read displaced same-run trace"),
        b"",
        "failed namespace authentication left the exact same-run trace replayable"
    );
}

#[cfg(unix)]
#[test]
fn test_failed_creation_invalidation_never_removes_replacement() {
    let dir = tempfile::tempdir().expect("tempdir");

    let owned_path = dir.path().join("owned.trace");
    let owned = open_new_decision_trace(&owned_path).expect("create owned trace");
    assert!(
        invalidate_failed_decision_trace_creation(&owned_path, &owned)
            .expect("invalidate owned trace"),
        "descriptor-owned destination should be invalidated"
    );
    assert!(
        owned_path.exists(),
        "failed creation invalidation must not unlink the path"
    );
    assert_eq!(
        std::fs::metadata(&owned_path)
            .expect("invalidated creation metadata")
            .len(),
        0,
        "failed creation must leave a zero-length, non-replayable file"
    );

    let replaced_path = dir.path().join("replaced.trace");
    let replaced = open_new_decision_trace(&replaced_path).expect("create trace to replace");
    std::fs::remove_file(&replaced_path).expect("unlink descriptor-owned path");
    let replacement = b"replacement must survive";
    std::fs::write(&replaced_path, replacement).expect("create replacement");
    assert!(
        !invalidate_failed_decision_trace_creation(&replaced_path, &replaced)
            .expect("authenticate invalidation target"),
        "invalidation must refuse a replacement inode"
    );
    assert_eq!(
        std::fs::read(&replaced_path).expect("read replacement"),
        replacement,
        "invalidation removed or changed a replacement"
    );
}
