// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::{mpsc, Arc};

#[test]
fn a_fresh_reading_answers_and_a_stale_one_is_read_again() {
    let reading = AtomicBool::new(false);
    let at = AtomicU64::new(0);
    let bytes = AtomicUsize::new(0);
    let reads = std::cell::Cell::new(0);
    let sample = |now, value| {
        cached_slot(
            &reading,
            &at,
            &bytes,
            || now,
            || {
                reads.set(reads.get() + 1);
                value
            },
        )
    };
    let ttl = u64::try_from(FOOTPRINT_TTL.as_nanos()).unwrap();
    assert_eq!(sample(1, 4096), 4096);
    assert_eq!(reads.get(), 1);
    // One nanosecond before expiry: no probe and no competing global cache.
    assert_eq!(sample(ttl, 8192), 4096);
    assert_eq!(reads.get(), 1);
    // Exactly TTL old: refresh once, without sleeping on the machine clock.
    assert_eq!(sample(ttl + 1, 8192), 8192);
    assert_eq!(reads.get(), 2);
}

#[test]
fn a_competing_reader_measures_without_waiting_or_publishing_a_mixed_pair() {
    let state = Arc::new((
        AtomicBool::new(false),
        AtomicU64::new(1),
        AtomicUsize::new(4096),
    ));
    let writer_state = Arc::clone(&state);
    let (entered_tx, entered_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let writer = std::thread::spawn(move || {
        cached_slot(
            &writer_state.0,
            &writer_state.1,
            &writer_state.2,
            || 9_000_000,
            || {
                entered_tx.send(()).unwrap();
                release_rx.recv_timeout(Duration::from_secs(2)).unwrap();
                8192
            },
        )
    });
    entered_rx.recv_timeout(Duration::from_secs(2)).unwrap();
    // The writer is still inside its operating-system probe. This reader
    // must see its own fresh value, not the old bytes or a partial publication.
    assert_eq!(
        cached_slot(&state.0, &state.1, &state.2, || 9_000_001, || 16384),
        16384
    );
    assert!(state.0.load(Ordering::Relaxed));
    assert_eq!(state.1.load(Ordering::Relaxed), 1);
    assert_eq!(state.2.load(Ordering::Relaxed), 4096);
    release_tx.send(()).unwrap();
    assert_eq!(writer.join().unwrap(), 8192);
    assert!(!state.0.load(Ordering::Relaxed));
    assert_eq!(state.1.load(Ordering::Relaxed), 9_000_000);
    assert_eq!(state.2.load(Ordering::Relaxed), 8192);
    assert_eq!(
        cached_slot(&state.0, &state.1, &state.2, || 9_000_002, || 32768),
        8192
    );
}

#[test]
fn a_probe_that_unwinds_does_not_leave_the_shared_reader_slot_owned() {
    let reading = AtomicBool::new(false);
    let at = AtomicU64::new(0);
    let bytes = AtomicUsize::new(4096);
    let failed = std::panic::catch_unwind(|| {
        cached_slot(&reading, &at, &bytes, || 1, || panic!("probe refused"))
    });
    assert!(failed.is_err());
    assert!(!reading.load(Ordering::Relaxed));
    assert_eq!(at.load(Ordering::Relaxed), 0);
    assert_eq!(bytes.load(Ordering::Relaxed), 4096);
    assert_eq!(cached_slot(&reading, &at, &bytes, || 2, || 8192), 8192);
    assert_eq!(at.load(Ordering::Relaxed), 2);
}

#[test]
fn a_backwards_clock_never_marks_a_future_measurement_fresh() {
    let reading = AtomicBool::new(false);
    let at = AtomicU64::new(100);
    let bytes = AtomicUsize::new(4096);
    assert_eq!(cached_slot(&reading, &at, &bytes, || 99, || 8192), 8192);
    assert_eq!(at.load(Ordering::Relaxed), 99);
    assert_eq!(bytes.load(Ordering::Relaxed), 8192);
}
