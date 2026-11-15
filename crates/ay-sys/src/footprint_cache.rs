// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The advisory memory probe's footprint reading, cached (roadmap D5: "the
//! memory probe is a cached atomic").
//!
//! [`crate::process_memory_exceeded`] is polled from every solver
//! cancellation checkpoint, and each poll read the footprint with a
//! `task_info` system call (a `/proc/self/statm` read on Linux). A reading at
//! most [`FOOTPRINT_TTL`] old now answers instead. The advisory can trip that
//! much later than before; bursts between polls were never its job — the
//! allocator's hard ceiling refuses those synchronously on live bytes — and
//! the memory watchdog, which polls every 100 ms, always sees a fresh reading.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

/// How old a cached footprint reading may be before it is read again.
pub(crate) const FOOTPRINT_TTL: Duration = Duration::from_millis(2);

static EPOCH: OnceLock<Instant> = OnceLock::new();
static BYTES: AtomicUsize = AtomicUsize::new(0);
/// When [`BYTES`] was read, in nanoseconds after [`EPOCH`] plus one; zero
/// means never.
static READ_AT: AtomicU64 = AtomicU64::new(0);
static READING: AtomicBool = AtomicBool::new(false);

/// The process footprint, read at most [`FOOTPRINT_TTL`] ago.
pub(crate) fn cached_footprint_bytes() -> usize {
    cached_with(crate::current_footprint_bytes)
}

fn cached_with(read: impl FnOnce() -> usize) -> usize {
    let epoch = *EPOCH.get_or_init(Instant::now);
    cached_slot(
        &READING,
        &READ_AT,
        &BYTES,
        || {
            u64::try_from(epoch.elapsed().as_nanos())
                .unwrap_or(u64::MAX - 1)
                .saturating_add(1)
        },
        read,
    )
}

/// A reader owns both fields until it publishes the same measurement's bytes
/// and timestamp. A competing reader takes its own fresh measurement rather
/// than waiting for a possibly slow operating-system probe.
struct ReadingLease<'a>(&'a AtomicBool);

impl Drop for ReadingLease<'_> {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}

fn cached_slot(
    reading: &AtomicBool,
    read_at: &AtomicU64,
    bytes_slot: &AtomicUsize,
    clock: impl FnOnce() -> u64,
    read: impl FnOnce() -> usize,
) -> usize {
    if reading
        .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        return read();
    }
    let _lease = ReadingLease(reading);
    let now = clock();
    let at = read_at.load(Ordering::Relaxed);
    let ttl = u64::try_from(FOOTPRINT_TTL.as_nanos()).unwrap_or(u64::MAX);
    if at != 0 && now >= at && now - at < ttl {
        return bytes_slot.load(Ordering::Relaxed);
    }
    let bytes = read();
    bytes_slot.store(bytes, Ordering::Relaxed);
    read_at.store(now, Ordering::Relaxed);
    bytes
}

#[cfg(test)]
#[path = "footprint_cache/publication_tests.rs"]
mod publication_tests;
