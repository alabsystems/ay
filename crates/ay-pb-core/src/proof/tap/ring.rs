// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded SPSC byte ring for proof-tap micro-op records.
//!
//! One producer (the solver thread) and one consumer (the serializer thread)
//! share a power-of-two byte buffer with free-running head/tail counters.
//! The producer writes a whole length-prefixed record and publishes it with a
//! single release-store of `tail`, so the consumer only ever observes whole
//! records; wrap-around is byte-granular (no pad records needed).
//!
//! Backpressure is the spec's BOUNDED-THROTTLE-THEN-FAIL-CLOSED policy: a
//! full ring parks the producer in bounded condvar waits (default 250 ms
//! quantum) charged against a per-solve stall budget; exhausting the budget —
//! or a dead consumer, or a record that can never fit — surfaces an error so
//! the caller can VOID the proof and continue solving unlogged. Records are
//! never dropped, truncated, or reordered.
//!
//! The byte buffer is `AtomicU8`s written/read with relaxed ordering; the
//! release-store/acquire-load pair on `tail` (and symmetrically `head`)
//! provides the necessary happens-before edges without `unsafe`.

use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use super::varint::{decode_u64, encode_u64};

/// Default ring capacity (16 MiB, spec "Ring architecture").
pub(crate) const DEFAULT_RING_CAPACITY: usize = 16 << 20;

/// Bounded wait quantum while the ring is full.
const FULL_WAIT_QUANTUM: Duration = Duration::from_millis(250);

/// Consumer wait quantum while the ring is empty (also woken explicitly).
const EMPTY_WAIT_QUANTUM: Duration = Duration::from_millis(100);

/// Producer-side push failure. All variants are fail-closed: the record was
/// NOT written and the ring is unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RingPushError {
    /// The consumer is gone; nothing will ever drain the ring.
    ConsumerGone,
    /// The cumulative stall budget for full-ring waits is exhausted.
    StallBudgetExhausted,
    /// The record is larger than the whole ring and can never fit.
    RecordTooLarge,
}

struct RingShared {
    buf: Box<[AtomicU8]>,
    mask: usize,
    /// Consumer read position (free-running).
    head: AtomicUsize,
    /// Producer write position (free-running).
    tail: AtomicUsize,
    producer_closed: AtomicBool,
    consumer_closed: AtomicBool,
    lock: Mutex<()>,
    cond: Condvar,
}

impl RingShared {
    fn notify(&self) {
        // Take the lock so a waiter between its condition re-check and its
        // `wait_timeout` cannot miss the wakeup.
        let _guard = self.lock.lock().unwrap_or_else(|e| e.into_inner());
        self.cond.notify_all();
    }
}

/// Creates a connected producer/consumer pair over a fresh ring.
///
/// `capacity` is rounded up to a power of two (minimum 64 bytes).
pub(crate) fn ring(capacity: usize) -> (RingProducer, RingConsumer) {
    let capacity = capacity.max(64).next_power_of_two();
    let mut buf = Vec::with_capacity(capacity);
    buf.resize_with(capacity, || AtomicU8::new(0));
    let shared = Arc::new(RingShared {
        buf: buf.into_boxed_slice(),
        mask: capacity - 1,
        head: AtomicUsize::new(0),
        tail: AtomicUsize::new(0),
        producer_closed: AtomicBool::new(false),
        consumer_closed: AtomicBool::new(false),
        lock: Mutex::new(()),
        cond: Condvar::new(),
    });
    (
        RingProducer {
            shared: Arc::clone(&shared),
            stall_used: Duration::ZERO,
            stall_budget: Duration::from_secs(10),
            len_scratch: Vec::with_capacity(8),
        },
        RingConsumer { shared, head: 0 },
    )
}

/// Producer handle (solver thread). Closes the ring on drop.
pub(crate) struct RingProducer {
    shared: Arc<RingShared>,
    stall_used: Duration,
    stall_budget: Duration,
    len_scratch: Vec<u8>,
}

impl RingProducer {
    /// Overrides the cumulative full-ring stall budget (default 10 s).
    #[cfg(test)]
    pub(crate) fn set_stall_budget(&mut self, budget: Duration) {
        self.stall_budget = budget;
    }

    /// Pushes one whole record (length prefix added here), blocking in
    /// bounded waits while the ring is full. On error the ring is unchanged.
    pub(crate) fn push(&mut self, record_bytes: &[u8]) -> Result<(), RingPushError> {
        let shared = &self.shared;
        self.len_scratch.clear();
        encode_u64(&mut self.len_scratch, record_bytes.len() as u64);
        let total = self.len_scratch.len() + record_bytes.len();
        let capacity = shared.mask + 1;
        if total > capacity {
            return Err(RingPushError::RecordTooLarge);
        }

        loop {
            if shared.consumer_closed.load(Ordering::Acquire) {
                return Err(RingPushError::ConsumerGone);
            }
            let head = shared.head.load(Ordering::Acquire);
            let tail = shared.tail.load(Ordering::Relaxed);
            let used = tail.wrapping_sub(head);
            if capacity - used >= total {
                // Write the length prefix and payload, then publish once.
                let mut at = tail;
                for &byte in self.len_scratch.iter().chain(record_bytes) {
                    shared.buf[at & shared.mask].store(byte, Ordering::Relaxed);
                    at = at.wrapping_add(1);
                }
                shared.tail.store(at, Ordering::Release);
                shared.notify();
                return Ok(());
            }

            // Ring full: bounded park, charged against the stall budget.
            if self.stall_used >= self.stall_budget {
                return Err(RingPushError::StallBudgetExhausted);
            }
            let quantum =
                FULL_WAIT_QUANTUM.min(self.stall_budget.checked_sub(self.stall_used).unwrap());
            let start = std::time::Instant::now();
            {
                let guard = shared.lock.lock().unwrap_or_else(|e| e.into_inner());
                // Re-check under the lock so a concurrent pop cannot slip
                // between the check above and the wait below.
                let head_now = shared.head.load(Ordering::Acquire);
                let used_now = tail.wrapping_sub(head_now);
                if capacity - used_now >= total || shared.consumer_closed.load(Ordering::Acquire) {
                    continue;
                }
                let _ = shared
                    .cond
                    .wait_timeout(guard, quantum)
                    .unwrap_or_else(|e| e.into_inner());
            }
            self.stall_used += start.elapsed();
        }
    }
}

impl Drop for RingProducer {
    fn drop(&mut self) {
        self.shared.producer_closed.store(true, Ordering::Release);
        self.shared.notify();
    }
}

/// Consumer handle (serializer thread). Marks the consumer gone on drop.
pub(crate) struct RingConsumer {
    shared: Arc<RingShared>,
    head: usize,
}

impl RingConsumer {
    /// Pops the next whole record's payload into `out` (cleared first).
    ///
    /// Blocks until a record is available. Returns `false` when the producer
    /// has closed the ring and every buffered record has been drained.
    pub(crate) fn pop(&mut self, out: &mut Vec<u8>) -> bool {
        let shared = Arc::clone(&self.shared);
        loop {
            let closed = shared.producer_closed.load(Ordering::Acquire);
            let tail = shared.tail.load(Ordering::Acquire);
            let avail = tail.wrapping_sub(self.head);
            if avail > 0 {
                // The producer publishes whole records, so at least one full
                // record (length prefix + payload) is readable.
                let mut prefix = [0u8; 10];
                let prefix_len = avail.min(prefix.len());
                for (i, slot) in prefix.iter_mut().enumerate().take(prefix_len) {
                    *slot =
                        shared.buf[self.head.wrapping_add(i) & shared.mask].load(Ordering::Relaxed);
                }
                let mut pos = 0usize;
                let len = decode_u64(&prefix[..prefix_len], &mut pos)
                    .expect("SPSC ring length prefix is always whole and valid")
                    as usize;
                debug_assert!(avail >= pos + len, "ring published a partial record");

                out.clear();
                out.reserve(len);
                let payload_start = self.head.wrapping_add(pos);
                for i in 0..len {
                    out.push(
                        shared.buf[payload_start.wrapping_add(i) & shared.mask]
                            .load(Ordering::Relaxed),
                    );
                }
                self.head = self.head.wrapping_add(pos + len);
                shared.head.store(self.head, Ordering::Release);
                shared.notify();
                return true;
            }
            if closed {
                return false;
            }
            let guard = shared.lock.lock().unwrap_or_else(|e| e.into_inner());
            // Re-check under the lock (a push may have landed since).
            let tail_now = shared.tail.load(Ordering::Acquire);
            if tail_now.wrapping_sub(self.head) > 0
                || shared.producer_closed.load(Ordering::Acquire)
            {
                continue;
            }
            let _ = shared
                .cond
                .wait_timeout(guard, EMPTY_WAIT_QUANTUM)
                .unwrap_or_else(|e| e.into_inner());
        }
    }
}

impl Drop for RingConsumer {
    fn drop(&mut self) {
        self.shared.consumer_closed.store(true, Ordering::Release);
        self.shared.notify();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_thread_round_trip_with_wraparound() {
        let (mut producer, mut consumer) = ring(64);
        let mut out = Vec::new();
        // Push/pop enough records to wrap the 64-byte ring several times.
        for round in 0u32..64 {
            let payload: Vec<u8> = (0..(round % 40) as u8).map(|b| b ^ round as u8).collect();
            producer.push(&payload).expect("fits");
            assert!(consumer.pop(&mut out));
            assert_eq!(out, payload, "round {round}");
        }
    }

    #[test]
    fn producer_close_drains_then_ends() {
        let (mut producer, mut consumer) = ring(256);
        producer.push(&[1, 2, 3]).unwrap();
        producer.push(&[4]).unwrap();
        drop(producer);
        let mut out = Vec::new();
        assert!(consumer.pop(&mut out));
        assert_eq!(out, [1, 2, 3]);
        assert!(consumer.pop(&mut out));
        assert_eq!(out, [4]);
        assert!(!consumer.pop(&mut out));
        assert!(!consumer.pop(&mut out), "stays closed");
    }

    #[test]
    fn oversized_record_fails_closed() {
        let (mut producer, _consumer) = ring(64);
        let big = vec![0u8; 65];
        assert_eq!(producer.push(&big), Err(RingPushError::RecordTooLarge));
    }

    #[test]
    fn full_ring_with_dead_consumer_fails_closed() {
        let (mut producer, consumer) = ring(64);
        drop(consumer);
        assert_eq!(producer.push(&[0u8; 16]), Err(RingPushError::ConsumerGone));
    }

    #[test]
    fn full_ring_exhausts_stall_budget() {
        let (mut producer, _consumer) = ring(64);
        producer.set_stall_budget(Duration::from_millis(50));
        // Fill the ring (leave the consumer idle).
        while producer.push(&[7u8; 20]).is_ok() {}
        assert_eq!(
            producer.push(&[7u8; 20]),
            Err(RingPushError::StallBudgetExhausted)
        );
    }

    #[test]
    fn cross_thread_stream_preserves_order_and_bytes() {
        let (mut producer, mut consumer) = ring(1 << 10);
        let records: Vec<Vec<u8>> = (0u32..5000)
            .map(|i| {
                let len = (i % 96) as usize;
                (0..len).map(|j| (i as u8).wrapping_add(j as u8)).collect()
            })
            .collect();
        let expected = records.clone();
        let handle = std::thread::spawn(move || {
            let mut out = Vec::new();
            let mut seen = Vec::new();
            while consumer.pop(&mut out) {
                seen.push(out.clone());
            }
            seen
        });
        for record in &records {
            producer.push(record).expect("consumer is draining");
        }
        drop(producer);
        let seen = handle.join().expect("consumer thread");
        assert_eq!(seen, expected);
    }
}
