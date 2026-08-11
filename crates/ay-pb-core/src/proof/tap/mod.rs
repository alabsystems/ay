// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof tap: asynchronous micro-op proof capture for the dense conflict path
//! (the development design notes).
//!
//! The solver thread captures each dense conflict analysis as a FRAME of
//! LEB128 micro-op records pushed through a bounded SPSC byte ring; a
//! dedicated serializer thread replays each frame into ONE VeriPB pol line
//! via the existing [`VeriPbWriter`]. Proof ids are allocated SOLVER-SIDE
//! (this handle owns the id counter); the serializer re-derives and ASSERTS
//! the same sequence, so any reorder or desync is an immediate, attributable
//! hard error rather than an eventual checker rejection.
//!
//! FAIL-CLOSED CONTRACT: every failure (ring backpressure budget, dead or
//! panicked serializer, encode/IO error, id desync) surfaces as a
//! [`ProofError`] that the solver stores via its usual first-error-wins path,
//! after which the tap is dropped and the solve continues UNLOGGED on the
//! plain dense path. A conclusion only commits after the serializer has
//! drained the ring, emitted the conclusion block, and flushed — the
//! conclusion handshake blocks (with a generous timeout) at claim-commit
//! time, never on the hot path. The failure mode is "no certificate", never
//! "wrong certificate".

pub(crate) mod record;
pub(crate) mod ring;
pub(crate) mod serializer;
pub(crate) mod varint;

use std::io::Write;
use std::panic::AssertUnwindSafe;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::Duration;

use crate::types::PbLit;

use super::steps::ConstraintId;
use super::veripb::{ProofError, VeriPbWriter};
use record::TapRecord;
use ring::{RingConsumer, RingProducer, RingPushError};
use serializer::{SerializerFlow, TapSerializer};

/// Generous conclusion-handshake timeout: the serializer only has the ring
/// backlog plus one flush left when the solver blocks here.
const CONCLUSION_TIMEOUT: Duration = Duration::from_mins(10);

/// CHECKPOINT thresholds (spec record kind 9): split the frame's pol line
/// every K captured ops or 64 KiB of frame record bytes.
const CHECKPOINT_OPS_DEFAULT: u32 = 256;
const CHECKPOINT_BYTES_DEFAULT: usize = 64 << 10;

/// 64 KiB record chunking: a `ProvenResolve` weaken list longer than this is
/// split into `WeakenCont` chunks. Each encoded pair is at most 29 bytes
/// (10-byte lit varint + 19-byte i128 varint), so a chunk stays under 64 KiB.
const MAX_WEAKEN_PAIRS_PER_RECORD: usize = 2048;

/// Running serializer/tap counters (shared atomics; written by both the
/// solver side — checkpoints — and the serializer sink — bytes/lines).
#[derive(Debug, Default)]
pub(crate) struct TapStats {
    pub(crate) checkpoints: AtomicU64,
    pub(crate) bytes_written: AtomicU64,
    pub(crate) lines_emitted: AtomicU64,
}

/// Point-in-time snapshot of the tap's running counters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ProofTapStats {
    /// CHECKPOINT line splits emitted (deep frames continued via an
    /// intermediate id that the serializer auto-deletes).
    pub checkpoints: u64,
    /// Proof bytes handed to the underlying sink so far.
    pub bytes_written: u64,
    /// Proof lines (newlines) handed to the underlying sink so far.
    pub lines_emitted: u64,
}

impl TapStats {
    pub(crate) fn snapshot(&self) -> ProofTapStats {
        ProofTapStats {
            checkpoints: self.checkpoints.load(Ordering::Relaxed),
            bytes_written: self.bytes_written.load(Ordering::Relaxed),
            lines_emitted: self.lines_emitted.load(Ordering::Relaxed),
        }
    }
}

/// Byte/line-counting sink wrapper for the serializer's writer (running
/// stats for the deletion-discipline soft cap and diagnostics).
pub(crate) struct CountingWriter<W> {
    inner: W,
    stats: Arc<TapStats>,
}

impl<W: Write> Write for CountingWriter<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let written = self.inner.write(buf)?;
        self.stats
            .bytes_written
            .fetch_add(written as u64, Ordering::Relaxed);
        // Simple per-write scan; the serializer batches writes, so this is
        // negligible against the I/O and not worth a bytecount dependency.
        #[allow(clippy::naive_bytecount)]
        let newlines = buf[..written].iter().filter(|&&b| b == b'\n').count();
        self.stats
            .lines_emitted
            .fetch_add(newlines as u64, Ordering::Relaxed);
        Ok(written)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

/// Shared solver/serializer state: poison flag + first error.
struct TapShared {
    poisoned: AtomicBool,
    error: Mutex<Option<ProofError>>,
}

impl TapShared {
    fn poison(&self, error: ProofError) {
        {
            let mut slot = self.error.lock().unwrap_or_else(|e| e.into_inner());
            if slot.is_none() {
                *slot = Some(error);
            }
        }
        self.poisoned.store(true, Ordering::Release);
    }

    fn take_error(&self) -> ProofError {
        self.error
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .take()
            .unwrap_or_else(|| ProofError::TapSerializer(String::from("tap poisoned")))
    }
}

/// Solver-side proof-tap handle. Owns the id allocator, the ring producer,
/// and the serializer thread join handle.
pub(crate) struct ProofTap {
    producer: Option<RingProducer>,
    shared: Arc<TapShared>,
    stats: Arc<TapStats>,
    /// Next proof id to allocate (source of truth; the writer's own counter
    /// is only the reconciliation check).
    next_id: u64,
    /// Whether a conflict frame is currently open (solver-side mirror).
    frame_open: bool,
    /// Captured ops since the frame opened / the last checkpoint.
    frame_ops: u32,
    /// Frame record bytes since the frame opened / the last checkpoint.
    frame_bytes: usize,
    checkpoint_ops_limit: u32,
    checkpoint_bytes_limit: usize,
    done_rx: Receiver<Result<(), ()>>,
    join: Option<JoinHandle<()>>,
    encode_buf: Vec<u8>,
}

impl ProofTap {
    /// Spawns the serializer thread over `writer` (which has already emitted
    /// the proof header). `first_free_id` seeds the solver-side allocator and
    /// must equal the writer's next id (`num_input_constraints + 1` with the
    /// Eq-counted-twice rule).
    pub(crate) fn spawn<W: Write + Send + 'static>(
        writer: VeriPbWriter<W>,
        first_free_id: u64,
        ring_capacity: usize,
    ) -> Self {
        Self::spawn_with_stats(
            writer,
            first_free_id,
            ring_capacity,
            Arc::new(TapStats::default()),
            None,
        )
    }

    /// Spawns the serializer thread over a raw sink: wraps it in the
    /// byte/line-counting writer BEFORE the VeriPB header is emitted, so the
    /// running stats cover the whole proof stream.
    pub(crate) fn spawn_counting<W: Write + Send + 'static>(
        sink: W,
        num_input_constraints: u64,
        ring_capacity: usize,
    ) -> Result<Self, ProofError> {
        let stats = Arc::new(TapStats::default());
        let writer = VeriPbWriter::new(
            CountingWriter {
                inner: sink,
                stats: Arc::clone(&stats),
            },
            num_input_constraints,
        )?;
        let first_free_id = num_input_constraints
            .checked_add(1)
            .ok_or(ProofError::ConstraintIdOverflow)?;
        Ok(Self::spawn_with_stats(
            writer,
            first_free_id,
            ring_capacity,
            stats,
            Self::default_soft_cap(),
        ))
    }

    /// Test-only constructor injecting a soft cap without touching the env.
    /// (No test uses it yet — kept for owner review.)
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn spawn_with_soft_cap<W: Write + Send + 'static>(
        writer: VeriPbWriter<W>,
        first_free_id: u64,
        ring_capacity: usize,
        soft_cap: Option<u64>,
    ) -> Self {
        Self::spawn_with_stats(
            writer,
            first_free_id,
            ring_capacity,
            Arc::new(TapStats::default()),
            soft_cap,
        )
    }

    fn spawn_with_stats<W: Write + Send + 'static>(
        writer: VeriPbWriter<W>,
        first_free_id: u64,
        ring_capacity: usize,
        stats: Arc<TapStats>,
        soft_cap: Option<u64>,
    ) -> Self {
        let (producer, consumer) = ring::ring(ring_capacity);
        let shared = Arc::new(TapShared {
            poisoned: AtomicBool::new(false),
            error: Mutex::new(None),
        });
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let thread_shared = Arc::clone(&shared);
        let thread_stats = Arc::clone(&stats);
        let join = std::thread::Builder::new()
            .name(String::from("ay-pb-proof-tap"))
            .spawn(move || {
                serializer_thread(
                    consumer,
                    writer,
                    thread_shared,
                    done_tx,
                    thread_stats,
                    soft_cap,
                )
            })
            .expect("spawning the proof-tap serializer thread");
        Self {
            producer: Some(producer),
            shared,
            stats,
            next_id: first_free_id,
            frame_open: false,
            frame_ops: 0,
            frame_bytes: 0,
            checkpoint_ops_limit: CHECKPOINT_OPS_DEFAULT,
            checkpoint_bytes_limit: CHECKPOINT_BYTES_DEFAULT,
            done_rx,
            join: Some(join),
            encode_buf: Vec::with_capacity(512),
        }
    }

    /// Shared handle to the running counters (kept by the solver so stats
    /// survive a tap drop/void).
    pub(crate) fn stats_arc(&self) -> Arc<TapStats> {
        Arc::clone(&self.stats)
    }

    /// Overrides the CHECKPOINT split thresholds. Test/diagnostic hook: lower
    /// limits force multi-segment pol derivations on small instances.
    pub(crate) fn set_checkpoint_limits(&mut self, ops: u32, bytes: usize) {
        self.checkpoint_ops_limit = ops.max(1);
        self.checkpoint_bytes_limit = bytes.max(1);
    }

    /// Test-only: shrinks the producer's cumulative stall budget so the
    /// void-on-stall / backpressure path fires sub-second and deterministically
    /// instead of after the ~10s production default. No-op after shutdown.
    #[cfg(test)]
    pub(crate) fn set_stall_budget(&mut self, budget: Duration) {
        if let Some(producer) = self.producer.as_mut() {
            producer.set_stall_budget(budget);
        }
    }

    /// Default ring capacity (env `AY_PB_PROOF_TAP_RING_MIB` override).
    pub(crate) fn default_ring_capacity() -> usize {
        std::env::var("AY_PB_PROOF_TAP_RING_MIB")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .filter(|&mib| (1..=1024).contains(&mib))
            .map_or(ring::DEFAULT_RING_CAPACITY, |mib| mib << 20)
    }

    /// Optional serializer soft byte cap (env `AY_PB_PROOF_TAP_SOFT_CAP_MIB`;
    /// unset or 0 = uncapped). Breaching it VOIDS the proof (no certificate),
    /// it never truncates.
    pub(crate) fn default_soft_cap() -> Option<u64> {
        std::env::var("AY_PB_PROOF_TAP_SOFT_CAP_MIB")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .filter(|&mib| mib > 0)
            .map(|mib| mib << 20)
    }

    /// One relaxed poison check (the per-conflict BEGIN-site check).
    pub(crate) fn is_poisoned(&self) -> bool {
        self.shared.poisoned.load(Ordering::Relaxed)
    }

    /// Takes the stored serializer error (or a generic one).
    pub(crate) fn take_error(&self) -> ProofError {
        self.shared.take_error()
    }

    fn alloc_id(&mut self) -> Result<ConstraintId, ProofError> {
        let id = ConstraintId::new(self.next_id).ok_or(ProofError::ConstraintIdOverflow)?;
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or(ProofError::ConstraintIdOverflow)?;
        Ok(id)
    }

    /// Pushes one record, returning its encoded byte size (feeds the
    /// CHECKPOINT frame-bytes threshold).
    fn push(&mut self, record: &TapRecord) -> Result<usize, ProofError> {
        let Some(producer) = self.producer.as_mut() else {
            return Err(ProofError::TapTransport("tap already shut down"));
        };
        self.encode_buf.clear();
        record.encode(&mut self.encode_buf);
        let encoded_len = self.encode_buf.len();
        let result = producer.push(&self.encode_buf).map_err(|e| match e {
            RingPushError::ConsumerGone => {
                // The serializer stored its own (more specific) error first.
                if self.shared.poisoned.load(Ordering::Acquire) {
                    self.shared.take_error()
                } else {
                    ProofError::TapTransport("proof-tap serializer terminated")
                }
            }
            RingPushError::StallBudgetExhausted => {
                ProofError::TapTransport("ring backpressure stall budget exhausted")
            }
            RingPushError::RecordTooLarge => {
                ProofError::TapTransport("record larger than the ring")
            }
        });
        result.map(|()| encoded_len)
    }

    /// Opens a conflict frame. Checks the poison flag first (the mandatory
    /// per-conflict check) and self-heals a dangling open frame.
    pub(crate) fn begin_frame(&mut self, conflict_pid: ConstraintId) -> Result<(), ProofError> {
        if self.is_poisoned() {
            return Err(self.take_error());
        }
        self.abort_frame_if_open()?;
        self.push(&TapRecord::BeginFrame {
            conflict_pid: conflict_pid.get(),
        })?;
        self.frame_open = true;
        self.frame_ops = 0;
        self.frame_bytes = 0;
        Ok(())
    }

    /// CHECKPOINT (spec record kind 9): when the frame has accumulated K ops
    /// or 64 KiB of record bytes, allocate an intermediate id, split the pol
    /// line there, and reset the counters. Fires only at op boundaries.
    fn maybe_checkpoint(&mut self) -> Result<(), ProofError> {
        if !self.frame_open
            || (self.frame_ops < self.checkpoint_ops_limit
                && self.frame_bytes < self.checkpoint_bytes_limit)
        {
            return Ok(());
        }
        let intermediate = self.alloc_id()?;
        self.push(&TapRecord::Checkpoint {
            intermediate_pid: intermediate.get(),
        })?;
        self.frame_ops = 0;
        self.frame_bytes = 0;
        self.stats.checkpoints.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }

    /// Captures one accepted PROVEN round-to-one resolution step. Oversized
    /// weaken lists are chunked into `WeakenCont` records (64 KiB record cap)
    /// so no single record can exceed ring capacity.
    pub(crate) fn proven_resolve(
        &mut self,
        reason_pid: ConstraintId,
        c: i128,
        w: i128,
        weakened: Vec<(PbLit, i128)>,
    ) -> Result<(), ProofError> {
        debug_assert!(self.frame_open, "proven_resolve outside a frame");
        let mut op_bytes = 0usize;
        let mut rest = weakened;
        while rest.len() > MAX_WEAKEN_PAIRS_PER_RECORD {
            let tail = rest.split_off(MAX_WEAKEN_PAIRS_PER_RECORD);
            op_bytes += self.push(&TapRecord::WeakenCont { pairs: rest })?;
            rest = tail;
        }
        op_bytes += self.push(&TapRecord::ProvenResolve {
            reason_pid: reason_pid.get(),
            c,
            w,
            weakened: rest,
        })?;
        self.frame_ops += 1;
        self.frame_bytes += op_bytes;
        self.maybe_checkpoint()
    }

    /// Captures one accepted heuristic resolution step.
    pub(crate) fn heuristic_resolve(
        &mut self,
        reason_pid: ConstraintId,
        conflict_factor: i128,
        reason_factor: i128,
        div: Option<i128>,
    ) -> Result<(), ProofError> {
        debug_assert!(self.frame_open, "heuristic_resolve outside a frame");
        let op_bytes = self.push(&TapRecord::HeuristicResolve {
            reason_pid: reason_pid.get(),
            conflict_factor,
            reason_factor,
            div,
        })?;
        self.frame_ops += 1;
        self.frame_bytes += op_bytes;
        self.maybe_checkpoint()
    }

    /// Closes the frame with the strengthening ops, allocating and returning
    /// the lemma's proof id.
    pub(crate) fn final_frame(
        &mut self,
        gcd1: i128,
        weaken_ran: bool,
        weakened: Vec<PbLit>,
        gcd2: i128,
    ) -> Result<ConstraintId, ProofError> {
        debug_assert!(self.frame_open, "final_frame outside a frame");
        let lemma_pid = self.alloc_id()?;
        self.frame_open = false;
        self.push(&TapRecord::FinalFrame {
            gcd1,
            weaken_ran,
            weakened,
            gcd2,
            lemma_pid: lemma_pid.get(),
        })?;
        Ok(lemma_pid)
    }

    /// Aborts the open frame, if any (safe to call unconditionally; covers
    /// every early return out of conflict analysis).
    pub(crate) fn abort_frame_if_open(&mut self) -> Result<(), ProofError> {
        if self.frame_open {
            self.frame_open = false;
            self.push(&TapRecord::AbortFrame)?;
        }
        Ok(())
    }

    /// Logs a structured RUP row; formatting happens on the serializer.
    pub(crate) fn log_rup(
        &mut self,
        terms: Vec<(PbLit, i128)>,
        degree: i128,
    ) -> Result<ConstraintId, ProofError> {
        let pid = self.alloc_id()?;
        self.push(&TapRecord::Rup {
            pid: pid.get(),
            terms,
            degree,
        })?;
        Ok(pid)
    }

    /// Logs a pre-formatted RUP row (legacy `ProofStep::Rup` payloads).
    pub(crate) fn log_rup_text(&mut self, text: String) -> Result<ConstraintId, ProofError> {
        let pid = self.alloc_id()?;
        self.push(&TapRecord::RupText {
            pid: pid.get(),
            text,
        })?;
        Ok(pid)
    }

    /// Logs a checked deletion (allocates no id).
    pub(crate) fn log_delete(&mut self, pid: ConstraintId) -> Result<(), ProofError> {
        self.push(&TapRecord::Delete { pid: pid.get() }).map(|_| ())
    }

    /// Emits the UNSAT conclusion and BLOCKS until the serializer has drained
    /// the ring, written the conclusion block, and flushed (claim-commit
    /// handshake). Any buffered failure surfaces here, before the claim.
    pub(crate) fn conclude_unsat(
        &mut self,
        contradiction_pid: ConstraintId,
    ) -> Result<(), ProofError> {
        self.push(&TapRecord::ConcludeUnsat {
            contradiction_pid: contradiction_pid.get(),
        })?;
        self.await_conclusion()
    }

    /// Emits the SAT conclusion (same handshake as UNSAT).
    pub(crate) fn conclude_sat(&mut self, assignment: &[bool]) -> Result<(), ProofError> {
        self.push(&TapRecord::ConcludeSat {
            assignment: assignment.to_vec(),
        })?;
        self.await_conclusion()
    }

    fn await_conclusion(&mut self) -> Result<(), ProofError> {
        match self.done_rx.recv_timeout(CONCLUSION_TIMEOUT) {
            Ok(Ok(())) => Ok(()),
            Ok(Err(())) => Err(self.take_error()),
            Err(RecvTimeoutError::Timeout) => Err(ProofError::TapSerializer(String::from(
                "conclusion handshake timed out",
            ))),
            Err(RecvTimeoutError::Disconnected) => {
                if self.is_poisoned() {
                    Err(self.take_error())
                } else {
                    Err(ProofError::TapSerializer(String::from(
                        "serializer exited before the conclusion",
                    )))
                }
            }
        }
    }

    /// Shuts the tap down and surfaces any serializer error. Called from
    /// `conclude_proof` after the (optional) conclusion handshake.
    pub(crate) fn finish(&mut self) -> Result<(), ProofError> {
        if let Some(producer) = self.producer.as_mut() {
            // Best-effort; producer drop below closes the ring regardless.
            let mut buf = Vec::with_capacity(4);
            TapRecord::Shutdown.encode(&mut buf);
            let _ = producer.push(&buf);
        }
        self.producer = None;
        if let Some(join) = self.join.take() {
            let _ = join.join();
        }
        if self.shared.poisoned.load(Ordering::Acquire) {
            return Err(self.take_error());
        }
        Ok(())
    }
}

impl Drop for ProofTap {
    fn drop(&mut self) {
        // Close the ring so the serializer drains and exits, then join. The
        // temp proof is deleted by the caller's commit-or-remove logic when no
        // conclusion committed, so a discarded result here is safe.
        self.producer = None;
        if let Some(join) = self.join.take() {
            let _ = join.join();
        }
    }
}

/// Serializer thread body: pop records, drive the state machine, complete
/// conclusion handshakes, poison on any error (first error wins).
fn serializer_thread<W: Write>(
    mut consumer: RingConsumer,
    writer: VeriPbWriter<W>,
    shared: Arc<TapShared>,
    done_tx: Sender<Result<(), ()>>,
    stats: Arc<TapStats>,
    soft_cap: Option<u64>,
) {
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let mut serializer = TapSerializer::new(writer);
        let mut buf = Vec::with_capacity(512);
        while consumer.pop(&mut buf) {
            let record = match TapRecord::decode(&buf) {
                Ok(record) => record,
                Err(_) => {
                    return Err(ProofError::TapProtocol("undecodable record in the ring"));
                }
            };
            match serializer.process(record) {
                Ok(SerializerFlow::Continue) => {
                    // Soft-cap check ONLY here: derivation/RUP records are
                    // processed strictly before the single trailing conclusion
                    // record, so a breach voids the proof (no certificate)
                    // before any conclusion can commit — fail-closed, never a
                    // truncated-yet-concluded proof.
                    if let Some(cap) = soft_cap {
                        let bytes = stats.bytes_written.load(Ordering::Relaxed);
                        if bytes > cap {
                            eprintln!(
                                "warning: proof-tap soft cap exceeded \
                                 ({bytes} > {cap} bytes); voiding certificate"
                            );
                            return Err(ProofError::TapSoftCapExceeded { bytes, cap });
                        }
                    }
                }
                Ok(SerializerFlow::Concluded) => {
                    // The conclusion block is written and flushed: complete
                    // the claim-commit handshake.
                    let _ = done_tx.send(Ok(()));
                }
                Ok(SerializerFlow::Shutdown) => return Ok(()),
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }));

    match result {
        Ok(Ok(())) => {}
        Ok(Err(error)) => {
            shared.poison(error);
            let _ = done_tx.send(Err(()));
        }
        Err(_panic) => {
            shared.poison(ProofError::TapSerializer(String::from(
                "serializer thread panicked",
            )));
            let _ = done_tx.send(Err(()));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn writer_to_shared_vec() -> (VeriPbWriter<SharedVec>, Arc<Mutex<Vec<u8>>>) {
        let sink = Arc::new(Mutex::new(Vec::new()));
        let writer = VeriPbWriter::new(
            SharedVec {
                inner: Arc::clone(&sink),
            },
            2,
        )
        .expect("in-memory header");
        (writer, sink)
    }

    /// A `Write` sink the test can read back after the thread finishes.
    struct SharedVec {
        inner: Arc<Mutex<Vec<u8>>>,
    }

    impl Write for SharedVec {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.inner.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    fn cid(raw: u64) -> ConstraintId {
        ConstraintId::new(raw).expect("nonzero")
    }

    #[test]
    fn end_to_end_frame_and_unsat_conclusion_through_the_ring() {
        let (writer, sink) = writer_to_shared_vec();
        let mut tap = ProofTap::spawn(writer, 3, 1 << 16);

        tap.begin_frame(cid(1)).unwrap();
        tap.proven_resolve(cid(2), 2, 3, vec![]).unwrap();
        let lemma = tap
            .final_frame(1, false, Vec::new(), 0)
            .expect("frame closes");
        assert_eq!(lemma.get(), 3);

        let contradiction = tap.log_rup_text(String::from(">= 1 ;")).unwrap();
        assert_eq!(contradiction.get(), 4);
        tap.conclude_unsat(contradiction).expect("handshake");
        tap.finish().expect("clean shutdown");

        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        assert_eq!(
            text,
            "pseudo-Boolean proof version 3.0\nf 2 ;\n\
             pol 1 s 2 2 d 3 * + s s ;\n\
             rup >= 1 ;\n\
             output NONE;\nconclusion UNSAT : 4;\nend pseudo-Boolean proof;\n"
        );
    }

    #[test]
    fn solver_side_desync_surfaces_before_conclusion_commits() {
        let (writer, _sink) = writer_to_shared_vec();
        // Wrong first free id (writer expects 3): the very first allocating
        // record must hard-fail the tap.
        let mut tap = ProofTap::spawn(writer, 10, 1 << 16);
        let pid = tap.log_rup_text(String::from(">= 1 ;")).unwrap();
        assert_eq!(pid.get(), 10);
        let err = tap.conclude_unsat(pid).expect_err("desync must void");
        assert!(
            matches!(
                err,
                ProofError::TapIdDesync {
                    expected: 10,
                    actual: 3
                }
            ),
            "unexpected error: {err:?}"
        );
    }

    #[test]
    fn aborted_frames_allocate_nothing() {
        let (writer, sink) = writer_to_shared_vec();
        let mut tap = ProofTap::spawn(writer, 3, 1 << 16);
        tap.begin_frame(cid(1)).unwrap();
        tap.heuristic_resolve(cid(2), 2, 3, Some(4)).unwrap();
        tap.abort_frame_if_open().unwrap();
        // Self-healing: begin while another begin never closed.
        tap.begin_frame(cid(2)).unwrap();
        tap.begin_frame(cid(1)).unwrap();
        let lemma = tap.final_frame(0, false, Vec::new(), 0).unwrap();
        assert_eq!(lemma.get(), 3, "aborted frames must not consume ids");
        tap.finish().expect("clean shutdown");
        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        assert!(text.ends_with("pol 1 s s ;\n"), "{text}");
    }

    #[test]
    fn ops_threshold_checkpoints_split_frames_and_auto_delete_intermediates() {
        let (writer, sink) = writer_to_shared_vec();
        let mut tap = ProofTap::spawn(writer, 3, 1 << 16);
        tap.set_checkpoint_limits(2, usize::MAX);

        tap.begin_frame(cid(1)).unwrap();
        for _ in 0..5 {
            tap.heuristic_resolve(cid(2), 1, 1, None).unwrap();
        }
        // 5 ops with K=2: checkpoints after ops 2 and 4 consume ids 3 and 4,
        // so the lemma id is 5.
        let lemma = tap.final_frame(1, false, Vec::new(), 0).unwrap();
        assert_eq!(lemma.get(), 5);
        assert_eq!(tap.stats_arc().snapshot().checkpoints, 2);

        let contradiction = tap.log_rup_text(String::from(">= 1 ;")).unwrap();
        assert_eq!(contradiction.get(), 6);
        tap.conclude_unsat(contradiction).expect("handshake");
        tap.finish().expect("clean shutdown");

        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        assert_eq!(
            text,
            "pseudo-Boolean proof version 3.0\nf 2 ;\n\
             pol 1 s 2 + s 2 + s ;\n\
             pol 3 2 + s 2 + s ;\n\
             pol 4 2 + s s ;\n\
             del id 3 ;\ndel id 4 ;\n\
             rup >= 1 ;\n\
             output NONE;\nconclusion UNSAT : 6;\nend pseudo-Boolean proof;\n"
        );
    }

    #[test]
    fn byte_threshold_checkpoints_fire_on_frame_record_bytes() {
        let (writer, sink) = writer_to_shared_vec();
        let mut tap = ProofTap::spawn(writer, 3, 1 << 16);
        // Tiny byte budget: every op crosses it, so each op is followed by a
        // checkpoint.
        tap.set_checkpoint_limits(u32::MAX, 1);
        tap.begin_frame(cid(1)).unwrap();
        tap.heuristic_resolve(cid(2), 1, 1, None).unwrap();
        tap.heuristic_resolve(cid(2), 1, 1, None).unwrap();
        let lemma = tap.final_frame(0, false, Vec::new(), 0).unwrap();
        assert_eq!(lemma.get(), 5, "two checkpoints consumed ids 3 and 4");
        tap.finish().expect("clean shutdown");
        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        assert!(
            text.contains("del id 3 ;\ndel id 4 ;"),
            "intermediates must be auto-deleted:\n{text}"
        );
    }

    #[test]
    fn oversized_weaken_lists_are_chunked_and_replay_identically() {
        let (writer, sink) = writer_to_shared_vec();
        let mut tap = ProofTap::spawn(writer, 3, 1 << 20);
        // 2*MAX + 3 pairs: two full WeakenCont chunks + a 3-pair tail in the
        // ProvenResolve record itself.
        let n = 2 * MAX_WEAKEN_PAIRS_PER_RECORD + 3;
        let weakened: Vec<(PbLit, i128)> = (1..=n)
            .map(|i| {
                (
                    PbLit {
                        var: i as u32,
                        negated: false,
                    },
                    1i128,
                )
            })
            .collect();
        tap.begin_frame(cid(1)).unwrap();
        tap.proven_resolve(cid(1), 1, 1, weakened).unwrap();
        let lemma = tap.final_frame(0, false, Vec::new(), 0).unwrap();
        assert_eq!(lemma.get(), 3, "chunking must not consume ids");
        tap.finish().expect("clean shutdown");
        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        // Every weakened literal appears exactly once, in order.
        let pol_line = text
            .lines()
            .find(|l| l.starts_with("pol "))
            .expect("one pol line");
        assert_eq!(pol_line.matches(" * + ").count(), n, "{n} weaken axioms");
        let first = pol_line.find("~x1 1 * +").expect("first pair present");
        let last = pol_line
            .find(&format!("~x{n} 1 * +"))
            .expect("last pair present");
        assert!(first < last, "order preserved across chunks");
    }

    #[test]
    fn soft_cap_breach_voids_the_proof_instead_of_truncating() {
        // A CountingWriter over the shared sink, sharing the tap's stats so
        // bytes_written reflects real emitted bytes (as spawn_counting does in
        // production).
        let stats = Arc::new(TapStats::default());
        let sink = Arc::new(Mutex::new(Vec::new()));
        let writer = VeriPbWriter::new(
            CountingWriter {
                inner: SharedVec {
                    inner: Arc::clone(&sink),
                },
                stats: Arc::clone(&stats),
            },
            2,
        )
        .expect("in-memory header");
        // MB-scale cap: 1 MiB. One frame whose weaken list makes a single pol
        // line exceed the cap, so the breach is a real derivation.
        let cap = 1u64 << 20;
        let mut tap = ProofTap::spawn_with_stats(writer, 3, 1 << 22, Arc::clone(&stats), Some(cap));
        // ~300k weaken pairs -> pol line well over 1 MiB (each " ~xN 1 * +" is
        // ~10-15 text bytes).
        let weakened: Vec<(PbLit, i128)> = (1..=300_000u32)
            .map(|i| {
                (
                    PbLit {
                        var: i,
                        negated: false,
                    },
                    1i128,
                )
            })
            .collect();
        tap.begin_frame(cid(1)).unwrap();
        tap.proven_resolve(cid(1), 1, 1, weakened).unwrap();
        let _lemma = tap.final_frame(0, false, Vec::new(), 0).unwrap();
        let contradiction = tap.log_rup_text(String::from(">= 1 ;")).unwrap();
        // The conclusion handshake must VOID: no certificate.
        let err = tap
            .conclude_unsat(contradiction)
            .expect_err("cap must void");
        assert!(
            matches!(err, ProofError::TapSoftCapExceeded { .. }),
            "got {err:?}"
        );
        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        // Derivation bytes were written (the partial pol line exists) but the
        // run is VOID, never a truncated-yet-concluded proof.
        assert!(
            text.contains("pol 1 s "),
            "partial derivation should be present"
        );
        assert!(
            !text.contains("conclusion"),
            "voided run must not conclude: {}",
            &text[..text.len().min(200)]
        );
        // The counter (surviving the void) shows we really crossed the cap.
        assert!(stats.snapshot().bytes_written > cap);
        // finish() also errs (poison is durable; the specific error was already
        // taken by the conclusion handshake).
        assert!(tap.finish().is_err());
    }

    #[test]
    fn dropping_the_tap_never_hangs_and_writes_no_conclusion() {
        let (writer, sink) = writer_to_shared_vec();
        let mut tap = ProofTap::spawn(writer, 3, 1 << 16);
        tap.begin_frame(cid(1)).unwrap();
        drop(tap);
        let text = String::from_utf8(sink.lock().unwrap().clone()).unwrap();
        assert!(!text.contains("conclusion"), "{text}");
    }

    /// A sink that passes writes while `open`, otherwise blocks the caller
    /// (spinning) until re-opened. Used to wedge the serializer so the ring
    /// fills and the producer hits the stall budget.
    struct BlockingSink {
        open: Arc<AtomicBool>,
    }
    impl Write for BlockingSink {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            while !self.open.load(Ordering::Acquire) {
                std::thread::sleep(Duration::from_millis(1));
            }
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// CHAOS — void-on-stall / backpressure. A wedged serializer (blocked sink)
    /// fills the ring; the producer parks in bounded quanta against the
    /// test-shrunk stall budget and then FAILS CLOSED with the backpressure
    /// error, never dropping a record or emitting a partial frame. In the
    /// solver this funnels through store_proof_error and voids the certificate.
    #[test]
    fn void_on_stall_backpressure_fails_closed() {
        // Header is emitted (on this thread) with the gate OPEN; then we shut
        // it so every SERIALIZER write blocks, wedging the consumer.
        let open = Arc::new(AtomicBool::new(true));
        let writer = VeriPbWriter::new(
            BlockingSink {
                open: Arc::clone(&open),
            },
            2,
        )
        .expect("header emits with the gate open");
        open.store(false, Ordering::SeqCst);

        // Tiny ring + short stall budget => deterministic sub-second void.
        let mut tap = ProofTap::spawn(writer, 3, 1 << 12);
        tap.set_stall_budget(Duration::from_millis(150));

        // The first RUP wedges the (now-blocked) serializer on its write; we
        // then keep pushing until the ring fills and the stall budget is spent.
        let mut backpressure: Option<ProofError> = None;
        for _ in 0..1_000_000 {
            match tap.log_rup_text(String::from(">= 1 ;")) {
                Ok(_) => continue,
                Err(error) => {
                    backpressure = Some(error);
                    break;
                }
            }
        }
        let error = backpressure.expect("a blocked sink must eventually void via backpressure");
        assert!(
            matches!(
                error,
                ProofError::TapTransport("ring backpressure stall budget exhausted")
            ),
            "expected the fail-closed backpressure void, got {error:?}"
        );

        // Release the sink BEFORE teardown so the blocked write returns and the
        // serializer join cannot hang. No conclusion was ever pushed: the run
        // is voided, never concluded.
        open.store(true, Ordering::SeqCst);
        let _ = tap.finish();
    }

    /// A sink whose write panics once `armed` (header first emits un-armed).
    struct PanicSink {
        armed: Arc<AtomicBool>,
    }
    impl Write for PanicSink {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            assert!(
                !self.armed.load(Ordering::Acquire),
                "injected serializer panic"
            );
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// CHAOS — killed/panicked serializer. A sink whose write panics unwinds the
    /// serializer thread; catch_unwind poisons the tap (first-error-wins) and
    /// the conclusion handshake surfaces the poison as an Err. No conclusion
    /// can ever commit.
    #[test]
    fn panicked_serializer_poisons_and_voids() {
        let armed = Arc::new(AtomicBool::new(false));
        let writer = VeriPbWriter::new(
            PanicSink {
                armed: Arc::clone(&armed),
            },
            2,
        )
        .expect("header emits before arming");
        armed.store(true, Ordering::SeqCst);
        let mut tap = ProofTap::spawn(writer, 3, 1 << 16);

        // The RUP is the serializer's first write after the header: it panics,
        // catch_unwind poisons, done_tx sends Err.
        let contradiction = tap.log_rup_text(String::from(">= 1 ;")).unwrap();
        let err = tap
            .conclude_unsat(contradiction)
            .expect_err("a panicked serializer must void the certificate");
        assert!(
            err.to_string().to_lowercase().contains("panic"),
            "expected the serializer-panic poison, got {err:?}"
        );
        // Poison is durable: finish() re-surfaces it too, never a clean commit.
        assert!(tap.finish().is_err());
    }
}
