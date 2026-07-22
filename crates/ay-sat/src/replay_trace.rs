// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic replay trace for reproducible SAT debugging.
//!
//! Records solver decisions, conflicts, learned clauses, restarts, and DB
//! reductions to a compact binary file. The trace can be replayed to
//! reproduce exact solver behavior and detect divergences after code changes.
//!
//! ## Binary Format
//!
//! ```text
//! Header:  b"AYRT" (magic) | version: u8 | num_vars: u32
//! Events:  tag: u8 | payload (tag-dependent, see TraceEvent)
//! ```
//!
//! All integers are little-endian. The format is designed for ~100 bytes per
//! conflict, yielding ~100MB for 1M-conflict solves.
//!
//! ## Usage
//!
//! Recording: set `AY_REPLAY_TRACE=<path>` before running AY on a DIMACS file.
//! Replay: call `ReplayTraceReader::open()` and step through events.

#[cfg(test)]
use crate::literal::Literal;
#[cfg(test)]
use std::fs::File;
#[cfg(test)]
use std::io::{self, BufReader, BufWriter, Read, Write};
#[cfg(test)]
use std::path::Path;

/// Magic bytes for replay trace files.
#[cfg(test)]
const MAGIC: [u8; 4] = *b"AYRT";

/// Current format version.
#[cfg(test)]
const VERSION: u8 = 1;

/// Tag bytes for each event type.
#[cfg(test)]
const TAG_DECIDE: u8 = 0x01;
#[cfg(test)]
const TAG_CONFLICT: u8 = 0x02;
#[cfg(test)]
const TAG_LEARN: u8 = 0x03;
#[cfg(test)]
const TAG_RESTART: u8 = 0x04;
#[cfg(test)]
const TAG_REDUCE_DB: u8 = 0x05;

/// A single solver event recorded during solving.
///
/// Used by `ReplayTraceReader` to parse trace files. Currently test-only;
/// production replay mode is tracked in #4541 acceptance criteria.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraceEvent {
    /// Decision literal (includes polarity).
    Decide(Literal),
    /// Conflict detected at the given clause index.
    Conflict(u32),
    /// Learned clause with LBD and literals.
    Learn { lbd: u16, clause: Vec<Literal> },
    /// Restart event.
    Restart,
    /// Clause database reduction (number of clauses deleted).
    ReduceDb(u32),
}

/// Writer for binary replay trace files.
///
/// Currently test-only. Production replay mode is tracked in #4541.
#[cfg(test)]
pub(crate) struct ReplayTraceWriter {
    writer: BufWriter<File>,
    event_count: u64,
}

#[cfg(test)]
impl ReplayTraceWriter {
    /// Create a new trace writer and write the file header.
    pub(crate) fn new(path: &Path, num_vars: u32) -> io::Result<Self> {
        let file = File::create(path)?;
        let mut writer = BufWriter::new(file);
        writer.write_all(&MAGIC)?;
        writer.write_all(&[VERSION])?;
        writer.write_all(&num_vars.to_le_bytes())?;
        writer.flush()?;
        Ok(Self {
            writer,
            event_count: 0,
        })
    }

    /// Record a decision event.
    #[inline]
    pub(crate) fn write_decide(&mut self, lit: Literal) {
        let _ = self.writer.write_all(&[TAG_DECIDE]);
        let _ = self.writer.write_all(&lit.0.to_le_bytes());
        self.event_count += 1;
        self.maybe_flush();
    }

    /// Record a conflict event.
    #[inline]
    pub(crate) fn write_conflict(&mut self, clause_idx: u32) {
        let _ = self.writer.write_all(&[TAG_CONFLICT]);
        let _ = self.writer.write_all(&clause_idx.to_le_bytes());
        self.event_count += 1;
        self.maybe_flush();
    }

    /// Record a learned clause event.
    #[inline]
    pub(crate) fn write_learn(&mut self, lbd: u16, clause: &[Literal]) {
        let _ = self.writer.write_all(&[TAG_LEARN]);
        let _ = self.writer.write_all(&lbd.to_le_bytes());
        let len = clause.len() as u16;
        let _ = self.writer.write_all(&len.to_le_bytes());
        for &lit in clause {
            let _ = self.writer.write_all(&lit.0.to_le_bytes());
        }
        self.event_count += 1;
        self.maybe_flush();
    }

    /// Record a restart event.
    #[inline]
    pub(crate) fn write_restart(&mut self) {
        let _ = self.writer.write_all(&[TAG_RESTART]);
        self.event_count += 1;
        self.maybe_flush();
    }

    /// Record a DB reduction event.
    #[inline]
    pub(crate) fn write_reduce_db(&mut self, deleted_count: u32) {
        let _ = self.writer.write_all(&[TAG_REDUCE_DB]);
        let _ = self.writer.write_all(&deleted_count.to_le_bytes());
        self.event_count += 1;
        self.maybe_flush();
    }

    /// Flush and return the event count.
    pub(crate) fn finish(&mut self) -> u64 {
        let _ = self.writer.flush();
        self.event_count
    }

    /// Flush periodically to avoid data loss on crash.
    #[inline]
    fn maybe_flush(&mut self) {
        if self.event_count & 0xFFF == 0 {
            let _ = self.writer.flush();
        }
    }
}

/// Reader for binary replay trace files.
///
/// Reads events lazily from a buffered file reader.
/// Currently test-only; production replay mode is tracked in #4541.
#[cfg(test)]
pub(crate) struct ReplayTraceReader {
    reader: BufReader<File>,
    num_vars: u32,
    events_read: u64,
}

#[cfg(test)]
impl std::fmt::Debug for ReplayTraceReader {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReplayTraceReader")
            .field("num_vars", &self.num_vars)
            .field("events_read", &self.events_read)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
impl ReplayTraceReader {
    /// Open a trace file and read the header.
    pub(crate) fn open(path: &Path) -> io::Result<Self> {
        let file = File::open(path)?;
        let mut reader = BufReader::new(file);

        // Read and validate magic
        let mut magic = [0u8; 4];
        reader.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("invalid replay trace magic: expected AYRT, got {magic:?}"),
            ));
        }

        // Read and validate version
        let mut ver = [0u8; 1];
        reader.read_exact(&mut ver)?;
        if ver[0] != VERSION {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("unsupported replay trace version: {ver}", ver = ver[0]),
            ));
        }

        // Read num_vars
        let mut buf = [0u8; 4];
        reader.read_exact(&mut buf)?;
        let num_vars = u32::from_le_bytes(buf);

        Ok(Self {
            reader,
            num_vars,
            events_read: 0,
        })
    }

    /// Number of variables recorded in the trace header.
    pub(crate) fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Number of events read so far.
    pub(crate) fn events_read(&self) -> u64 {
        self.events_read
    }

    /// Read the next event, or `None` at EOF.
    pub(crate) fn next_event(&mut self) -> io::Result<Option<TraceEvent>> {
        let mut tag = [0u8; 1];
        match self.reader.read_exact(&mut tag) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e),
        }

        let event = match tag[0] {
            TAG_DECIDE => {
                let lit_raw = self.read_u32()?;
                TraceEvent::Decide(Literal(lit_raw))
            }
            TAG_CONFLICT => {
                let idx = self.read_u32()?;
                TraceEvent::Conflict(idx)
            }
            TAG_LEARN => {
                let lbd = self.read_u16()?;
                let len = self.read_u16()?;
                let mut clause = Vec::with_capacity(len as usize);
                for _ in 0..len {
                    let lit_raw = self.read_u32()?;
                    clause.push(Literal(lit_raw));
                }
                TraceEvent::Learn { lbd, clause }
            }
            TAG_RESTART => TraceEvent::Restart,
            TAG_REDUCE_DB => {
                let count = self.read_u32()?;
                TraceEvent::ReduceDb(count)
            }
            other => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("unknown trace event tag: 0x{other:02x}"),
                ))
            }
        };

        self.events_read += 1;
        Ok(Some(event))
    }

    /// Read all remaining events into a vector.
    pub(crate) fn read_all(&mut self) -> io::Result<Vec<TraceEvent>> {
        let mut events = Vec::new();
        while let Some(event) = self.next_event()? {
            events.push(event);
        }
        Ok(events)
    }

    fn read_u16(&mut self) -> io::Result<u16> {
        let mut buf = [0u8; 2];
        self.reader.read_exact(&mut buf)?;
        Ok(u16::from_le_bytes(buf))
    }

    fn read_u32(&mut self) -> io::Result<u32> {
        let mut buf = [0u8; 4];
        self.reader.read_exact(&mut buf)?;
        Ok(u32::from_le_bytes(buf))
    }
}

#[cfg(test)]
#[path = "replay_trace_tests.rs"]
mod tests;
