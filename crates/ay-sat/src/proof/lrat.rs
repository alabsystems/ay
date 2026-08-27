// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT proof writer for generating UNSAT certificates with clause IDs and hints.
//!
//! # Hint type boundary: `u64` vs `i64` (#5634, #5687)
//!
//! The LRAT *format* uses **signed** hint IDs: positive values are clause-ID
//! references for RUP checking, and negative values mark RAT witness boundaries
//! (see `ay-lrat-check::lrat_parser` for the format specification).
//!
//! The proof infrastructure types (`LratStep`, `ProofStep`) use `Vec<i64>` for
//! hints to support signed hint IDs needed for extended resolution (ER) and
//! blocked clause elimination (BCE) proofs (#5687).
//!
//! The default forward path still uses **unsigned** `u64` hints because most
//! internal solver hint generation (conflict analysis, RUP-only inprocessing)
//! only produces positive clause-ID references. A separate signed `&[i64]`
//! path is available for proof-manager call sites that have already validated
//! RAT witness boundaries and must preserve negative hints in the LRAT file.
//!
//! Internal hint storage (`ClauseTraceEntry::resolution_hints`) remains
//! `Vec<u64>` since resolution hints are always positive.

use super::{has_duplicate_literal, ToDimacs};
use crate::literal::Literal;
use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

const LRAT_PENDING_DELETIONS_INITIAL_CAPACITY: usize = 64;
const LRAT_PENDING_DELETIONS_MAX_RETAINED_CAPACITY: usize = 32 * 1024;
const LRAT_TEXT_LINE_INITIAL_CAPACITY: usize = 256;
const LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY: usize = 256 * 1024;
const LRAT_TEXT_ID_BYTES_ESTIMATE: usize = 21; // u64::MAX plus trailing space.
const LRAT_TEXT_LIT_BYTES_ESTIMATE: usize = 12; // i32 DIMACS literal plus trailing space.

/// Typed failure from the bounded pending-deletion buffer used by the
/// in-memory resolution-DAG producer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LratBoundedResourceFailure {
    /// The configured deletion-id count was exceeded.
    PendingDeletionLimit { limit: usize, attempted: usize },
    /// Fallible deletion-buffer growth failed.
    PendingDeletionAllocation,
}

/// Largest original-clause count from which at least one universally
/// representable LRAT addition ID remains. Binary LRAT doubles IDs, while RAT
/// hints use signed `i64`, so proof IDs are bounded by `i64::MAX`.
pub const MAX_LRAT_ORIGINAL_CLAUSES: u64 = i64::MAX as u64 - 1;

fn push_u64_decimal(buf: &mut Vec<u8>, mut value: u64) {
    if value == 0 {
        buf.push(b'0');
        return;
    }

    let mut digits = [0u8; 20];
    let mut len = 0;
    while value != 0 {
        digits[len] = b'0' + (value % 10) as u8;
        value /= 10;
        len += 1;
    }
    for digit in digits[..len].iter().rev() {
        buf.push(*digit);
    }
}

fn push_u64_decimal_field(buf: &mut Vec<u8>, value: u64) {
    push_u64_decimal(buf, value);
    buf.push(b' ');
}

fn push_i32_decimal_field(buf: &mut Vec<u8>, value: i32) {
    if value < 0 {
        buf.push(b'-');
        push_u64_decimal(buf, (-i64::from(value)) as u64);
    } else {
        push_u64_decimal(buf, value as u64);
    }
    buf.push(b' ');
}

fn push_i64_decimal_field(buf: &mut Vec<u8>, value: i64) {
    if value < 0 {
        buf.push(b'-');
        push_u64_decimal(buf, value.unsigned_abs());
    } else {
        push_u64_decimal(buf, value as u64);
    }
    buf.push(b' ');
}

fn lrat_text_add_capacity_estimate(clause_len: usize, hint_len: usize) -> usize {
    LRAT_TEXT_ID_BYTES_ESTIMATE
        .saturating_add(clause_len.saturating_mul(LRAT_TEXT_LIT_BYTES_ESTIMATE))
        .saturating_add(2)
        .saturating_add(hint_len.saturating_mul(LRAT_TEXT_ID_BYTES_ESTIMATE))
        .saturating_add(2)
}

fn lrat_text_delete_capacity_estimate(deletion_len: usize) -> usize {
    LRAT_TEXT_ID_BYTES_ESTIMATE
        .saturating_add(2)
        .saturating_add(deletion_len.saturating_mul(LRAT_TEXT_ID_BYTES_ESTIMATE))
        .saturating_add(2)
}

fn prepare_reusable_text_line(buf: &mut Vec<u8>, needed: usize) {
    debug_assert!(needed <= LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY);

    if needed > buf.capacity() || buf.capacity() > LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY {
        *buf = Vec::with_capacity(needed.max(LRAT_TEXT_LINE_INITIAL_CAPACITY));
    } else {
        buf.clear();
    }
}

fn write_lrat_text_line<W: Write>(
    writer: &mut W,
    reusable_line: &mut Vec<u8>,
    needed: usize,
    build: impl FnOnce(&mut Vec<u8>),
) -> io::Result<()> {
    if needed <= LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY {
        prepare_reusable_text_line(reusable_line, needed);
        build(reusable_line);
        writer.write_all(reusable_line)
    } else {
        let mut line = Vec::with_capacity(needed);
        build(&mut line);
        writer.write_all(&line)
    }
}

fn build_text_add_line(buf: &mut Vec<u8>, id: u64, clause: &[Literal], hints: &[u64]) {
    push_u64_decimal_field(buf, id);
    for lit in clause {
        push_i32_decimal_field(buf, lit.to_dimacs());
    }
    buf.extend_from_slice(b"0 ");
    for &hint in hints {
        push_u64_decimal_field(buf, hint);
    }
    buf.extend_from_slice(b"0\n");
}

fn build_text_add_line_i64_hints(buf: &mut Vec<u8>, id: u64, clause: &[Literal], hints: &[i64]) {
    push_u64_decimal_field(buf, id);
    for lit in clause {
        push_i32_decimal_field(buf, lit.to_dimacs());
    }
    buf.extend_from_slice(b"0 ");
    for &hint in hints {
        push_i64_decimal_field(buf, hint);
    }
    buf.extend_from_slice(b"0\n");
}

fn build_text_delete_line(buf: &mut Vec<u8>, del_id: u64, deletions: &[u64]) {
    push_u64_decimal_field(buf, del_id);
    buf.extend_from_slice(b"d ");
    for &id in deletions {
        push_u64_decimal_field(buf, id);
    }
    buf.extend_from_slice(b"0\n");
}

fn clear_pending_deletions(deletions: &mut Vec<u64>) {
    if deletions.capacity() > LRAT_PENDING_DELETIONS_MAX_RETAINED_CAPACITY {
        *deletions = Vec::with_capacity(LRAT_PENDING_DELETIONS_INITIAL_CAPACITY);
    } else {
        deletions.clear();
    }
}

/// LRAT proof writer for generating UNSAT certificates with clause IDs and hints
///
/// LRAT proofs include clause IDs and resolution hints, enabling linear-time
/// proof checking. Each added clause includes:
/// - A unique clause ID
/// - The clause literals
/// - Hint IDs (clause IDs used to derive this clause)
///
/// Like `DratWriter`, tracks I/O errors internally (CaDiCaL-style).
pub struct LratWriter<W: Write> {
    writer: W,
    binary: bool,
    /// Number of original (input) clauses; immutable after construction.
    num_original: u64,
    /// Next clause ID to assign
    next_id: u64,
    /// ID of the most recently added clause (for deletion batching)
    latest_id: u64,
    /// Pending deletions (batched for efficiency)
    pending_deletions: Vec<u64>,
    /// Optional hard pending-deletion count for bounded in-memory producers.
    max_pending_deletions: Option<usize>,
    /// First bounded-resource failure, if any.
    bounded_resource_failure: Option<LratBoundedResourceFailure>,
    /// Shared solve interrupt set on bounded storage failure.
    bounded_interrupt: Option<Arc<AtomicBool>>,
    /// Reusable buffer for text LRAT lines.
    text_line: Vec<u8>,
    /// Count of clauses successfully added (does not count failed writes)
    added_count: u64,
    /// Count of clauses deleted (batched; actual I/O failure caught on flush)
    deleted_count: u64,
    /// Set on first I/O error; subsequent writes become no-ops
    io_failed: bool,
}

impl<W: Write> LratWriter<W> {
    /// Create a new LRAT writer with text format
    ///
    /// `num_original_clauses` is the number of clauses in the original formula.
    /// The first learned clause will get ID `num_original_clauses + 1`.
    pub fn new_text(writer: W, num_original_clauses: u64) -> Self {
        Self::new(writer, false, num_original_clauses, None, None)
    }

    /// Create a new LRAT writer with binary format
    ///
    /// `num_original_clauses` is the number of clauses in the original formula.
    pub fn new_binary(writer: W, num_original_clauses: u64) -> Self {
        Self::new(writer, true, num_original_clauses, None, None)
    }

    /// Binary writer with a hard cap on deletion IDs waiting between proof
    /// additions. Used only by the bounded in-memory ResolutionDag path.
    pub(crate) fn new_binary_bounded(
        writer: W,
        num_original_clauses: u64,
        max_pending_deletions: usize,
        interrupt: Arc<AtomicBool>,
    ) -> Self {
        Self::new(
            writer,
            true,
            num_original_clauses,
            Some(max_pending_deletions),
            Some(interrupt),
        )
    }

    fn new(
        writer: W,
        binary: bool,
        num_original_clauses: u64,
        max_pending_deletions: Option<usize>,
        bounded_interrupt: Option<Arc<AtomicBool>>,
    ) -> Self {
        let next_id = num_original_clauses.checked_add(1).filter(|&id| {
            num_original_clauses <= MAX_LRAT_ORIGINAL_CLAUSES && i64::try_from(id).is_ok()
        });
        Self {
            writer,
            binary,
            num_original: num_original_clauses,
            // Preserve the infallible constructor API, but make an invalid
            // count a permanently failed writer instead of wrapping ID 0.
            next_id: next_id.unwrap_or(i64::MAX as u64),
            latest_id: num_original_clauses,
            pending_deletions: if max_pending_deletions.is_some() {
                Vec::new()
            } else {
                Vec::with_capacity(LRAT_PENDING_DELETIONS_INITIAL_CAPACITY)
            },
            max_pending_deletions,
            bounded_resource_failure: None,
            bounded_interrupt,
            text_line: if max_pending_deletions.is_some() {
                Vec::new()
            } else {
                Vec::with_capacity(LRAT_TEXT_LINE_INITIAL_CAPACITY)
            },
            added_count: 0,
            deleted_count: 0,
            io_failed: next_id.is_none(),
        }
    }

    fn fail_bounded_resource(&mut self, failure: LratBoundedResourceFailure) {
        if self.bounded_resource_failure.is_none() {
            self.bounded_resource_failure = Some(failure);
        }
        self.io_failed = true;
        if let Some(interrupt) = &self.bounded_interrupt {
            interrupt.store(true, Ordering::Release);
        }
    }

    /// Flush any pending deletions to the output
    fn flush_deletions(&mut self) -> io::Result<()> {
        if self.pending_deletions.is_empty() {
            return Ok(());
        }

        if self.binary {
            self.writer.write_all(b"d")?;
            // Take the pending deletions to avoid borrow conflict
            let mut deletions = std::mem::take(&mut self.pending_deletions);
            for id in &deletions {
                self.write_binary_id(*id)?;
            }
            self.writer.write_all(&[0])?;
            self.recycle_pending_deletions(&mut deletions);
            self.pending_deletions = deletions;
        } else {
            // Text format: "step_id d id1 id2 ... 0". Burning a fresh ID is
            // AY's convention (#4398), not a format rule — drat-trim/CaDiCaL
            // stamp the line with the previous addition's ID and the reference
            // checker ignores the field — so do not derive a parser rule here.
            let del_id = self.next_id;
            self.next_id = del_id + 1;
            let needed = lrat_text_delete_capacity_estimate(self.pending_deletions.len());
            write_lrat_text_line(&mut self.writer, &mut self.text_line, needed, |line| {
                build_text_delete_line(line, del_id, &self.pending_deletions)
            })?;
            self.latest_id = del_id;
            if self.max_pending_deletions.is_some() {
                self.pending_deletions.clear();
            } else {
                clear_pending_deletions(&mut self.pending_deletions);
            }
        }

        Ok(())
    }

    fn recycle_pending_deletions(&self, deletions: &mut Vec<u64>) {
        if self.max_pending_deletions.is_some() {
            deletions.clear();
        } else {
            clear_pending_deletions(deletions);
        }
    }

    /// Log addition of a learned clause with resolution hints.
    ///
    /// Returns the assigned clause ID. After an I/O failure, subsequent calls
    /// are no-ops returning `Ok(0)` (CaDiCaL-style). Counter only increments
    /// on successful writes.
    ///
    /// # Hint type boundary (`u64` vs `i64`)
    ///
    /// The writer uses unsigned `u64` hints because AY currently only generates
    /// RUP proofs (all hints are positive clause-ID references). The LRAT
    /// *format* uses signed hint IDs — negative values mark RAT witness
    /// boundaries (see `ay-lrat-check` parser). If AY adds RAT proof
    /// generation in the future, this API must change to `&[i64]` (#5634).
    pub fn add(&mut self, clause: &[Literal], hints: &[u64]) -> io::Result<u64> {
        debug_assert!(
            !has_duplicate_literal(clause),
            "BUG: LRAT add contains duplicate literal in clause of length {}",
            clause.len()
        );
        // Empty hint lists are part of LRAT syntax (for example, a blocked
        // extension-definition clause). They do not confer axiom/trust status:
        // a standalone checker still decides whether the addition is valid.
        // ProofManager therefore suppresses unproved TrustedTransform steps.
        debug_assert!(
            hints.iter().all(|&h| h != 0),
            "BUG: LRAT hint contains ID 0 -- hint IDs must be valid clause references",
        );
        // RUP-only guard: all hints must fit in i64 for LRAT format compatibility.
        // This will be removed when the writer switches to i64 hints for RAT support (#5634).
        debug_assert!(
            hints.iter().all(|&h| i64::try_from(h).is_ok()),
            "BUG: LRAT hint exceeds i64::MAX -- would corrupt signed LRAT format",
        );
        // Note: hint range validation (h < next_id) is done in ProofManager::validate_lrat_hints
        // which has access to the full set of registered clause IDs. The LratWriter does not
        // track externally registered IDs (from Solver::add_clause), so range checks here
        // would produce false positives.
        if self.io_failed {
            return Ok(0);
        }
        // Flush any pending deletions first
        if let Err(e) = self.flush_deletions() {
            self.io_failed = true;
            return Err(e);
        }

        let id = self.next_id;
        if id > i64::MAX as u64 {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "LRAT clause ID exceeds the signed/binary encoding limit",
            ));
        }
        let result = if self.binary {
            self.write_binary_add(id, clause, hints)
        } else {
            self.write_text_add(id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.next_id = id + 1;
                self.io_failed |= self.next_id > i64::MAX as u64;
                self.latest_id = id;
                self.added_count += 1;
                Ok(id)
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Log addition of a learned clause with already-validated signed LRAT
    /// hints.
    ///
    /// Negative hints are RAT witness boundaries and are preserved exactly in
    /// text output. Binary output encodes the LRAT sign bit instead of forcing
    /// hints through the unsigned RUP-only writer path.
    pub(crate) fn add_signed_hints(
        &mut self,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<u64> {
        debug_assert!(
            !has_duplicate_literal(clause),
            "BUG: LRAT add contains duplicate literal in clause of length {}",
            clause.len()
        );
        debug_assert!(
            hints.iter().all(|&h| h != 0),
            "BUG: LRAT signed hint contains ID 0 -- hint IDs must be valid clause references",
        );
        debug_assert!(
            hints.iter().all(|&h| h != i64::MIN),
            "BUG: LRAT signed hint i64::MIN cannot be encoded",
        );
        if self.io_failed {
            return Ok(0);
        }
        if let Err(e) = self.flush_deletions() {
            self.io_failed = true;
            return Err(e);
        }

        let id = self.next_id;
        if id > i64::MAX as u64 {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "LRAT clause ID exceeds the signed/binary encoding limit",
            ));
        }
        let result = if self.binary {
            self.write_binary_add_i64_hints(id, clause, hints)
        } else {
            self.write_text_add_i64_hints(id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.next_id = id + 1;
                self.io_failed |= self.next_id > i64::MAX as u64;
                self.latest_id = id;
                self.added_count += 1;
                Ok(id)
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Write an addition with a pre-assigned clause ID (#8105).
    ///
    /// Used by backward reconstruction: the ID was reserved during solving
    /// via `reserve_id`, and now the addition line is written with proper hints.
    /// Does not advance `next_id`: the ID was already reserved. Pending
    /// deletions deliberately remain buffered until all older reserved
    /// additions have been backfilled, so a deletion can never precede the
    /// addition it refers to.
    pub fn add_with_id(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        if clause_id == 0
            || clause_id > i64::MAX as u64
            || clause_id >= self.next_id
            || clause_id <= self.latest_id
            || hints
                .iter()
                .any(|&hint| hint == 0 || hint > i64::MAX as u64)
        {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid or non-monotonic pre-assigned LRAT addition",
            ));
        }
        let result = if self.binary {
            self.write_binary_add(clause_id, clause, hints)
        } else {
            self.write_text_add(clause_id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.latest_id = clause_id;
                self.added_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Write an addition with a pre-assigned clause ID and already-validated
    /// signed hints.
    ///
    /// Negative entries delimit RAT witness groups and must be preserved
    /// exactly. As with the unsigned variant, pending deletions remain buffered
    /// until the reserved additions have been backfilled.
    pub(crate) fn add_with_id_signed_hints(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        debug_assert!(
            hints.iter().all(|&h| h != 0 && h != i64::MIN),
            "BUG: signed LRAT hints must be representable non-zero IDs"
        );
        if self.io_failed {
            return Ok(());
        }
        if clause_id == 0
            || clause_id > i64::MAX as u64
            || clause_id >= self.next_id
            || clause_id <= self.latest_id
            || hints.iter().any(|&hint| hint == 0 || hint == i64::MIN)
        {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid or non-monotonic pre-assigned signed LRAT addition",
            ));
        }
        let result = if self.binary {
            self.write_binary_add_i64_hints(clause_id, clause, hints)
        } else {
            self.write_text_add_i64_hints(clause_id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.latest_id = clause_id;
                self.added_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Emit a caller-prevalidated positive-RUP addition without repeating
    /// whole-hint scans. The bounded ResolutionDag producer has already
    /// enforced nonzero/unique/known hints under its deadline and count caps.
    pub(crate) fn add_bounded_prevalidated_rup(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<u64> {
        if self.io_failed {
            return Ok(0);
        }
        if let Err(error) = self.flush_deletions() {
            self.io_failed = true;
            return Err(error);
        }
        let id = self.next_id;
        if id > i64::MAX as u64 {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "LRAT clause ID exceeds the signed/binary encoding limit",
            ));
        }
        let result = if self.binary {
            self.write_binary_add(id, clause, hints)
        } else {
            self.write_text_add(id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.next_id = id + 1;
                self.io_failed |= self.next_id > i64::MAX as u64;
                self.latest_id = id;
                self.added_count += 1;
                Ok(id)
            }
            Err(error) => {
                self.io_failed = true;
                Err(error)
            }
        }
    }

    /// Emit a pre-assigned caller-prevalidated positive-RUP addition without
    /// generic RAT/duplicate preflight allocation or scans.
    pub(crate) fn add_with_id_bounded_prevalidated_rup(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        if clause_id == 0
            || clause_id > i64::MAX as u64
            || clause_id >= self.next_id
            || clause_id <= self.latest_id
        {
            self.io_failed = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid or non-monotonic pre-assigned bounded LRAT addition",
            ));
        }
        let result = if self.binary {
            self.write_binary_add_i64_hints(clause_id, clause, hints)
        } else {
            self.write_text_add_i64_hints(clause_id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.latest_id = clause_id;
                self.added_count += 1;
                Ok(())
            }
            Err(error) => {
                self.io_failed = true;
                Err(error)
            }
        }
    }

    /// Write addition in text format: "id lit1 lit2 ... 0 hint1 hint2 ... 0"
    fn write_text_add(&mut self, id: u64, clause: &[Literal], hints: &[u64]) -> io::Result<()> {
        let needed = lrat_text_add_capacity_estimate(clause.len(), hints.len());
        write_lrat_text_line(&mut self.writer, &mut self.text_line, needed, |line| {
            build_text_add_line(line, id, clause, hints)
        })
    }

    fn write_text_add_i64_hints(
        &mut self,
        id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        let needed = lrat_text_add_capacity_estimate(clause.len(), hints.len());
        write_lrat_text_line(&mut self.writer, &mut self.text_line, needed, |line| {
            build_text_add_line_i64_hints(line, id, clause, hints)
        })
    }

    /// Write addition in binary format
    fn write_binary_add(&mut self, id: u64, clause: &[Literal], hints: &[u64]) -> io::Result<()> {
        self.writer.write_all(b"a")?;
        self.write_binary_id(id)?;
        for lit in clause {
            self.write_binary_lit(*lit)?;
        }
        self.writer.write_all(&[0])?;
        for &hint in hints {
            self.write_binary_id(hint)?;
        }
        self.writer.write_all(&[0])
    }

    fn write_binary_add_i64_hints(
        &mut self,
        id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        self.writer.write_all(b"a")?;
        self.write_binary_id(id)?;
        for lit in clause {
            self.write_binary_lit(*lit)?;
        }
        self.writer.write_all(&[0])?;
        for &hint in hints {
            self.write_binary_signed_id(hint)?;
        }
        self.writer.write_all(&[0])
    }

    /// Log deletion of a clause by ID
    ///
    /// Deletions are batched for efficiency and flushed on the next add.
    /// After an I/O failure, subsequent calls are no-ops.
    pub fn delete(&mut self, clause_id: u64) -> io::Result<()> {
        // Clause ID 0 is a reserved sentinel and never a valid clause reference.
        // The full ID-references-known-clause check is done by ProofManager::emit_delete()
        // which has visibility into both original and derived clause IDs.
        debug_assert!(
            clause_id != 0,
            "BUG: LRAT delete of clause ID 0 (reserved sentinel)"
        );
        debug_assert!(
            clause_id < self.next_id,
            "BUG: LRAT delete of future clause ID {clause_id} (next_id={})",
            self.next_id,
        );
        if self.io_failed {
            return Ok(());
        }
        if let Some(limit) = self.max_pending_deletions {
            let attempted = self.pending_deletions.len().checked_add(1).ok_or_else(|| {
                self.fail_bounded_resource(LratBoundedResourceFailure::PendingDeletionLimit {
                    limit,
                    attempted: usize::MAX,
                });
                io::Error::other("bounded LRAT pending-deletion count overflow")
            })?;
            if attempted > limit {
                self.fail_bounded_resource(LratBoundedResourceFailure::PendingDeletionLimit {
                    limit,
                    attempted,
                });
                return Err(io::Error::other(
                    "bounded LRAT pending-deletion limit exceeded",
                ));
            }
            if self.pending_deletions.len() == self.pending_deletions.capacity() {
                let current = self.pending_deletions.capacity();
                let target = if current == 0 {
                    LRAT_PENDING_DELETIONS_INITIAL_CAPACITY.min(limit)
                } else {
                    current.saturating_mul(2).min(limit)
                }
                .max(attempted);
                if self
                    .pending_deletions
                    .try_reserve_exact(target - self.pending_deletions.len())
                    .is_err()
                {
                    self.fail_bounded_resource(
                        LratBoundedResourceFailure::PendingDeletionAllocation,
                    );
                    return Err(io::Error::other(
                        "bounded LRAT pending-deletion allocation failed",
                    ));
                }
                if self.pending_deletions.capacity() > limit {
                    let actual = self.pending_deletions.capacity();
                    self.pending_deletions = Vec::new();
                    self.fail_bounded_resource(LratBoundedResourceFailure::PendingDeletionLimit {
                        limit,
                        attempted: actual,
                    });
                    return Err(io::Error::other(
                        "bounded LRAT allocator exceeded pending-deletion limit",
                    ));
                }
            }
        }
        self.deleted_count += 1;
        self.pending_deletions.push(clause_id);
        Ok(())
    }

    /// Write a literal in binary encoding (same logic as `DratWriter`).
    ///
    /// Uses checked arithmetic to prevent silent overflow (#4474).
    fn write_binary_lit(&mut self, lit: Literal) -> io::Result<()> {
        let var = lit
            .variable()
            .0
            .checked_add(1) // 1-indexed
            .expect("BUG: variable index overflow in binary LRAT encoding");
        let encoded = var
            .checked_mul(2)
            .expect("BUG: literal encoding overflow in binary LRAT encoding")
            + u32::from(!lit.is_positive()); // +0 or +1; safe since 2*var is even

        let mut val = encoded;
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    /// Write a clause ID in binary encoding (variable-length).
    ///
    /// Binary LRAT encodes all values (IDs, literals, hints) as
    /// `2 * abs(val) + sign_bit` in LEB128. IDs are always positive,
    /// so: `val = 2 * id`.
    ///
    /// Reference: CaDiCaL `lrattracer.cpp:56-68`, drat-trim `decompress.c:34-46`.
    fn write_binary_id(&mut self, id: u64) -> io::Result<()> {
        let mut val = id
            .checked_mul(2)
            .expect("BUG: clause ID overflow in binary LRAT encoding");
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    fn write_binary_signed_id(&mut self, id: i64) -> io::Result<()> {
        debug_assert!(id != 0, "BUG: binary LRAT signed ID 0 is reserved");
        let magnitude = id.unsigned_abs();
        let mut val = magnitude
            .checked_mul(2)
            .expect("BUG: signed clause ID overflow in binary LRAT encoding");
        if id < 0 {
            val = val
                .checked_add(1)
                .expect("BUG: signed clause ID sign-bit overflow in binary LRAT encoding");
        }
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    /// Get the next clause ID that will be assigned
    pub fn next_id(&self) -> u64 {
        self.next_id
    }

    /// Return whether a deletion batch is waiting to be flushed before the next
    /// LRAT addition.
    pub(crate) fn has_pending_deletions(&self) -> bool {
        !self.pending_deletions.is_empty()
    }

    /// Advance the ID counter without emitting a proof step.
    ///
    /// Used by the fail-close mechanism (#4713): when a theory-lemma write is
    /// suppressed, the solver still allocates a clause ID. Calling this keeps
    /// the writer's counter synchronized so subsequent writes (e.g., the empty
    /// clause) receive non-conflicting IDs.
    pub fn reserve_id(&mut self) -> u64 {
        if self.io_failed || self.next_id > i64::MAX as u64 {
            self.io_failed = true;
            return 0;
        }
        let id = self.next_id;
        self.next_id = id + 1;
        self.io_failed |= self.next_id > i64::MAX as u64;
        id
    }

    /// Advance the ID counter so it is at least `min_next`.
    ///
    /// Used to synchronize the writer's counter after axiom IDs are allocated
    /// through a separate path (e.g., `register_lrat_axiom` via `next_lrat_id`
    /// in ProofManager). No-op if the counter is already >= `min_next`.
    pub fn advance_past(&mut self, min_next: u64) {
        if min_next > i64::MAX as u64 {
            self.io_failed = true;
            return;
        }
        if min_next > self.next_id {
            self.next_id = min_next;
        }
    }

    /// Get the number of original clauses
    pub fn num_original_clauses(&self) -> u64 {
        self.num_original
    }

    /// Get the number of clauses successfully added
    pub fn added_count(&self) -> u64 {
        self.added_count
    }

    /// Get the number of clauses deleted
    pub fn deleted_count(&self) -> u64 {
        self.deleted_count
    }

    /// Returns true if any I/O error occurred during proof writing
    pub fn has_io_error(&self) -> bool {
        self.io_failed
    }

    /// Return the first bounded pending-deletion resource failure.
    pub(crate) fn bounded_resource_failure(&self) -> Option<LratBoundedResourceFailure> {
        self.bounded_resource_failure
    }

    #[cfg(test)]
    pub(crate) fn text_line_capacity_for_tests(&self) -> usize {
        self.text_line.capacity()
    }

    #[cfg(test)]
    pub(crate) fn pending_deletions_capacity_for_tests(&self) -> usize {
        self.pending_deletions.capacity()
    }

    #[cfg(test)]
    pub(crate) const fn max_retained_text_line_capacity_for_tests() -> usize {
        LRAT_TEXT_LINE_MAX_RETAINED_CAPACITY
    }

    #[cfg(test)]
    pub(crate) const fn max_retained_pending_deletions_capacity_for_tests() -> usize {
        LRAT_PENDING_DELETIONS_MAX_RETAINED_CAPACITY
    }

    /// Flush the writer (including any pending deletions; no-op after I/O failure)
    pub fn flush(&mut self) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        if let Err(e) = self.flush_deletions() {
            self.io_failed = true;
            return Err(e);
        }
        match self.writer.flush() {
            Ok(()) => Ok(()),
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Finalize the proof by flushing pending deletions and returning the inner writer
    ///
    /// Returns an error if an I/O failure occurred during proof writing.
    pub fn into_inner(mut self) -> io::Result<W> {
        if self.io_failed {
            return Err(io::Error::other(
                "LRAT proof writer encountered I/O error during solve",
            ));
        }
        self.flush_deletions()?;
        Ok(self.writer)
    }
}
