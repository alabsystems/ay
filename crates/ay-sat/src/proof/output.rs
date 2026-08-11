// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified proof output facade that abstracts over DRAT and LRAT formats.

use super::{BoxedWriter, DratWriter, LratBoundedResourceFailure, LratWriter};
use crate::literal::Literal;
use std::io::{self, Write};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// Unified proof output that can be either DRAT or LRAT format.
///
/// This enum allows the solver to write proofs in either format while maintaining
/// a single proof_writer field. LRAT proofs include clause IDs and resolution hints
/// for linear-time verification.
///
/// The writer type is erased via `BoxedWriter` so that `ProofOutput` (and therefore
/// `ProofManager` and `Solver`) are non-generic. This eliminates the `W: Write`
/// type parameter that previously threaded through ~32 impl blocks and ~17,300
/// lines of solver code (#5088).
#[non_exhaustive]
pub enum ProofOutput {
    /// DRAT proof format (no hints, clause-based deletions)
    Drat(DratWriter<BoxedWriter>),
    /// LRAT proof format (with hints, ID-based deletions)
    Lrat(LratWriter<BoxedWriter>),
}

impl ProofOutput {
    /// Create a new DRAT text proof output
    pub fn drat_text(writer: impl Write + Send + 'static) -> Self {
        Self::Drat(DratWriter::new_text(BoxedWriter::new(writer)))
    }

    /// Create a new DRAT binary proof output
    pub fn drat_binary(writer: impl Write + Send + 'static) -> Self {
        Self::Drat(DratWriter::new_binary(BoxedWriter::new(writer)))
    }

    /// Create a new LRAT text proof output
    pub fn lrat_text(writer: impl Write + Send + 'static, num_original_clauses: u64) -> Self {
        Self::Lrat(LratWriter::new_text(
            BoxedWriter::new(writer),
            num_original_clauses,
        ))
    }

    /// Create a new LRAT binary proof output
    pub fn lrat_binary(writer: impl Write + Send + 'static, num_original_clauses: u64) -> Self {
        Self::Lrat(LratWriter::new_binary(
            BoxedWriter::new(writer),
            num_original_clauses,
        ))
    }

    /// Create binary LRAT output with a hard in-memory pending-deletion cap.
    pub(crate) fn lrat_binary_bounded(
        writer: impl Write + Send + 'static,
        num_original_clauses: u64,
        max_pending_deletions: usize,
        interrupt: Arc<AtomicBool>,
    ) -> Self {
        Self::Lrat(LratWriter::new_binary_bounded(
            BoxedWriter::new(writer),
            num_original_clauses,
            max_pending_deletions,
            interrupt,
        ))
    }

    /// Check if this is an LRAT proof
    pub fn is_lrat(&self) -> bool {
        matches!(self, Self::Lrat(_))
    }

    /// Additions written so far (DRAT only; 0 for LRAT).
    pub fn adds_written(&self) -> u64 {
        match self {
            Self::Drat(w) => w.added_count(),
            Self::Lrat(_) => 0,
        }
    }

    /// Add a learned clause to the proof.
    ///
    /// For DRAT, hints are ignored. For LRAT, hints are the clause IDs used
    /// to derive this clause (RUP-only, unsigned). Returns the clause ID
    /// (for LRAT) or 0 (for DRAT). See `LratWriter::add` for the u64/i64
    /// boundary note (#5634).
    pub fn add(&mut self, clause: &[Literal], hints: &[u64]) -> io::Result<u64> {
        match self {
            Self::Drat(w) => {
                w.add(clause)?;
                Ok(0)
            }
            Self::Lrat(w) => w.add(clause, hints),
        }
    }

    /// Add a clause while preserving already-validated signed LRAT hints.
    ///
    /// Negative hints are RAT witness boundaries. DRAT has no hint channel, so
    /// the clause is emitted normally there and the return ID remains `0`.
    pub(crate) fn add_signed_lrat_hints(
        &mut self,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<u64> {
        match self {
            Self::Drat(w) => {
                w.add(clause)?;
                Ok(0)
            }
            Self::Lrat(w) => w.add_signed_hints(clause, hints),
        }
    }

    /// Add a PR (propagation-redundant) clause with a witness assignment.
    ///
    /// For DRAT this emits a DPR `a`-line (`clause… witness… 0`). The LPR (linear
    /// PR) route for LRAT is not yet wired — emitting a PR clause without its
    /// linear hints would be unverifiable, so the LRAT arm fails closed with an
    /// error rather than write an unsound/incomplete step.
    pub fn add_pr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        match self {
            Self::Drat(w) => w.add_pr(clause, witness),
            Self::Lrat(_) => Err(io::Error::other(
                "PR/LPR clause emission is not yet supported on the LRAT writer",
            )),
        }
    }

    /// Add an SR (substitution-redundant) clause with a full substitution witness.
    ///
    /// For DRAT this emits a DSR `a`-line (`clause… witness… 0`) where `witness` is
    /// the substitution-witness token stream. The LSR route for LRAT is not wired
    /// (the SR proof is elaborated externally by `dsr-trim`), so the LRAT arm fails
    /// closed rather than write an unverifiable step.
    pub fn add_sr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        match self {
            Self::Drat(w) => w.add_sr(clause, witness),
            Self::Lrat(_) => Err(io::Error::other(
                "SR/LSR clause emission is not yet supported on the LRAT writer",
            )),
        }
    }

    /// Add a clause with a pre-assigned ID to the LRAT proof (#8105).
    ///
    /// Used by backward reconstruction to write learned clause additions that
    /// had their IDs reserved during solving via `reserve_id`. For DRAT, this
    /// is a no-op (DRAT doesn't use IDs).
    pub fn add_with_id(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<()> {
        match self {
            Self::Drat(_) => Ok(()),
            Self::Lrat(w) => w.add_with_id(clause_id, clause, hints),
        }
    }

    /// Emit a bounded-producer prevalidated positive-RUP addition.
    pub(crate) fn add_bounded_prevalidated_rup(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<u64> {
        match self {
            Self::Drat(writer) => {
                writer.add(clause)?;
                Ok(0)
            }
            Self::Lrat(writer) => writer.add_bounded_prevalidated_rup(clause, hints),
        }
    }

    /// Emit a pre-assigned bounded-producer positive-RUP addition.
    pub(crate) fn add_with_id_bounded_prevalidated_rup(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        match self {
            Self::Drat(_) => Ok(()),
            Self::Lrat(writer) => {
                writer.add_with_id_bounded_prevalidated_rup(clause_id, clause, hints)
            }
        }
    }

    /// Add a clause with a pre-assigned ID using already-validated signed LRAT
    /// hints.
    ///
    /// This preserves RAT witness-group delimiters instead of coercing the
    /// backward chain through the unsigned RUP-only API.
    pub(crate) fn add_with_id_signed_lrat_hints(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        match self {
            Self::Drat(_) => Ok(()),
            Self::Lrat(w) => w.add_with_id_signed_hints(clause_id, clause, hints),
        }
    }

    /// Advance the LRAT writer's ID counter without emitting a proof step.
    ///
    /// For DRAT, this is a no-op (returns 0). For LRAT, advances the counter
    /// so subsequent writes receive non-conflicting IDs. Used by the fail-close
    /// mechanism when theory-lemma writes are suppressed (#4713).
    pub fn reserve_id(&mut self) -> u64 {
        match self {
            Self::Drat(_) => 0,
            Self::Lrat(w) => w.reserve_id(),
        }
    }

    pub(crate) fn next_lrat_id(&self) -> Option<u64> {
        match self {
            Self::Drat(_) => None,
            Self::Lrat(w) => Some(w.next_id()),
        }
    }

    pub(crate) fn has_pending_lrat_deletions(&self) -> bool {
        match self {
            Self::Drat(_) => false,
            Self::Lrat(w) => w.has_pending_deletions(),
        }
    }

    /// Advance the LRAT writer's ID counter to at least `min_next`.
    ///
    /// Synchronizes the writer after axiom IDs are allocated through a
    /// separate path (ProofManager::next_lrat_id). No-op for DRAT.
    pub fn advance_past(&mut self, min_next: u64) {
        match self {
            Self::Drat(_) => {}
            Self::Lrat(w) => w.advance_past(min_next),
        }
    }

    /// Delete a clause from the proof
    ///
    /// For DRAT, uses the clause literals. For LRAT, uses the clause ID.
    pub fn delete(&mut self, clause: &[Literal], clause_id: u64) -> io::Result<()> {
        match self {
            Self::Drat(w) => w.delete(clause),
            Self::Lrat(w) => w.delete(clause_id),
        }
    }

    /// Flush the proof writer
    pub fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Drat(w) => w.flush(),
            Self::Lrat(w) => w.flush(),
        }
    }

    /// Get the number of clauses successfully added
    pub fn added_count(&self) -> u64 {
        match self {
            Self::Drat(w) => w.added_count(),
            Self::Lrat(w) => w.added_count(),
        }
    }

    /// Get the number of clauses deleted
    pub fn deleted_count(&self) -> u64 {
        match self {
            Self::Drat(w) => w.deleted_count(),
            Self::Lrat(w) => w.deleted_count(),
        }
    }

    /// Returns true if any I/O error occurred during proof writing
    ///
    /// Check this at proof finalization to detect truncated/corrupted proofs
    /// caused by disk-full, broken-pipe, or other write errors during solve.
    pub fn has_io_error(&self) -> bool {
        match self {
            Self::Drat(w) => w.has_io_error(),
            Self::Lrat(w) => w.has_io_error(),
        }
    }

    /// Typed failure from bounded LRAT storage outside the byte writer.
    pub(crate) fn lrat_bounded_resource_failure(&self) -> Option<LratBoundedResourceFailure> {
        match self {
            Self::Drat(_) => None,
            Self::Lrat(writer) => writer.bounded_resource_failure(),
        }
    }

    /// Get the inner boxed writer back, consuming the `ProofOutput`.
    ///
    /// Returns an error if any I/O failure occurred during proof writing,
    /// or if LRAT finalization (flushing pending deletions) fails.
    pub fn into_inner(self) -> io::Result<BoxedWriter> {
        match self {
            Self::Drat(w) => w.into_inner(),
            Self::Lrat(w) => w.into_inner(),
        }
    }

    /// Extract proof bytes as `Vec<u8>`, consuming the `ProofOutput`.
    ///
    /// Convenience for the common test pattern where the writer is `Vec<u8>`.
    /// Panics if the underlying writer is not `Vec<u8>`.
    pub fn into_vec(self) -> io::Result<Vec<u8>> {
        self.into_inner().map(|bw| {
            bw.into_vec()
                .expect("proof writer was not Vec<u8> — use into_inner() for non-Vec writers")
        })
    }
}
