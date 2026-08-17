// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-tap serializer: replays micro-op records into VeriPB proof text.
//!
//! The serializer owns the [`VeriPbWriter`] for the whole solve. Frames are
//! accumulated into ONE reused pol-RPN expression string (one proof line and
//! ONE allocated id per learned lemma); non-frame records map onto the
//! existing [`ProofStep`] emissions. Every allocating record carries the
//! solver-pre-allocated id, and the writer-returned id is asserted equal
//! (reconciliation) — any divergence poisons the tap at the first bad line
//! instead of surfacing hours later as a checker rejection.

use std::fmt::Write as _;
use std::io::Write;

use crate::cutting_planes::negate_lit;

use super::super::steps::{ConstraintId, ProofStep};
use super::super::veripb::{format_constraint, format_lit, ProofError, VeriPbWriter};
use super::record::TapRecord;

/// Flow control returned by [`TapSerializer::process`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SerializerFlow {
    /// Keep consuming records.
    Continue,
    /// A conclusion block was emitted and flushed; complete the handshake.
    Concluded,
    /// Explicit shutdown record; stop consuming.
    Shutdown,
}

/// Per-solve serializer state machine (single-threaded; the thread loop in
/// `tap::spawn` drives it from the ring).
pub(crate) struct TapSerializer<W: Write> {
    writer: VeriPbWriter<W>,
    /// The pol RPN expression of the open frame (reused across frames).
    frame: Option<String>,
    /// Checkpoint intermediates emitted for the open frame; deleted by the
    /// serializer right after the frame's final (or aborting) record.
    frame_intermediates: Vec<u64>,
    /// `WeakenCont` pairs buffered for the next `ProvenResolve` (64 KiB
    /// record chunking). Must be empty at every other record boundary.
    pending_weaken: Vec<(crate::types::PbLit, i128)>,
}

impl<W: Write> TapSerializer<W> {
    pub(crate) fn new(writer: VeriPbWriter<W>) -> Self {
        Self {
            writer,
            frame: None,
            frame_intermediates: Vec::new(),
            pending_weaken: Vec::new(),
        }
    }

    /// Consumes the serializer, returning the underlying writer (tests).
    #[cfg(test)]
    pub(crate) fn into_writer(self) -> VeriPbWriter<W> {
        self.writer
    }

    fn frame_mut(&mut self, context: &'static str) -> Result<&mut String, ProofError> {
        self.frame.as_mut().ok_or(ProofError::TapProtocol(context))
    }

    /// Emits an allocating step and reconciles the id against the record's.
    fn log_reconciled(&mut self, step: ProofStep, expected: u64) -> Result<(), ProofError> {
        let actual = self.writer.log_step(step)?;
        if actual.get() != expected {
            return Err(ProofError::TapIdDesync {
                expected,
                actual: actual.get(),
            });
        }
        Ok(())
    }

    fn pid(raw: u64) -> Result<ConstraintId, ProofError> {
        ConstraintId::new(raw).ok_or(ProofError::TapProtocol("record carried proof id 0"))
    }

    /// Deletes the open frame's checkpoint intermediates (spec kind 9:
    /// serializer-injected `del id` right after the frame's final line —
    /// counter-safe because `Delete` never allocates).
    fn delete_frame_intermediates(&mut self) -> Result<(), ProofError> {
        for raw in std::mem::take(&mut self.frame_intermediates) {
            self.writer.log_step(ProofStep::Delete(Self::pid(raw)?))?;
        }
        Ok(())
    }

    /// Processes one record.
    pub(crate) fn process(&mut self, record: TapRecord) -> Result<SerializerFlow, ProofError> {
        // 64 KiB chunking protocol: buffered WeakenCont pairs may only be
        // followed by more WeakenCont records or the consuming ProvenResolve.
        if !self.pending_weaken.is_empty()
            && !matches!(
                record,
                TapRecord::WeakenCont { .. } | TapRecord::ProvenResolve { .. }
            )
        {
            return Err(ProofError::TapProtocol(
                "WeakenCont chunk not followed by its ProvenResolve",
            ));
        }
        match record {
            TapRecord::BeginFrame { conflict_pid } => {
                if self.frame.is_some() {
                    return Err(ProofError::TapProtocol("BeginFrame with a frame open"));
                }
                Self::pid(conflict_pid)?;
                let mut expr = String::with_capacity(256);
                // Load the conflict row; the initial saturate of conflict
                // analysis is this `s ` (checker normal form is implicit).
                let _ = write!(expr, "{conflict_pid} s ");
                self.frame = Some(expr);
                Ok(SerializerFlow::Continue)
            }
            TapRecord::ProvenResolve {
                reason_pid,
                c,
                w,
                weakened,
            } => {
                Self::pid(reason_pid)?;
                if c <= 0 || w <= 0 {
                    return Err(ProofError::TapProtocol(
                        "ProvenResolve requires positive pivot coefficients",
                    ));
                }
                // Chunked weaken lists (64 KiB record cap): buffered
                // WeakenCont pairs precede the record's own list in order.
                let pending = std::mem::take(&mut self.pending_weaken);
                let expr = self.frame_mut("ProvenResolve outside a frame")?;
                // Reduce the reason: add rem*(~l >= 0) literal axioms (partial
                // weakening under normal form), ceiling-divide by c, scale by
                // w, add into the running conflict (pivot pair cancels), s.
                let _ = write!(expr, "{reason_pid} ");
                for (lit, rem) in pending.into_iter().chain(weakened) {
                    if rem <= 0 {
                        return Err(ProofError::TapProtocol(
                            "ProvenResolve weakening remainder must be positive",
                        ));
                    }
                    let _ = write!(expr, "{} {rem} * + ", format_lit(negate_lit(lit)));
                }
                if c > 1 {
                    let _ = write!(expr, "{c} d ");
                }
                if w > 1 {
                    let _ = write!(expr, "{w} * ");
                }
                expr.push_str("+ s ");
                Ok(SerializerFlow::Continue)
            }
            TapRecord::HeuristicResolve {
                reason_pid,
                conflict_factor,
                reason_factor,
                div,
            } => {
                Self::pid(reason_pid)?;
                if conflict_factor <= 0 || reason_factor <= 0 || div.is_some_and(|d| d <= 1) {
                    return Err(ProofError::TapProtocol(
                        "HeuristicResolve requires positive factors and divisor > 1",
                    ));
                }
                let expr = self.frame_mut("HeuristicResolve outside a frame")?;
                if conflict_factor > 1 {
                    let _ = write!(expr, "{conflict_factor} * ");
                }
                let _ = write!(expr, "{reason_pid} ");
                if reason_factor > 1 {
                    let _ = write!(expr, "{reason_factor} * ");
                }
                expr.push_str("+ s ");
                if let Some(d) = div {
                    let _ = write!(expr, "{d} d s ");
                }
                Ok(SerializerFlow::Continue)
            }
            TapRecord::FinalFrame {
                gcd1,
                weaken_ran,
                weakened,
                gcd2,
                lemma_pid,
            } => {
                let mut expr = self
                    .frame
                    .take()
                    .ok_or(ProofError::TapProtocol("FinalFrame outside a frame"))?;
                // Post-loop strengthening: saturate + GCD, then (rarely) the
                // conservative weakening pipeline + re-saturate + GCD. Logging
                // the weakening closes the trusted-path fidelity gap where a
                // weakened lemma was stored under a pre-weakening proof id.
                expr.push_str("s ");
                if gcd1 > 1 {
                    let _ = write!(expr, "{gcd1} d ");
                }
                if weaken_ran {
                    for lit in weakened {
                        // VeriPB weakening is VARIABLE-based and polarity-
                        // independent ("<constraint> <variable> w"; the spec
                        // forbids a negated operand and 3.0.2 hard-rejects
                        // `~xN w` with a parse error). The capture carries the
                        // removed literal in native polarity, so emit only its
                        // variable — the semantics match the solver's mutation
                        // (zero the coefficient, reduce the degree) either way.
                        let _ = write!(expr, "x{} w ", lit.var);
                    }
                    expr.push_str("s ");
                    if gcd2 > 1 {
                        let _ = write!(expr, "{gcd2} d ");
                    }
                }
                expr.push(';');
                self.log_reconciled(ProofStep::Polynomial(expr), lemma_pid)?;
                // Checkpoint intermediates are dead once the lemma line is
                // emitted: delete them immediately (spec kind 9 cleanup).
                self.delete_frame_intermediates()?;
                Ok(SerializerFlow::Continue)
            }
            TapRecord::AbortFrame => {
                // Discard the buffered frame; no id was allocated for the
                // LEMMA. Intermediates already emitted by checkpoints stay
                // allocated on both sides — delete them to keep the checker
                // database tight; the id sequence stays reconciled.
                self.frame = None;
                self.pending_weaken.clear();
                self.delete_frame_intermediates()?;
                Ok(SerializerFlow::Continue)
            }
            TapRecord::Checkpoint { intermediate_pid } => {
                let mut expr = self
                    .frame
                    .take()
                    .ok_or(ProofError::TapProtocol("Checkpoint outside a frame"))?;
                // Close the running pol line at the intermediate id, then
                // continue the frame from it. The expression always ends with
                // a complete op here (checkpoints fire only at op boundaries).
                expr.push(';');
                self.log_reconciled(ProofStep::Polynomial(expr), intermediate_pid)?;
                let mut continued = String::with_capacity(256);
                let _ = write!(continued, "{intermediate_pid} ");
                self.frame = Some(continued);
                self.frame_intermediates.push(intermediate_pid);
                Ok(SerializerFlow::Continue)
            }
            TapRecord::WeakenCont { pairs } => {
                if self.frame.is_none() {
                    return Err(ProofError::TapProtocol("WeakenCont outside a frame"));
                }
                self.pending_weaken.extend(pairs);
                Ok(SerializerFlow::Continue)
            }
            TapRecord::Rup { pid, terms, degree } => {
                let mut sorted = terms;
                sorted.sort_by_key(|(lit, _)| (lit.var, lit.negated));
                let text = format_constraint(&sorted, degree);
                self.log_reconciled(ProofStep::Rup(text), pid)?;
                Ok(SerializerFlow::Continue)
            }
            TapRecord::RupText { pid, text } => {
                self.log_reconciled(ProofStep::Rup(text), pid)?;
                Ok(SerializerFlow::Continue)
            }
            TapRecord::Delete { pid } => {
                self.writer.log_step(ProofStep::Delete(Self::pid(pid)?))?;
                Ok(SerializerFlow::Continue)
            }
            TapRecord::ConcludeUnsat { contradiction_pid } => {
                self.writer.conclude_unsat(Self::pid(contradiction_pid)?)?;
                self.writer.flush()?;
                Ok(SerializerFlow::Concluded)
            }
            TapRecord::ConcludeSat { assignment } => {
                self.writer.conclude_sat(&assignment)?;
                self.writer.flush()?;
                Ok(SerializerFlow::Concluded)
            }
            TapRecord::Shutdown => {
                self.writer.flush()?;
                Ok(SerializerFlow::Shutdown)
            }
        }
    }
}

/// Formats one frame worth of records into the exact pol expression (tests).
/// (No test uses it yet — kept for owner review.)
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn frame_expression(records: Vec<TapRecord>) -> String {
    let writer = VeriPbWriter::new(Vec::new(), 0).expect("in-memory header");
    let mut serializer = TapSerializer::new(writer);
    for record in records {
        serializer.process(record).expect("scripted records");
    }
    let bytes = serializer.into_writer().into_inner();
    String::from_utf8(bytes).expect("proof text is UTF-8")
}

#[cfg(test)]
mod tests;
