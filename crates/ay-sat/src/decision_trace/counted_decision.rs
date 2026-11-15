// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission of actual Decide events, without cloning replay payloads.

use super::*;
use crate::counted_storage::Result;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};

#[cfg(test)]
mod tests;

pub(crate) fn invalid(owner: &CountedAdmission, why: &'static str) -> CountedAdmissionError {
    owner.refuse(CountedAdmissionError::Original(
        QueryError::Invalid(why).into(),
    ))
}

impl ReplayTrace {
    pub(crate) fn admit_learning_event(
        &self,
        event: &TraceEvent,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(2, 0)?;
        learning_event_bytes(event, owner)?;
        if self.events.get(self.cursor) == Some(event) {
            Ok(())
        } else {
            Err(invalid(owner, "counted learning replay mismatch"))
        }
    }

    pub(crate) fn commit_admitted_learning_event(&mut self, event: &TraceEvent) -> bool {
        if self.events.get(self.cursor) != Some(event) {
            return false;
        }
        self.cursor += 1;
        true
    }

    pub(crate) fn admit_decision(&self, lit_dimacs: i32, owner: &CountedAdmission) -> Result<()> {
        owner.admit(1, 0)?;
        if self.matches_decision(lit_dimacs) {
            Ok(())
        } else {
            // In particular, do not clone an arbitrarily large expected
            // Reduce event or allocate a mismatch diagnostic after refusal.
            Err(invalid(owner, "counted decision replay mismatch"))
        }
    }

    fn matches_decision(&self, lit_dimacs: i32) -> bool {
        matches!(self.events.get(self.cursor), Some(TraceEvent::Decide { lit_dimacs: expected }) if *expected == lit_dimacs)
    }

    pub(crate) fn commit_admitted_decision(&mut self, lit_dimacs: i32) -> bool {
        if !self.matches_decision(lit_dimacs) {
            return false;
        }
        self.cursor += 1;
        true
    }
}

impl DecisionTraceWriter {
    pub(crate) fn admit_learning_event(
        &self,
        event: &TraceEvent,
        owner: &CountedAdmission,
    ) -> Result<()> {
        let bytes = learning_event_bytes(event, owner)?;
        if self.event_count == u64::MAX {
            return Err(invalid(owner, "learning trace event counter overflow"));
        }
        let work = self
            .writer
            .buffer()
            .len()
            .checked_add(bytes)
            .and_then(|n| n.checked_mul(2))
            .and_then(|n| n.checked_add(4))
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, bytes)
    }

    pub(crate) fn admit_decision(&self, owner: &CountedAdmission) -> Result<()> {
        owner.admit(1, 0)?;
        if self.event_count == u64::MAX {
            return Err(invalid(owner, "decision trace event counter overflow"));
        }
        // Decide is one tag byte + an i32. The existing fixed-capacity buffer
        // never grows. Pay its whole pending prefix too: either a capacity or
        // 1024-event flush may write it, and terminal cleanup must not flush
        // additional bytes for free. Count the new artifact bytes as storage.
        let work = self
            .writer
            .buffer()
            .len()
            .checked_add(5)
            .and_then(|bytes| bytes.checked_mul(2))
            .and_then(|work| work.checked_add(4))
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 5)
    }

    /// Close the exact owned descriptor without BufWriter's implicit flush.
    /// A stopped decision must not perform a later, unobserved output commit.
    pub(crate) fn discard_without_flush(self) {
        let (file, pending) = self.writer.into_parts();
        drop(pending);
        drop(file);
    }

    #[cfg(test)]
    pub(crate) fn decision_test_snapshot(&self) -> (u64, Vec<u8>, usize) {
        (
            self.event_count,
            self.writer.buffer().to_vec(),
            self.writer.capacity(),
        )
    }
}

fn learning_event_bytes(event: &TraceEvent, owner: &CountedAdmission) -> Result<usize> {
    owner.admit(1, 0)?;
    match event {
        TraceEvent::Learn { .. } => Ok(9),
        TraceEvent::Inprocess { .. } => Ok(2),
        _ => Err(invalid(owner, "event is not a fixed-size learning event")),
    }
}

#[cfg(test)]
impl ReplayTrace {
    pub(crate) fn decision_test_cursor(&self) -> usize {
        self.cursor
    }

    pub(crate) fn decision_test_new(events: Vec<TraceEvent>) -> Self {
        Self { events, cursor: 0 }
    }
}

#[cfg(test)]
impl DecisionTraceWriter {
    pub(crate) fn decision_test_read_only(file: File) -> Self {
        Self {
            writer: BufWriter::with_capacity(1, file),
            event_count: 0,
        }
    }
}
