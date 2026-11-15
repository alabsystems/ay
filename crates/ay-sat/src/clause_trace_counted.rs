// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact borrowed trace transaction. Preparation never publishes an event;
//! the linear token binds the trace, metadata, clause and forward hints.
//! Commit has no callback/allocation. It must stay inside the caller's owning
//! solver guard, with a final same-owner fence before any result escapes.

use super::{capacity::ArenaCapacities, ClauseTrace, EntryMeta};
use crate::counted_storage::{try_reserved_exact, Result};
use crate::decision_trace::counted_decision::invalid;
use crate::literal::Literal;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

#[path = "clause_trace_counted/originals.rs"]
mod originals;
#[path = "clause_trace_counted/reserve.rs"]
mod reserve;
#[cfg(test)]
#[path = "clause_trace_counted/tests.rs"]
mod tests;

/// An exclusive, single-use reservation for the exact borrowed payload.
/// Dropping it publishes nothing; counted capacity changes may remain.
pub(crate) struct PreparedTraceAdd<'trace, 'data> {
    trace: &'trace mut ClauseTrace,
    meta: EntryMeta,
    clause: &'data [Literal],
    hints: &'data [u64],
}

impl PreparedTraceAdd<'_, '_> {
    /// Callback-free and allocation-free. The caller must check its original
    /// owner immediately before the whole coupled publication, then fence the
    /// resulting private state before exposing it. No proof is certified here.
    pub(crate) fn commit(self) {
        self.trace.publish_entry(self.meta, self.clause, self.hints);
    }
}

impl ClauseTrace {
    pub(crate) fn prepare_counted_add<'trace, 'data>(
        &'trace mut self,
        id: u64,
        clause: &'data [Literal],
        is_original: bool,
        hints: &'data [u64],
        owner: &CountedAdmission,
    ) -> Result<PreparedTraceAdd<'trace, 'data>> {
        owner.admit(24, 0)?;
        if self.is_truncated || self.proof_work_exhausted || id == 0 {
            return Err(invalid(
                owner,
                "counted trace requires a complete nonzero-ID event",
            ));
        }
        // The optional probe prints to an external descriptor and is not an
        // admitted part of this in-memory transaction.
        if ay_core::captured_misc_cli_flags().is_none() || super::probe_trace_dup_enabled() {
            return Err(invalid(
                owner,
                "counted trace duplicate diagnostic output is not admitted",
            ));
        }
        if !self.original_event_open(is_original) {
            return Err(invalid(owner, "counted trace original event is closed"));
        }
        self.check_counted_id(id, owner)?;
        let meta = self
            .preflight_entry_meta(id, clause, is_original, hints)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        let work = clause
            .len()
            .checked_add(hints.len())
            .and_then(|n| n.checked_add(self.scope_assumptions_capacity()))
            .and_then(|n| n.checked_add(8))
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 0)?; // append + provenance retirement + token drop
        reserve::prepare(self, clause.len(), hints.len(), owner)?;
        owner.check()?;
        Ok(PreparedTraceAdd {
            trace: self,
            meta,
            clause,
            hints,
        })
    }

    fn check_counted_id(&self, id: u64, owner: &CountedAdmission) -> Result<()> {
        for entry in &self.meta {
            owner.admit(1, 0)?;
            if entry.id == id {
                return Err(invalid(owner, "duplicate counted trace ID"));
            }
        }
        if let Some(originals) = &self.originals.arena {
            for &original in &originals.ids {
                owner.admit(1, 0)?;
                if original == id {
                    return Err(invalid(owner, "counted trace ID aliases an original"));
                }
            }
        }
        // During pending original transfer the solver's original ledger owns
        // the actual IDs. Its coupled insertion must enforce that namespace;
        // this trace does not manufacture an unavailable lookup/authority.
        Ok(())
    }
}
