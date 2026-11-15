// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh original-prefix admission: constant-time ID checks, no all-pairs scan.

use super::*;
use crate::solver::FreshInputTraceEvent;

impl ClauseTrace {
    pub(crate) fn with_capacity_counted(capacity: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(std::mem::size_of::<Self>().saturating_add(32), 0)?;
        let mut trace = Self::new();
        let bytes = capacity
            .checked_mul(std::mem::size_of::<EntryMeta>())
            .filter(|bytes| *bytes <= trace.budget_bytes)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        let meta = try_reserved_exact(owner, capacity)?;
        let actual = meta
            .capacity()
            .checked_mul(std::mem::size_of::<EntryMeta>())
            .filter(|actual| *actual <= trace.budget_bytes)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        owner.admit(
            meta.capacity().saturating_sub(capacity),
            actual.saturating_sub(bytes),
        )?;
        trace.meta = meta;
        owner.check()?;
        Ok(trace)
    }

    /// The unforgeable token comes from the exclusively borrowed fresh solver.
    /// No public raw ID or caller-provided monotonicity assertion grants this.
    /// The session establishes empty storage once; every subsequent event uses
    /// this same method, preserving strictly increasing IDs inductively. Real
    /// skipped original IDs and the session's empty-input derived row are kept.
    pub(crate) fn prepare_counted_original<'trace, 'data>(
        &'trace mut self,
        original: &FreshInputTraceEvent<'_>,
        clause: &'data [Literal],
    ) -> Result<PreparedTraceAdd<'trace, 'data>> {
        let owner = original.owner();
        owner.admit(40, 0)?;
        if self.is_truncated
            || self.proof_work_exhausted
            || self.originals.arena.is_some()
            || self.originals.control.is_some()
            || self.originals.count != 0
            || self.originals.bytes != 0
            || self.solver_num_vars.is_some()
            || !self.hint_pool.is_empty()
            || self.meta.len() != original.prefix()
            || self.meta.last().map(|last| last.id) != original.previous()
            || original.id() == 0
            || original.previous().is_some_and(|id| id >= original.id())
            || (!original.is_original() && !clause.is_empty())
        {
            return Err(invalid(owner, "fresh original trace prefix changed"));
        }
        if ay_core::captured_misc_cli_flags().is_none() || super::super::probe_trace_dup_enabled() {
            return Err(invalid(
                owner,
                "counted original trace diagnostic output is not admitted",
            ));
        }
        let meta = self
            .preflight_entry_meta(original.id(), clause, original.is_original(), &[])
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        owner.admit(clause.len().saturating_add(8), 0)?;
        reserve::prepare(self, clause.len(), 0, owner)?;
        owner.check()?;
        Ok(PreparedTraceAdd {
            trace: self,
            meta,
            clause,
            hints: &[],
        })
    }
}
