// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Event-preserving ownership transfer for a fresh, fixed original CNF.
//!
//! A learned event retains the number of originals already registered, not
//! their IDs or a second literal/metadata copy. Reserved input IDs need not
//! compare below an intervening learned ID. The merged iterator follows those
//! event positions; sorting all rows by ID would hide forward references.

use super::{ClauseTrace, ClauseTraceEntryRef, TraceEntries};
use crate::literal::Literal;
use std::mem::size_of;

#[path = "clause_trace_originals/control.rs"]
mod control;
#[path = "clause_trace_originals/validate.rs"]
mod validate;
pub use control::ConsumingTraceStop;
pub(crate) use control::OriginalControl;

#[derive(Clone, Debug, Default)]
pub(super) struct OriginalStorage {
    pub(super) arena: Option<OriginalArena>,
    pub(super) count: u32,
    pub(super) bytes: usize,
    pub(super) control: Option<OriginalControl>,
}

impl OriginalStorage {
    pub(super) fn is_pending(&self) -> bool {
        self.control.is_some() && self.arena.is_none()
    }
}

/// These three buffers are MOVED from OriginalLedger, never reconstructed.
#[derive(Clone, Debug)]
pub(crate) struct OriginalArena {
    pub(crate) literals: Vec<Literal>,
    pub(crate) offsets: Vec<u32>,
    pub(crate) ids: Vec<u64>,
}

impl OriginalArena {
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        self.literals
            .capacity()
            .checked_mul(size_of::<Literal>())?
            .checked_add(self.offsets.capacity().checked_mul(size_of::<u32>())?)?
            .checked_add(self.ids.capacity().checked_mul(size_of::<u64>())?)
    }

    pub(super) fn entry(&self, index: usize) -> Option<ClauseTraceEntryRef<'_>> {
        let start = *self.offsets.get(index)? as usize;
        let end = self
            .offsets
            .get(index + 1)
            .map_or(self.literals.len(), |n| *n as usize);
        Some(ClauseTraceEntryRef {
            id: *self.ids.get(index)?,
            clause: self.literals.get(start..end)?,
            is_original: true,
            origin: super::ClauseEventOrigin::Assumption,
            resolution_hints: &[],
        })
    }
}

impl<'a> TraceEntries<'a> {
    pub(crate) fn lookup_work_bound(&self) -> usize {
        if self.originals.is_none() || self.meta.is_empty() {
            return 0;
        }
        self.meta.len().bit_width() as usize
    }

    pub(super) fn combined_entry(
        &self,
        originals: &'a OriginalArena,
        index: usize,
    ) -> Option<ClauseTraceEntryRef<'a>> {
        if index >= self.len() {
            return None;
        }
        // Validated prefixes make derived event positions strictly increasing.
        // Sequential iteration below is O(1)/event; random access is O(log L).
        let mut low = 0;
        let mut high = self.meta.len();
        while low < high {
            let mid = low + (high - low) / 2;
            if self.meta[mid].original_prefix_len as usize + mid < index {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        if let Some(entry) = self.meta.get(low) {
            if entry.original_prefix_len as usize + low == index {
                return Some(self.view(entry));
            }
        }
        originals.entry(index.checked_sub(low)?)
    }
}

impl ClauseTrace {
    pub(crate) fn begin_original_transfer(&mut self, control: OriginalControl) -> bool {
        if !self.is_empty() || self.originals.control.is_some() {
            return false;
        }
        self.originals.control = Some(control);
        true
    }

    pub(crate) fn original_transfer_pending(&self) -> bool {
        self.originals.is_pending()
    }

    pub(crate) fn original_control(&self) -> Option<OriginalControl> {
        self.originals.control.clone()
    }

    /// Called exactly at ledger admission, before propagation can derive a row.
    /// Only O(1) state changes here: no per-original trace metadata allocation.
    pub(crate) fn note_ledger_original(&mut self, count: usize, bytes: usize) -> bool {
        let admitted = self.originals.count.checked_add(1);
        if self.has_empty
            || self.proof_work_exhausted
            || self.is_truncated
            || admitted.map(|n| n as usize) != Some(count)
            || !self.original_event_open(false)
        {
            self.mark_proof_work_exhausted();
            return false;
        }
        if !self
            .originals
            .control
            .as_ref()
            .is_some_and(|control| control.work(4, &mut |_| true))
        {
            self.mark_proof_work_exhausted();
            return false;
        }
        self.originals.count = admitted.unwrap_or(0);
        self.originals.bytes = bytes;
        if self.used_bytes() > self.budget_bytes {
            self.is_truncated = true;
            return false;
        }
        true
    }

    pub(crate) fn owned_original_bytes(&self) -> usize {
        self.originals.bytes
    }

    pub(super) fn original_event_open(&self, is_original: bool) -> bool {
        let Some(control) = &self.originals.control else {
            return true;
        };
        if is_original {
            // A new original bypassing register_ledger_original is unsupported.
            control.refuse();
            return false;
        }
        control.open()
    }

    /// Validate storage and event order before publishing any borrowed view.
    /// The existing independent resolution checker still decides proof validity.
    pub(crate) fn finish_original_transfer(
        &mut self,
        originals: OriginalArena,
        num_vars: usize,
        work: &mut dyn FnMut(u64) -> bool,
    ) -> bool {
        if !self.original_transfer_pending()
            || self.is_truncated
            || self.proof_work_exhausted
            || originals.ids.len() != self.originals.count as usize
            || originals
                .retained_bytes()
                .is_none_or(|bytes| bytes > self.originals.bytes)
            || !self.original_event_open(false)
        {
            return false;
        }
        // The ordinary bulk-load slack reclamation may shrink the source
        // ledger before handoff. Keep the actual retained capacity, not a
        // historical reservation; growth without another admission is refused.
        let Some(bytes) = originals.retained_bytes() else {
            return false;
        };
        self.originals.bytes = bytes;
        let Some(control) = self.original_control() else {
            return false;
        };
        let mut admitted = |units| control.work(units, work);
        if !validate::structure(self, &originals, num_vars, &mut admitted) {
            self.mark_proof_work_exhausted();
            if let Some(control) = &self.originals.control {
                control.refuse();
            }
            return false;
        }
        self.originals.arena = Some(originals);
        // Mutators on an extracted trace clear provenance as usual. The caller
        // retains this same control until solver cleanup and the final fence.
        self.originals.control = None;
        true
    }
}

#[cfg(test)]
#[path = "clause_trace_originals/tests.rs"]
mod tests;
