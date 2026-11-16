// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller-metered producer interning; no typing or source/proof authority.

use std::sync::atomic::Ordering;

use super::NEXT_TERM_ENTRY_STAMP;
use super::{Constant, Sort, TermData, TermEntry, TermEntryStamp, TermId, TermStore};

pub(super) mod counted;
mod fresh;
mod reserve;
mod shape;
#[cfg(test)]
mod tests;

/// Refusal of bounded producer construction, never a solver verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum ControlledTermInternError {
    /// A progress callback, checked identity/accounting bound, or fallible
    /// allocation refused growth.
    #[error("controlled term interning resource limit exceeded")]
    ResourceLimit,
    /// The requested term or sort is outside the supported fragment.
    #[error("controlled term interning does not admit this fragment")]
    UnsupportedFragment,
    /// An input identity or payload is inconsistent with the live arena.
    #[error("controlled term interning requires live, consistent input")]
    InvalidInput,
    /// A checker snapshot was supplied where a producer store is required.
    #[error("checker-only term snapshots cannot mint producer terms")]
    ReadOnlySnapshot,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum StoreRole {
    Producer,
    ReadOnlySnapshot,
}

type Result<T> = std::result::Result<T, ControlledTermInternError>;

struct Admission<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    refused: bool,
}

impl Admission<'_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Result<()> {
        if self.refused {
            return Err(ControlledTermInternError::ResourceLimit);
        }
        // A caught callback panic may not continue this adapter.
        self.refused = true;
        if !(self.progress)(work, bytes) {
            return Err(ControlledTermInternError::ResourceLimit);
        }
        self.refused = false;
        Ok(())
    }
}

impl TermStore {
    /// Intern a borrowed, bounded term in this SAME producer arena.
    ///
    /// Admits Bool/BV1..128 constants, named applications with at most three
    /// live children and a name of at most 64 bytes, Not, and Ite. Output sorts
    /// are Bool/BV1..128 or flat BV64-index arrays of those cells. Variables,
    /// binders, indexed symbols and other payloads refuse; freshness/name-table
    /// construction is a separate operation, not silently fabricated here.
    ///
    /// This establishes bounded structural construction and exact sort-aware
    /// hash-consing, NOT operator typing, source equivalence or proof authority.
    /// The caller validates application semantics and owns its original finite
    /// work/storage/deadline/cancellation envelope across every call. A callback
    /// can borrow the SAME WorkBudget and retain its precise refusal separately.
    /// This method creates no allowance, callback, timer, reset or solver.
    ///
    /// Reservations and conservative allocation history can remain on refusal.
    /// If the final poll refuses after commit, no TermId is returned although
    /// the inert interned entry can remain. Caller-owned input disposal, allocator
    /// aborts, RSS, hard preemption and whole-route accounting are not promised.
    pub fn try_intern_with_progress(
        &mut self,
        term: &TermData,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = self.intern_controlled(term, sort, &mut admission);
        // All inner temporary payloads have dropped before this final fence.
        let final_poll = admission.pay(0, 0);
        match (result, final_poll) {
            (Ok(id), Ok(())) => Ok(id),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }

    fn intern_controlled(
        &mut self,
        term: &TermData,
        sort: &Sort,
        admission: &mut Admission<'_>,
    ) -> Result<TermId> {
        if self.store_role != StoreRole::Producer {
            return Err(ControlledTermInternError::ReadOnlySnapshot);
        }
        shape::validate(self, term, sort, admission)?;
        self.intern_controlled_validated(term, sort, admission)
    }

    // Only the public checked fragment or the fixed-purpose fresh-name factory
    // reaches this private entry. No caller may graft an arbitrary Var identity.
    fn intern_controlled_validated(
        &mut self,
        term: &TermData,
        sort: &Sort,
        admission: &mut Admission<'_>,
    ) -> Result<TermId> {
        // Complete bounded hash payload and scalar/sort comparison work.
        admission.pay(512, 0)?;
        let hash = Self::compute_hash(term);
        let plan = self.controlled_bucket_plan(hash, term, sort, admission)?;
        if let Some(id) = plan.existing {
            return Ok(id);
        }
        let id = checked_term_id(self.terms.len())?;
        admission.pay(512, 0)?;
        let credit = self.controlled_credit(plan.bucket_bytes)?;
        let prepared = self.controlled_reserve(hash, &plan, admission)?;
        // The fixed payload envelope precedes every bounded clone.
        admission.pay(512, 8192)?;
        let owned = shape::copy(term)?;
        let owned_sort = sort.clone();
        admission.pay(512, 0)?;
        let stamp = next_entry_stamp(&NEXT_TERM_ENTRY_STAMP)?;
        admission.pay(512, 0)?;
        self.controlled_settle(credit, Self::heap_size(&owned), prepared.growth)?;
        self.controlled_probe_fee(admission)?;
        admission.pay(0, 0)?;
        // All vectors/table slots are reserved, and u64 hashing cannot call
        // caller code. No fallible allocation or callback occurs during commit.
        let field_presence = self.entry_field_presence(&owned, &owned_sort);
        self.controlled_commit_bucket(
            hash,
            id,
            TermEntry {
                field_presence,
                term: owned,
                sort: owned_sort,
                stamp,
            },
            prepared,
        )?;
        Ok(id)
    }
}

fn checked_term_id(len: usize) -> Result<TermId> {
    let raw = u32::try_from(len).map_err(|_| ControlledTermInternError::ResourceLimit)?;
    if raw == u32::MAX {
        return Err(ControlledTermInternError::ResourceLimit);
    }
    Ok(TermId(raw))
}

fn next_entry_stamp(counter: &std::sync::atomic::AtomicU64) -> Result<TermEntryStamp> {
    // Match the ordinary producer: sibling stores cannot exhaust identity
    // space merely by winning an atomic race.
    #[allow(deprecated)]
    counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
            current.checked_add(1)
        })
        .map(TermEntryStamp)
        .map_err(|_| ControlledTermInternError::ResourceLimit)
}
