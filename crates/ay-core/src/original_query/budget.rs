// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::ops::ControlFlow;

/// An external cancellation/deadline decision; neither is a successful result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StopReason {
    /// The caller cancelled this operation.
    Cancelled,
    /// The caller's independently enforced deadline expired.
    Deadline,
}

/// Fail-closed structural validation/comparison errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum QueryError {
    /// The finite ledger cannot admit the requested work or storage.
    #[error("authored-query work exhausted")]
    Exhausted,
    /// Cancellation/deadline was observed and remains sticky.
    #[error("authored-query interrupted: {0:?}")]
    Interrupted(StopReason),
    /// A malformed structural descriptor was refused.
    #[error("invalid authored query: {0}")]
    Invalid(&'static str),
}

enum Owner<'a> {
    Checkpoint(&'a mut dyn FnMut() -> ControlFlow<StopReason>),
    Admission(&'a mut dyn FnMut(usize, usize) -> Result<(), QueryError>),
}

/// Finite work ledger and a borrowed original cancellation/resource owner.
///
/// The compatibility constructor polls cancellation/deadline but does not
/// enforce a separate storage budget. `with_admission` forwards every actual
/// work debit and explicit storage debit to the SAME original owner, before
/// the corresponding work/allocation. The owner must retain its own aggregate
/// limits and deadline across capture, checking and later consumers.
///
/// Refusal is sticky. There is no reset, refund, allowance renewal, or owned
/// resource callback. The local work ceiling is an additional guard, not a
/// replacement for the original owner's cumulative grant. This API cannot
/// itself prove that callers priced every allocation or bounded destruction.
pub struct WorkBudget<'a> {
    remaining: u64,
    stopped: Option<QueryError>,
    owner: Owner<'a>,
    refusal: Option<&'a mut dyn FnMut(QueryError)>,
}

impl<'a> WorkBudget<'a> {
    /// Compatibility ledger; the callback must check cancellation AND deadline.
    pub fn new(units: u64, checkpoint: &'a mut dyn FnMut() -> ControlFlow<StopReason>) -> Self {
        Self {
            remaining: units,
            stopped: None,
            owner: Owner::Checkpoint(checkpoint),
            refusal: None,
        }
    }

    /// Borrow a full-cost admission sink owned by the original operation.
    ///
    /// Parameters are `(work_units, storage_bytes)`, not the number of polls.
    /// The callback must check the original deadline, cancellation and aggregate
    /// work/storage grant. Storage is a caller-priced upper bound, not RSS.
    /// No second allowance or resettable observer is created here.
    ///
    /// Sticky refusal belongs to this adapter. Dropping it does not transfer
    /// its local exhaustion or caught-panic latch into the external owner.
    /// Reconstructing an adapter starts fresh local state: the operation must
    /// not do so after refusal, and an owner reused across adapters must retain
    /// its own cumulative grant, original deadline and terminal refusal.
    pub fn with_admission(
        units: u64,
        admission: &'a mut dyn FnMut(usize, usize) -> Result<(), QueryError>,
    ) -> Self {
        Self {
            remaining: units,
            stopped: None,
            owner: Owner::Admission(admission),
            refusal: None,
        }
    }

    /// Private scoped owner adapter. The notification preserves local
    /// failures across clones before the protected operation returns.
    pub(super) fn with_owner_admission(
        units: u64,
        admission: &'a mut dyn FnMut(usize, usize) -> Result<(), QueryError>,
        refusal: &'a mut dyn FnMut(QueryError),
    ) -> Self {
        Self {
            remaining: units,
            stopped: None,
            owner: Owner::Admission(admission),
            refusal: Some(refusal),
        }
    }

    fn notify_refusal(&mut self, error: QueryError) {
        if let Some(notify) = &mut self.refusal {
            notify(error);
        }
    }

    /// Remaining local work ceiling; not a cleared failure or storage balance.
    pub fn remaining(&self) -> u64 {
        self.remaining
    }

    /// Record allocation/range exhaustion without replacing an earlier stop.
    ///
    /// Frontend fallible allocations and checked arithmetic use this same latch;
    /// an allocation error may not become a nonsticky, retryable fresh grant.
    pub fn refuse_exhaustion(&mut self) -> QueryError {
        let error = *self.stopped.get_or_insert(QueryError::Exhausted);
        self.notify_refusal(error);
        error
    }

    pub(super) fn exhausted(&mut self) -> QueryError {
        self.refuse_exhaustion()
    }

    pub(super) fn tree(&mut self, entries: usize) -> Result<(), QueryError> {
        // A B-tree of constant-size keys makes bounded comparisons per level.
        // 32 units/bit conservatively exceeds std's current node branching and
        // split/search work; no string or environment vector is a tree key.
        let mut size = entries;
        loop {
            self.charge(32)?;
            if size == 0 {
                return Ok(());
            }
            size >>= 1;
        }
    }

    /// Admit finite work without an additional storage debit.
    ///
    /// Actual bulk units are forwarded unchanged by the full-cost constructor.
    /// Zero units still polls and refuses after any previous failure.
    pub fn charge(&mut self, units: usize) -> Result<(), QueryError> {
        self.admit(units, 0)
    }

    /// Admit actual work and upper-bounded storage BEFORE work/allocation.
    ///
    /// A compatibility checkpoint still runs for explicit storage-only admission,
    /// but that constructor makes NO separate aggregate storage-budget claim.
    pub fn admit(&mut self, units: usize, storage_bytes: usize) -> Result<(), QueryError> {
        if let Some(error) = self.stopped {
            return Err(error);
        }
        // Refuse before user code. If its panic is caught outside this call,
        // the same ledger may not be resumed through a permissive callback.
        self.stopped = Some(QueryError::Exhausted);
        // Keep compatibility ordering: the owner is polled before local debit.
        let result = match &mut self.owner {
            Owner::Checkpoint(checkpoint) => match checkpoint() {
                ControlFlow::Continue(()) => Ok(()),
                ControlFlow::Break(reason) => Err(QueryError::Interrupted(reason)),
            },
            Owner::Admission(admission) => admission(units, storage_bytes),
        };
        if let Err(error) = result {
            self.stopped = Some(error);
            self.notify_refusal(error);
            return Err(error);
        }
        self.stopped = None;
        let debit = u64::try_from(units).map_err(|_| self.refuse_exhaustion())?;
        self.remaining = self
            .remaining
            .checked_sub(debit)
            .ok_or_else(|| self.refuse_exhaustion())?;
        Ok(())
    }

    pub(super) fn text(&mut self, value: &str) -> Result<(), QueryError> {
        for chunk in value.as_bytes().chunks(128) {
            self.charge(chunk.len())?;
        }
        self.charge(1)
    }

    pub(super) fn text_eq(&mut self, left: &str, right: &str) -> Result<bool, QueryError> {
        self.charge(1)?;
        if left.len() != right.len() {
            return Ok(false);
        }
        for (a, b) in left
            .as_bytes()
            .chunks(128)
            .zip(right.as_bytes().chunks(128))
        {
            self.charge(a.len().saturating_add(b.len()))?;
            if a != b {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests;
