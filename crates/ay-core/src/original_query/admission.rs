// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicitly transferred original work/copy grant, not solver/proof authority.

use super::{QueryError, WorkBudget};
use crate::resource::CheckStop;
use crate::time::Instant;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

mod controls;
mod counted;
mod shared;
mod usage;
pub use counted::CountedAdmission;
pub use usage::{AdmissionUsage, CountedAdmissionError, COUNTED_ADMISSION_USAGE_VERSION};
#[cfg(test)]
mod tests;

/// A caller's finite invocation grant, MOVED into one original owner.
///
/// This is not an RSS limit or a SAT-conflict rlimit. The caller must supply
/// its already-chosen original work and cumulative logical-copy allowance.
/// Construction does not prove that all allocations were priced.
pub struct FiniteAdmissionGrant {
    work: u64,
    copy_bytes: usize,
}

impl FiniteAdmissionGrant {
    /// Record the caller's finite logical work and cumulative copy allowance.
    /// Construction alone grants no CPU, solver verdict or proof authority.
    pub fn new(work: u64, copy_bytes: usize) -> Self {
        Self { work, copy_bytes }
    }
}

/// First terminal refusal shared by every clone and scoped adapter.
///
/// A Boolean CheckStop observation carries no precise cancellation cause.
/// Callback/unwind handling is cooperative and cannot catch abort or preempt
/// an arbitrary callback/destructor that does not return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum OriginalAdmissionError {
    /// The underlying query ledger, cancellation/deadline check, or structural
    /// validation refused.
    #[error(transparent)]
    Query(#[from] QueryError),
    /// The original stop observer returned true and requested termination.
    #[error("the original check-stop observer refused")]
    ObserverStopped,
    /// The original stop observer unwound.
    #[error("the original check-stop observer panicked")]
    ObserverPanicked,
    /// The protected operation unwound.
    #[error("the protected original operation panicked")]
    OperationPanicked,
    /// An observer attempted to reenter its own active owner.
    #[error("the original admission observer reentered its own owner")]
    Reentrant,
    /// Shared accounting could no longer be safely accessed.
    #[error("the original admission bookkeeping was poisoned")]
    Poisoned,
}

impl OriginalAdmissionError {
    fn adapter_error(self) -> QueryError {
        match self {
            Self::Query(error) => error,
            // The scoped helper returns the precise shared error. Do not
            // fabricate Cancelled from an unclassified Boolean observer.
            _ => QueryError::Exhausted,
        }
    }
}

/// Caller-owned admission for ONE original invocation.
///
/// Clones retain the same counters, immutable absolute end, original observer
/// and first refusal. There is no reset/refund/grant replacement or new clock.
/// Short locks serialize paired debits; observers run without the state lock.
/// Same-thread observer recursion refuses, while other threads wait under the
/// SAME original end. Accepted debits are never refunded, even after failure.
///
/// No model extraction is wired by this prerequisite alone. Native publication
/// controls, minimum caps and exact-query one-shot certificates remain separate
/// mandatory authorities. Callers must check after their OWN later cleanup.
#[derive(Clone)]
pub struct OriginalAdmission {
    inner: Arc<shared::Inner>,
    end: Instant,
}

impl OriginalAdmission {
    /// Transfer the original grant and absolute end, without polling/resetting
    /// the original observer or deriving a fresh relative deadline.
    pub fn new(grant: FiniteAdmissionGrant, end: Instant, observer: CheckStop) -> Self {
        Self {
            inner: Arc::new(shared::Inner::new(grant, Some(end), observer, None)),
            end,
        }
    }

    /// Return the same original absolute endpoint, without renewal.
    pub fn deadline(&self) -> Instant {
        self.end
    }

    /// A zero-debit original-owner poll, including previous terminal failure.
    pub fn check(&self) -> Result<(), OriginalAdmissionError> {
        self.inner.admit(0, 0)
    }

    /// Borrow one adapter over the SAME aggregate grant, then poll after its
    /// local scratch cleanup. Every adapter refusal/caught unwind folds into
    /// the shared latch; constructing another adapter cannot renew it.
    ///
    /// The local ceiling is only the then-remaining original work, not a new
    /// allowance. Every debit still reaches the original serialized account.
    /// Fallible allocations must call WorkBudget::refuse_exhaustion before
    /// ignoring or returning a failure. Successful output remains DATA: this
    /// helper neither seals a solve result nor bounds later output disposal.
    pub fn with_work<T>(
        &self,
        operation: impl FnOnce(&mut WorkBudget<'_>) -> Result<T, QueryError>,
    ) -> Result<T, OriginalAdmissionError> {
        with_work(&self.inner, operation)
    }
}

/// The compatibility and counted handles use this exact same scoped adapter.
fn with_work<T>(
    inner: &shared::Inner,
    operation: impl FnOnce(&mut WorkBudget<'_>) -> Result<T, QueryError>,
) -> Result<T, OriginalAdmissionError> {
    inner.admit(0, 0)?;
    let local_ceiling = inner.remaining_work()?;
    let mut sink = |work, bytes| {
        inner
            .admit(work, bytes)
            .map_err(OriginalAdmissionError::adapter_error)
    };
    let mut refused = |error| {
        inner.refuse(OriginalAdmissionError::Query(error));
    };
    let mut work = WorkBudget::with_owner_admission(local_ceiling, &mut sink, &mut refused);
    let result = catch_unwind(AssertUnwindSafe(|| {
        let _unwind = inner.arm_unwind(OriginalAdmissionError::OperationPanicked);
        operation(&mut work)
    }));
    match result {
        Err(payload) => {
            let first = inner.refuse(OriginalAdmissionError::OperationPanicked);
            drop(payload);
            Err(first)
        }
        Ok(Err(error)) => {
            let first = inner.refuse(OriginalAdmissionError::Query(error));
            Err(first)
        }
        Ok(Ok(value)) => {
            let final_adapter = work.charge(0);
            if let Err(error) = final_adapter {
                let first = inner.refuse(OriginalAdmissionError::Query(error));
                drop(value);
                return Err(first);
            }
            if let Err(error) = inner.admit(0, 0) {
                drop(value);
                return Err(error);
            }
            Ok(value)
        }
    }
}
