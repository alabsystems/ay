// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::controls::Controls;
use super::{shared, AdmissionUsage, CountedAdmissionError, FiniteAdmissionGrant, QueryError};
use super::{OriginalAdmissionError, WorkBudget};
use crate::resource::CheckStop;
use crate::time::Instant;
use std::sync::Arc;

/// One counted invocation, optionally interrupted by a genuine external end.
///
/// This shares the compatibility owner's ledger implementation, not a second
/// allowance. Clones, direct admissions and scoped adapters retain one first
/// refusal and both balances. No default clock, timer, reset or refund exists.
/// Work units are defined by the caller; this owner does not instrument a solve.
#[derive(Clone)]
pub struct CountedAdmission {
    inner: Arc<shared::Inner>,
}

/// Opaque: the shared ledger is not printed, so `Debug` (which callers and
/// tests need for `Result::unwrap` on a refused attach) reveals no balance.
impl std::fmt::Debug for CountedAdmission {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CountedAdmission").finish_non_exhaustive()
    }
}

impl CountedAdmission {
    /// Move the caller's grants into an owner and capture ambient controls
    /// before invoking any observer. `None` does not invent a wall-clock end.
    /// An original Guard's effective deadline only tightens an explicit end.
    /// Other domain-specific deadlines must be supplied by the integration.
    pub fn new(
        grant: FiniteAdmissionGrant,
        end: Option<Instant>,
        observer: CheckStop,
    ) -> Result<Self, CountedAdmissionError> {
        let controls = Controls::capture(&observer)?;
        let end = end.into_iter().chain(controls.deadline()).min();
        Ok(Self {
            inner: Arc::new(shared::Inner::new(grant, end, observer, Some(controls))),
        })
    }

    /// Whether both handles retain the exact same invocation ledger.
    ///
    /// This only compares ownership identity; it does not poll, admit work,
    /// renew a grant or authorize a result. Equal balances alone are not enough.
    pub fn shares_ledger_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    /// The original effective end, without polling or extending live controls.
    pub fn deadline(&self) -> Option<Instant> {
        self.inner.end
    }

    /// Admit before doing work or allocating. Zero only polls; callers must
    /// positively charge even a trivial decision before publishing it.
    pub fn admit(&self, work: usize, storage: usize) -> Result<(), CountedAdmissionError> {
        self.inner
            .admit(work, storage)
            .map_err(|error| self.error(error))
    }

    /// Poll the same owner without admitting work or authorizing a decision.
    pub fn check(&self) -> Result<(), CountedAdmissionError> {
        self.admit(0, 0)
    }

    /// Same original ledger, with the existing post-scratch-cleanup fence.
    /// Any later returned data disposal remains the caller's responsibility.
    pub fn with_work<T>(
        &self,
        operation: impl FnOnce(&mut WorkBudget<'_>) -> Result<T, QueryError>,
    ) -> Result<T, CountedAdmissionError> {
        super::with_work(&self.inner, operation).map_err(|error| self.error(error))
    }

    /// Latch checked-size/allocation failure or another precise terminal cause.
    /// An earlier refusal always wins, including on all retained clones.
    pub fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        self.inner.refuse_counted(error)
    }

    /// Read the shared receipt without polling callbacks or authorizing work.
    pub fn usage(&self) -> Result<AdmissionUsage, CountedAdmissionError> {
        self.inner.usage().map_err(CountedAdmissionError::Original)
    }

    #[cfg(test)]
    pub(super) fn test_waiters(&self) -> usize {
        self.inner.test_waiters()
    }

    fn error(&self, fallback: OriginalAdmissionError) -> CountedAdmissionError {
        match self.usage() {
            Ok(usage) => usage
                .refusal
                .unwrap_or(CountedAdmissionError::Original(fallback)),
            Err(error) => error,
        }
    }
}

#[cfg(test)]
mod identity_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn ledger_identity_distinguishes_equal_grants_without_polling_or_renewal() {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(10, 20),
            None,
            Arc::new(move || {
                observed.fetch_add(1, Ordering::SeqCst);
                false
            }),
        )
        .unwrap();
        let clone = owner.clone();
        let other =
            CountedAdmission::new(FiniteAdmissionGrant::new(10, 20), None, Arc::new(|| false))
                .unwrap();
        let receipt = owner.usage().unwrap();
        assert!(owner.shares_ledger_with(&clone));
        assert!(!owner.shares_ledger_with(&other));
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(owner.usage().unwrap(), receipt);
        owner.refuse(CountedAdmissionError::WorkExhausted);
        let refused = owner.usage().unwrap();
        assert!(clone.shares_ledger_with(&owner));
        assert_eq!(clone.usage().unwrap(), refused);
        assert_eq!(calls.load(Ordering::SeqCst), 0);
    }
}
