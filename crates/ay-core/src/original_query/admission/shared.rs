// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::controls::Controls;
use super::{AdmissionUsage, CountedAdmissionError, COUNTED_ADMISSION_USAGE_VERSION};
use super::{FiniteAdmissionGrant, OriginalAdmissionError as Error, QueryError};
use crate::original_query::StopReason;
use crate::resource::CheckStop;
use crate::time::Instant;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{Condvar, Mutex, MutexGuard};
use std::thread::{self, ThreadId};

pub(super) struct Inner {
    pub(super) end: Option<Instant>,
    observer: CheckStop,
    controls: Option<Controls>,
    granted_work: u64,
    granted_storage: usize,
    state: Mutex<State>,
    available: Condvar,
}

struct State {
    work: u64,
    copy_bytes: usize,
    first: Option<CountedAdmissionError>,
    observing: Option<ThreadId>,
    #[cfg(test)]
    waiting: usize,
}

pub(super) struct UnwindRefusal<'a> {
    inner: &'a Inner,
    error: Error,
}

impl Drop for UnwindRefusal<'_> {
    fn drop(&mut self) {
        if thread::panicking() {
            self.inner.refuse(self.error);
        }
    }
}

impl State {
    fn refuse(&mut self, error: Error) -> Error {
        self.refuse_counted(CountedAdmissionError::Original(error))
            .legacy()
    }

    fn refuse_counted(&mut self, error: CountedAdmissionError) -> CountedAdmissionError {
        *self.first.get_or_insert(error)
    }

    fn capacity(&mut self, work: usize, bytes: usize) -> Option<(u64, usize)> {
        let next_work = u64::try_from(work)
            .ok()
            .and_then(|work| self.work.checked_sub(work));
        let next_bytes = self.copy_bytes.checked_sub(bytes);
        match (next_work, next_bytes) {
            (Some(work), Some(copy_bytes)) => Some((work, copy_bytes)),
            (None, _) => {
                self.refuse_counted(CountedAdmissionError::WorkExhausted);
                None
            }
            (_, None) => {
                self.refuse_counted(CountedAdmissionError::StorageExhausted);
                None
            }
        }
    }
}

impl Inner {
    pub(super) fn new(
        grant: FiniteAdmissionGrant,
        end: Option<Instant>,
        observer: CheckStop,
        controls: Option<Controls>,
    ) -> Self {
        Self {
            end,
            observer,
            controls,
            granted_work: grant.work,
            granted_storage: grant.copy_bytes,
            state: Mutex::new(State {
                work: grant.work,
                copy_bytes: grant.copy_bytes,
                first: None,
                observing: None,
                #[cfg(test)]
                waiting: 0,
            }),
            available: Condvar::new(),
        }
    }

    fn state(&self) -> Result<MutexGuard<'_, State>, Error> {
        match self.state.lock() {
            Ok(state) => Ok(state),
            Err(poison) => {
                let mut state = poison.into_inner();
                let error = state.refuse(Error::Poisoned);
                self.available.notify_all();
                Err(error)
            }
        }
    }

    pub(super) fn refuse(&self, error: Error) -> Error {
        self.refuse_counted(CountedAdmissionError::Original(error))
            .legacy()
    }

    pub(super) fn refuse_counted(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        match self.state() {
            Ok(mut state) => {
                let first = state.refuse_counted(error);
                self.available.notify_all();
                first
            }
            Err(first) => CountedAdmissionError::Original(first),
        }
    }

    pub(super) fn remaining_work(&self) -> Result<u64, Error> {
        let state = self.state()?;
        match state.first {
            Some(error) => Err(error.legacy()),
            None => Ok(state.work),
        }
    }

    pub(super) fn usage(&self) -> Result<AdmissionUsage, Error> {
        let state = self.state()?;
        Ok(AdmissionUsage {
            version: COUNTED_ADMISSION_USAGE_VERSION,
            work_granted: self.granted_work,
            work_admitted: self.granted_work - state.work,
            work_remaining: state.work,
            storage_granted: self.granted_storage,
            storage_admitted: self.granted_storage - state.copy_bytes,
            storage_remaining: state.copy_bytes,
            refusal: state.first,
        })
    }

    pub(super) fn arm_unwind(&self, error: Error) -> UnwindRefusal<'_> {
        UnwindRefusal { inner: self, error }
    }

    #[cfg(test)]
    pub(super) fn test_balances(&self) -> (u64, usize) {
        let state = self.state.lock().expect("test bookkeeping");
        (state.work, state.copy_bytes)
    }

    #[cfg(test)]
    pub(super) fn test_poison(&self) {
        let _state = self.state.lock().expect("test bookkeeping");
        panic!("test poisoned bookkeeping");
    }

    #[cfg(test)]
    pub(super) fn test_waiters(&self) -> usize {
        self.state.lock().expect("test bookkeeping").waiting
    }

    fn begin_observation(
        &self,
        snapshot: Option<&super::controls::Snapshot<'_>>,
    ) -> Result<(), Error> {
        let current = thread::current().id();
        let wait_end = self
            .end
            .into_iter()
            .chain(snapshot.and_then(super::controls::Snapshot::deadline))
            .min();
        let mut state = self.state()?;
        loop {
            if let Some(error) = state.first {
                return Err(error.legacy());
            }
            if thread::panicking() {
                let cause = if state.observing == Some(current) {
                    Error::ObserverPanicked
                } else {
                    Error::OperationPanicked
                };
                let error = state.refuse(cause);
                self.available.notify_all();
                return Err(error);
            }
            if self.end.is_some_and(|end| Instant::now() >= end) {
                let error =
                    state.refuse(Error::Query(QueryError::Interrupted(StopReason::Deadline)));
                self.available.notify_all();
                return Err(error);
            }
            if let Some(snapshot) = snapshot {
                // Only trusted Guard/memory reads run while locked. A later
                // caller's real end must also bound waiting for an observer;
                // no user callback is invoked concurrently or under this lock.
                if let Err(error) = snapshot.poll() {
                    let first = state.refuse_counted(error).legacy();
                    self.available.notify_all();
                    return Err(first);
                }
            }
            match state.observing {
                None => {
                    state.observing = Some(current);
                    return Ok(());
                }
                Some(owner) if owner == current => {
                    let error = state.refuse(Error::Reentrant);
                    self.available.notify_all();
                    return Err(error);
                }
                Some(_) => {
                    // No observer runs under this guard. Waiters release it;
                    // their duration is derived from the SAME original end.
                    #[cfg(test)]
                    {
                        state.waiting += 1;
                    }
                    let waited = match wait_end {
                        Some(end) => self
                            .available
                            .wait_timeout(state, end.saturating_duration_since(Instant::now()))
                            .map(|(state, _)| state)
                            .map_err(|poison| poison.into_inner().0),
                        None => self
                            .available
                            .wait(state)
                            .map_err(|poison| poison.into_inner()),
                    };
                    state = match waited {
                        Ok(state) => {
                            #[cfg(test)]
                            let mut state = state;
                            #[cfg(test)]
                            {
                                state.waiting -= 1;
                            }
                            state
                        }
                        Err(mut state) => {
                            #[cfg(test)]
                            {
                                state.waiting -= 1;
                            }
                            let error = state.refuse(Error::Poisoned);
                            self.available.notify_all();
                            return Err(error);
                        }
                    };
                }
            }
        }
    }

    pub(super) fn admit(&self, work: usize, bytes: usize) -> Result<(), Error> {
        // Capture the caller BEFORE waiting too. A preceding observer cannot
        // hide a later caller's deadline or replace its retained callback.
        let mut snapshot = self
            .controls
            .as_ref()
            .map(|controls| controls.snapshot(&self.observer))
            .transpose()
            .map_err(|error| self.refuse_counted(error).legacy())?;
        self.begin_observation(snapshot.as_ref())?;
        let observed = catch_unwind(AssertUnwindSafe(|| {
            let _unwind = self.arm_unwind(Error::ObserverPanicked);
            let result = self.observe(snapshot.as_ref());
            if let Err(error) = result {
                // Preserve the actual first observation before opaque callback
                // cleanup can recursively refuse with a different cause.
                self.refuse_counted(error);
            }
            if let Some(snapshot) = &mut snapshot {
                snapshot.release_callback();
            }
            result?;
            self.remaining_work()
                .map_err(CountedAdmissionError::Original)?;
            if let Some(snapshot) = &snapshot {
                snapshot.poll()?;
            }
            Ok(snapshot)
        }));
        // Callback recursion/panic does not run under the state lock. Both the
        // debit and publication poll recheck the first refusal and absolute end.
        let mut state = self.state()?;
        if state.first.is_none() {
            match observed {
                Err(payload) => {
                    state.refuse(Error::ObserverPanicked);
                    // Refusal is recorded BEFORE an opaque payload is dropped.
                    // Release bookkeeping before any user-owned destructor.
                    state.observing = None;
                    self.available.notify_all();
                    drop(state);
                    drop(payload);
                    return Err(self.refuse(Error::ObserverPanicked));
                }
                Ok(Err(error)) => {
                    state.refuse_counted(error);
                }
                Ok(Ok(_)) if self.end.is_some_and(|end| Instant::now() >= end) => {
                    state.refuse(Error::Query(QueryError::Interrupted(StopReason::Deadline)));
                }
                Ok(Ok(snapshot)) => {
                    if let Some((next_work, next_bytes)) = state.capacity(work, bytes) {
                        let debit = state.work - next_work;
                        let tick = snapshot
                            .as_ref()
                            .map_or(Ok(()), |snapshot| snapshot.tick(debit));
                        match tick {
                            Ok(()) => {
                                state.work = next_work;
                                state.copy_bytes = next_bytes;
                            }
                            Err(error) => {
                                state.refuse_counted(error);
                            }
                        }
                    }
                }
            }
        }
        state.observing = None;
        self.available.notify_all();
        match state.first {
            Some(error) => Err(error.legacy()),
            None => Ok(()),
        }
    }

    fn observe(
        &self,
        snapshot: Option<&super::controls::Snapshot<'_>>,
    ) -> Result<(), CountedAdmissionError> {
        if let Some(snapshot) = snapshot {
            snapshot.poll()?;
        }
        if (self.observer)() {
            return Err(CountedAdmissionError::Original(Error::ObserverStopped));
        }
        if let Some(snapshot) = snapshot {
            snapshot.observe(|| {
                self.remaining_work()
                    .map(|_| ())
                    .map_err(CountedAdmissionError::Original)
            })?;
        }
        Ok(())
    }
}
