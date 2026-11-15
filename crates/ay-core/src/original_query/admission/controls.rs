// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{CountedAdmissionError as Error, OriginalAdmissionError};
use crate::resource::{current_check_stop, current_guard, CheckStop, Exhausted, Guard};
use crate::time::Instant;
use std::sync::Arc;

pub(super) struct Controls {
    guard: Option<Guard>,
    callback: Option<CheckStop>,
    memory: Option<ay_sys::MemoryGroupObservation>,
}

/// Current controls are captured before arbitrary callbacks too, so removing
/// their TLS scopes inside a callback cannot erase the admission's constraints.
pub(super) struct Snapshot<'a> {
    original: &'a Controls,
    callback: Option<CheckStop>,
    guard: Option<Guard>,
    memory: Option<ay_sys::MemoryGroupObservation>,
    end: Option<Instant>,
}

impl Controls {
    pub(super) fn capture(observer: &CheckStop) -> Result<Self, Error> {
        let callback = current_check_stop().map_err(Error::CallbackCapture)?;
        Ok(Self {
            guard: current_guard(),
            callback: callback.filter(|original| !Arc::ptr_eq(original, observer)),
            memory: ay_sys::try_current_memory_group_observation()
                .map_err(|_| Error::MemoryCapture)?,
        })
    }

    pub(super) fn deadline(&self) -> Option<Instant> {
        self.guard.as_ref().and_then(Guard::effective_deadline)
    }

    pub(super) fn snapshot(&self, observer: &CheckStop) -> Result<Snapshot<'_>, Error> {
        let callback = current_check_stop().map_err(Error::CallbackCapture)?;
        let guard = current_guard();
        let end = self
            .deadline()
            .into_iter()
            .chain(guard.as_ref().and_then(Guard::effective_deadline))
            .min();
        Ok(Snapshot {
            original: self,
            callback: callback.filter(|current| {
                !Arc::ptr_eq(current, observer)
                    && !self
                        .callback
                        .as_ref()
                        .is_some_and(|original| Arc::ptr_eq(current, original))
            }),
            guard,
            memory: ay_sys::try_current_memory_group_observation()
                .map_err(|_| Error::MemoryCapture)?,
            end,
        })
    }
}

impl Snapshot<'_> {
    pub(super) fn deadline(&self) -> Option<Instant> {
        self.end
    }

    pub(super) fn observe(
        &self,
        mut continued: impl FnMut() -> Result<(), Error>,
    ) -> Result<(), Error> {
        self.poll()?;
        for callback in self.original.callback.iter().chain(self.callback.iter()) {
            // An earlier observer can refuse synchronously through a clone.
            // Do not invoke another opaque callback after that first refusal.
            continued()?;
            if callback() {
                return Err(Error::Original(OriginalAdmissionError::ObserverStopped));
            }
            self.poll()?;
        }
        continued()
    }

    /// A callback can remove its TLS scope, making this its final Arc. Its
    /// captured values have arbitrary destructors: release it WITHOUT the
    /// admission mutex, then recheck refusal and resources before any debit.
    pub(super) fn release_callback(&mut self) {
        drop(self.callback.take());
    }

    pub(super) fn poll(&self) -> Result<(), Error> {
        if self.end.is_some_and(|end| Instant::now() >= end) {
            return Err(Error::Guard(Exhausted::Deadline));
        }
        if let Some(reason) = self.original.guard.as_ref().and_then(Guard::poll) {
            return Err(Error::Guard(reason));
        }
        if let Some(reason) = self.guard.as_ref().and_then(Guard::poll) {
            return Err(Error::Guard(reason));
        }
        if crate::resource::process_cancelled() {
            return Err(Error::Guard(Exhausted::Cancelled));
        }
        if self
            .original
            .memory
            .as_ref()
            .is_some_and(|group| group.is_tripped())
            || self.memory.as_ref().is_some_and(|group| group.is_tripped())
            || ay_sys::process_memory_exceeded()
            || ay_sys::current_memory_group_soft_tripped()
        {
            return Err(Error::Memory);
        }
        Ok(())
    }

    /// Debit each independent enclosing authority once. A full child already
    /// charges its ancestor; a CancelOnly edge deliberately does not.
    pub(super) fn tick(&self, work: u64) -> Result<(), Error> {
        self.poll()?;
        match (&self.original.guard, &self.guard) {
            (Some(original), Some(current)) if current.charges_against(original) => {
                current.tick(work).map_err(Error::Guard)?;
            }
            (Some(original), Some(current)) if original.charges_against(current) => {
                original.tick(work).map_err(Error::Guard)?;
            }
            (original, current) => {
                for guard in original.iter().chain(current.iter()) {
                    guard.tick(work).map_err(Error::Guard)?;
                }
            }
        }
        self.poll()
    }
}
