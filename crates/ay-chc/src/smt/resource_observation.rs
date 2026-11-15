// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attempt-local observation, not a resource grant or solver authority.
//! Refusals remain recorded after reset/drop. No observer means no new state.

use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ResourceRefusal {
    Cancelled,
    Timeout,
    Memory,
}

thread_local! {
    static CURRENT: RefCell<Option<Rc<Cell<Option<ResourceRefusal>>>>> =
        const { RefCell::new(None) };
}

pub(crate) struct ScopedResourceObservation {
    observed: Rc<Cell<Option<ResourceRefusal>>>,
    previous: Option<Rc<Cell<Option<ResourceRefusal>>>>,
}

impl ScopedResourceObservation {
    pub(crate) fn install() -> Self {
        // Nested original checks share this owner; only a fresh outer attempt
        // creates an empty latch. Restoring a scope cannot erase child refusal.
        let observed = CURRENT
            .with(|cell| cell.borrow().clone())
            .unwrap_or_else(|| Rc::new(Cell::new(None)));
        let previous = CURRENT.with(|cell| cell.replace(Some(observed.clone())));
        Self { observed, previous }
    }

    pub(crate) fn first(&self) -> Option<ResourceRefusal> {
        self.observed.get()
    }

    pub(crate) fn note(&self, reason: ResourceRefusal) {
        if self.observed.get().is_none() {
            self.observed.set(Some(reason));
        }
    }
}

impl Drop for ScopedResourceObservation {
    fn drop(&mut self) {
        let previous = self.previous.take();
        let _ = CURRENT.try_with(|cell| {
            if let Ok(mut current) = cell.try_borrow_mut() {
                *current = previous;
            }
        });
    }
}

/// Read the already-observed cause without resetting or transferring TLS.
pub(crate) fn current_refusal() -> Result<Option<ResourceRefusal>, ()> {
    CURRENT
        .try_with(|cell| {
            cell.try_borrow()
                .map(|current| current.as_ref().and_then(|observed| observed.get()))
                .map_err(|_| ())
        })
        .map_err(|_| ())?
}

fn note_current(reason: ResourceRefusal) {
    let _ = CURRENT.try_with(|cell| {
        if let Ok(current) = cell.try_borrow() {
            if let Some(observed) = current.as_ref() {
                if observed.get().is_none() {
                    observed.set(Some(reason));
                }
            }
        }
    });
}

pub(crate) fn note_memory_refusal(exceeded: bool) {
    if exceeded {
        note_current(ResourceRefusal::Memory);
    }
}

pub(crate) fn note_executor_refusal(reason: Option<ay_dpll::UnknownReason>) {
    match reason {
        Some(ay_dpll::UnknownReason::MemoryLimit) => note_current(ResourceRefusal::Memory),
        Some(ay_dpll::UnknownReason::Interrupted) if original_cancellation_observed() => {
            note_current(ResourceRefusal::Cancelled)
        }
        _ => {}
    }
}

fn original_cancellation_observed() -> bool {
    // InterruptObserver's private flag also stops on internal panic/poison/join
    // failure. Interrupted alone therefore is NOT original caller cancellation.
    crate::smt::deadline::current_lane_token().is_some_and(|token| token.is_cancelled())
        || crate::smt::deadline::lane_interrupt_flag()
            .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
}

#[cfg(test)]
mod capture_tests {
    use super::*;

    #[test]
    fn a_borrowed_original_refusal_refuses_owner_capture() {
        let mut original = ay_core::resource::ResourceGuard::new();
        original.set_deadline(Some(
            ay_core::time::Instant::now() + std::time::Duration::from_secs(20),
        ));
        CURRENT.with(|cell| {
            let _borrowed = cell.borrow_mut();
            assert!(current_refusal().is_err());
            let owner = crate::engines::ExternalInvariantValidationOwner::capture(
                &original,
                &crate::PdrConfig::production(false),
            );
            assert_eq!(
                owner.check(),
                Some(crate::engines::ExternalInvariantValidation::Inconclusive)
            );
        });
        assert!(current_refusal().is_ok());
    }
}

#[cfg(test)]
mod tests;
