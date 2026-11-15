// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain the enclosing proof assembly's authority; never grant a new budget.

use crate::api::proofs::EnvelopeStop;
use crate::executor::proof::exact_authored_bv_refutation::control::Continuation;
use crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourceWorkEnvelope;
use crate::executor::Executor;
use ay_core::resource::{Exhausted, Guard};

pub(super) struct Control<'a> {
    stop: &'a dyn Fn() -> bool,
    continuation: Continuation,
    guard: Option<Guard>,
    refused: bool,
}

impl<'a> Control<'a> {
    pub(super) fn capture(executor: &Executor, stop: &'a dyn Fn() -> bool) -> Option<Self> {
        Some(Self {
            stop,
            continuation: Continuation::capture(executor),
            guard: ay_core::resource::current_guard(),
            refused: false,
        })
    }

    pub(super) fn enter(&self) -> ay_core::resource::CheckStopScope {
        self.continuation.enter()
    }

    pub(super) fn stopped(&self) -> bool {
        self.refused || self.continuation.stopped()
    }

    pub(super) fn reason(&self) -> Option<EnvelopeStop> {
        self.continuation.reason()
    }

    pub(super) fn admit(
        &mut self,
        work: &ProofSourceWorkEnvelope,
        visits: usize,
        bytes: usize,
    ) -> Option<()> {
        if self.refused || self.continuation.stopped() {
            return self.refuse();
        }
        // Pre-arm before arbitrary callbacks, so unwinding cannot resume work.
        self.refused = true;
        let current = ay_core::resource::current_guard();
        if (self.stop)() || ay_core::resource::check_stop_requested() {
            self.continuation.refuse(EnvelopeStop::Caller);
            return None;
        }
        // Logical traversal and copied representation work, not a claim of
        // CPU-instruction accounting for the pre-existing native interner.
        let units = visits.checked_add(bytes).or_else(|| self.refuse())?;
        if !work.spend_canonical_scan_work(units) {
            return self.refuse();
        }
        let cost = u64::try_from(units).ok().or_else(|| self.refuse())?;
        let result = match (&self.guard, &current) {
            (Some(original), Some(current)) if current.charges_against(original) => {
                current.tick(cost)
            }
            (Some(original), Some(current)) => original.tick(cost).and_then(|()| {
                if !original.charges_against(current) {
                    current.tick(cost)
                } else {
                    Ok(())
                }
            }),
            (Some(guard), None) | (None, Some(guard)) => guard.tick(cost),
            (None, None) => Ok(()),
        };
        if let Some(reason) = result
            .err()
            .or_else(|| self.guard.as_ref().and_then(Guard::poll))
            .or_else(|| current.as_ref().and_then(Guard::poll))
        {
            self.continuation.refuse(match reason {
                Exhausted::Cancelled => EnvelopeStop::Interrupt,
                Exhausted::Deadline | Exhausted::Cpu => EnvelopeStop::Backstop,
                Exhausted::Rlimit => EnvelopeStop::WorkLimit,
                Exhausted::Memory => EnvelopeStop::LaneShare,
            });
            return None;
        }
        self.refused = false;
        Some(())
    }

    pub(super) fn refuse<T>(&mut self) -> Option<T> {
        self.refused = true;
        self.continuation.refuse(EnvelopeStop::WorkLimit);
        None
    }
}

impl Drop for Control<'_> {
    fn drop(&mut self) {
        if self.refused {
            self.continuation.refuse(EnvelopeStop::Caller);
        }
    }
}
