// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One original IC3 refusal owner, not a solver verdict or new allowance.

use crate::bmc::memory::Budget;
use crate::engines::ExternalInvariantValidation;
use crate::smt::replay_control::ScopedReplayControl;
use crate::smt::resource_observation::ResourceRefusal;
use crate::{CancellationToken, ChcResult, PdrConfig};
use ay_core::resource::ResourceGuard;
use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Ready,
    Calling,
    Stopped,
}

pub(super) struct Resources {
    guard: ResourceGuard,
    deadline: Instant,
    cancellation: Option<CancellationToken>,
    interrupt: Option<Arc<AtomicBool>>,
    memory: Budget,
    group: Option<ay_sys::MemoryGroupObservation>,
    state: AtomicU8,
}

impl Resources {
    pub(super) fn capture(
        guard: &ResourceGuard,
        config: &PdrConfig,
        replay: &ScopedReplayControl,
    ) -> Self {
        Self {
            guard: guard.clone(),
            deadline: guard
                .effective_deadline()
                .map_or(replay.deadline(), |d| d.min(replay.deadline())),
            cancellation: replay.cancellation().cloned(),
            interrupt: crate::smt::deadline::lane_interrupt_flag(),
            memory: Budget::capture(config.memory_budget(), None),
            group: ay_sys::current_memory_group_observation(),
            state: AtomicU8::new(State::Ready as u8),
        }
    }

    pub(super) fn install_memory(&self) -> impl Drop {
        self.memory.install()
    }

    pub(super) fn poll(&self) -> bool {
        // Pre-latching survives callback panic and reentry. Never write an
        // upstream cancel/interrupt flag or replenish the original ticks.
        if self
            .state
            .compare_exchange(
                State::Ready as u8,
                State::Calling as u8,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_err()
        {
            self.state.store(State::Stopped as u8, Ordering::Release);
            return false;
        }
        if Instant::now() >= self.deadline
            || self
                .cancellation
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            || self
                .interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || self
                .group
                .as_ref()
                .is_some_and(ay_sys::MemoryGroupObservation::is_tripped)
            || self.guard.tick(1).is_err()
            || self.guard.should_stop()
            || ay_core::resource::check_stop_requested()
            || !self.memory.open()
            || Instant::now() >= self.deadline
        {
            self.state.store(State::Stopped as u8, Ordering::Release);
            return false;
        }
        if self
            .state
            .compare_exchange(
                State::Calling as u8,
                State::Ready as u8,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_err()
        {
            self.state.store(State::Stopped as u8, Ordering::Release);
            false
        } else {
            true
        }
    }

    pub(super) fn validation_config(&self, deadline: Instant) -> PdrConfig {
        let mut config = PdrConfig::production(false)
            .with_memory_budget(self.memory.term_limit())
            .with_cancellation_token(self.cancellation.clone());
        config.solve_timeout = Some(
            deadline
                .min(self.deadline)
                .saturating_duration_since(Instant::now()),
        );
        config
    }

    pub(super) fn observe_validation(
        &self,
        observed: Option<ResourceRefusal>,
        result: &ChcResult<ExternalInvariantValidation>,
    ) {
        // A genuine memory/caller cancellation survives validator reset/drop,
        // including Err. Local Timeout must not poison a later reserved rung.
        if matches!(
            observed,
            Some(ResourceRefusal::Memory | ResourceRefusal::Cancelled)
        ) || matches!(
            result,
            Ok(ExternalInvariantValidation::Memory | ExternalInvariantValidation::Cancelled)
        ) {
            self.state.store(State::Stopped as u8, Ordering::Release);
        }
    }
}

#[cfg(test)]
mod tests;
