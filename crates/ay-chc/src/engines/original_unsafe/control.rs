// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One original clock/stop owner; the short BMC phase never renews that grant.
//! Memory ownership is the existing per-context term limit, not process RSS.

use super::super::ambient_cancellation::Ambient;
use crate::bmc::memory::Budget;
use crate::{CancellationToken, PdrConfig};
use ay_core::time::Instant;
use std::time::Duration;

pub(super) struct Owner {
    deadline: Option<Instant>,
    cancellation: Option<CancellationToken>,
    external: Option<CancellationToken>,
    ambient: Ambient,
    memory: Budget,
    probe: Option<Instant>,
    stopped: bool,
}

impl Owner {
    pub(super) fn capture(config: &PdrConfig, deadline: Option<Instant>) -> Self {
        let ambient = Ambient::capture();
        let mut cancellation = config
            .cancellation_token
            .as_ref()
            .map(CancellationToken::sticky_child);
        let mut external = config
            .external_cancellation_token
            .as_ref()
            .map(CancellationToken::sticky_child);
        ambient.link_into(&mut cancellation);
        ambient.link_into(&mut external);
        if let Some(external) = &external {
            if let Some(cancellation) = &mut cancellation {
                cancellation.link_upstream(external);
            } else {
                cancellation = Some(external.clone());
            }
        }
        Self {
            deadline: [
                deadline,
                crate::smt::current_thread_solve_deadline(),
                crate::smt::deadline::current_smt_deadline(),
            ]
            .into_iter()
            .flatten()
            .min(),
            cancellation,
            external,
            ambient,
            memory: Budget::capture(config.memory_budget, None),
            probe: None,
            stopped: false,
        }
    }

    pub(super) fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    pub(super) fn memory(&self) -> Budget {
        self.memory
    }

    pub(super) fn install_lane(&self) -> Option<crate::smt::deadline::ScopedLaneCancellation> {
        self.ambient.install()
    }

    pub(super) fn open(&mut self) -> bool {
        self.open_at(Instant::now())
    }

    fn open_at(&mut self, now: Instant) -> bool {
        self.stopped |= self.deadline.is_some_and(|deadline| now >= deadline)
            || self
                .cancellation
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            || crate::smt::deadline::lane_cancelled()
            || self.ambient.is_cancelled()
            || !self.memory.open()
            || !Budget::capture(None, None).open();
        !self.stopped
    }

    pub(super) fn probe_deadline(&mut self) -> Option<Instant> {
        self.probe_deadline_at(Instant::now())
    }

    fn probe_deadline_at(&mut self, now: Instant) -> Option<Instant> {
        if !self.open_at(now) {
            return None;
        }
        let original = self.deadline?;
        // Same quarter/4s reserve convention as the existing array prepass.
        // Cache once: repeated requests cannot restart a spent phase.
        Some(*self.probe.get_or_insert_with(|| {
            let budget = (original.saturating_duration_since(now) / 4).min(Duration::from_secs(4));
            original.min(now + budget)
        }))
    }

    pub(super) fn configured(&self, base: &PdrConfig) -> PdrConfig {
        let mut configured = base.clone();
        // The BMC helper and strict validator consume the primary channel.
        // Both original channels remain linked there, while local search
        // cancellation does not cancel the caller or poison ordinary fallback.
        configured.cancellation_token = self.cancellation.as_ref().map(CancellationToken::child);
        configured.external_cancellation_token =
            self.external.as_ref().map(CancellationToken::child);
        configured
    }
}

#[cfg(test)]
mod tests;
