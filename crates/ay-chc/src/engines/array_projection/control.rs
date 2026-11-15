// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One caller-owned clock and stop state across projection, search and landing.
//! The captured memory scope bounds SMT term stores, not projection buffers or
//! process RSS. Polls around opaque cloning/cleanup are not a latency guarantee.

use super::super::ambient_cancellation::Ambient;
use crate::bmc::memory::Budget;
use crate::{CancellationToken, PdrConfig};
use ay_core::time::Instant;
use std::time::Duration;

pub(in crate::engines) struct Owner {
    deadline: Option<Instant>,
    primary: Option<CancellationToken>,
    external: Option<CancellationToken>,
    ambient: Ambient,
    memory: Budget,
    probe: Option<Instant>,
    stopped: bool,
}

impl Owner {
    pub(in crate::engines) fn capture(config: &PdrConfig, deadline: Option<Instant>) -> Self {
        let ambient = Ambient::capture();
        let mut primary = config
            .cancellation_token
            .as_ref()
            .map(CancellationToken::sticky_child);
        let mut external = config
            .external_cancellation_token
            .as_ref()
            .map(CancellationToken::sticky_child);
        ambient.link_into(&mut primary);
        ambient.link_into(&mut external);
        Self {
            deadline: [
                deadline,
                crate::smt::current_thread_solve_deadline(),
                crate::smt::deadline::current_smt_deadline(),
            ]
            .into_iter()
            .flatten()
            .min(),
            primary,
            external,
            ambient,
            memory: Budget::capture(config.memory_budget, None),
            probe: None,
            stopped: false,
        }
    }

    pub(in crate::engines) fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    pub(in crate::engines) fn memory(&self) -> Budget {
        self.memory
    }

    pub(in crate::engines) fn install_lane(
        &self,
    ) -> Option<crate::smt::deadline::ScopedLaneCancellation> {
        self.ambient.install()
    }

    pub(in crate::engines) fn open(&mut self) -> bool {
        self.open_at(Instant::now())
    }

    fn open_at(&mut self, now: Instant) -> bool {
        // Do not consult the current effective SMT deadline here: during the
        // speculative search it can be the shorter probe clock. Its expiry
        // permits fallback, whereas an observed original stop is terminal.
        self.stopped |= self.deadline.is_some_and(|deadline| now >= deadline)
            || self
                .primary
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            || self
                .external
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            || crate::smt::deadline::lane_cancelled()
            || self.ambient.is_cancelled()
            || !self.memory.open()
            || !Budget::capture(None, None).open();
        !self.stopped
    }

    pub(in crate::engines) fn probe_deadline(&mut self) -> Option<Instant> {
        self.probe_deadline_at(Instant::now())
    }

    fn probe_deadline_at(&mut self, now: Instant) -> Option<Instant> {
        if !self.open_at(now) {
            return None;
        }
        let original = self.deadline?;
        // The array probe in adaptive_multi_pred uses the same quarter/4s
        // convention to reserve downstream time. This optional strict prepass
        // does not start without a finite caller clock or renew a spent slice.
        let probe = *self.probe.get_or_insert_with(|| {
            let slice = (original.saturating_duration_since(now) / 4).min(Duration::from_secs(4));
            original.min(now + slice)
        });
        Some(probe)
    }

    pub(in crate::engines) fn search_config(&self, base: &PdrConfig, probe: Instant) -> PdrConfig {
        let mut configured = base.clone();
        let deadline = [self.deadline, self.probe]
            .into_iter()
            .flatten()
            .fold(probe, |earliest, clock| earliest.min(clock));
        let remaining = deadline.saturating_duration_since(Instant::now());
        configured.solve_timeout = Some(
            base.solve_timeout
                .map_or(remaining, |old| old.min(remaining)),
        );
        // Keep the channel positions: primary presence changes PDR's bounded
        // search/case-split policy, while external presence does not. Children
        // share the caller observations but local probe cancellation stays local.
        configured.cancellation_token = self.primary.as_ref().map(CancellationToken::child);
        configured.external_cancellation_token =
            self.external.as_ref().map(CancellationToken::child);
        configured
    }

    pub(in crate::engines) fn validation_config(&self, base: &PdrConfig) -> PdrConfig {
        let mut configured = base.clone();
        let mut primary = self.primary.as_ref().map(CancellationToken::child);
        if let Some(external) = &self.external {
            if let Some(primary) = &mut primary {
                primary.link_upstream(external);
            } else {
                primary = Some(external.child());
            }
        }
        // The unchanged original-model validator copies only the primary
        // channel. Link both there without changing the projected search policy.
        configured.cancellation_token = primary;
        configured.external_cancellation_token =
            self.external.as_ref().map(CancellationToken::child);
        configured
    }
}

#[cfg(test)]
mod tests;
