// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One cumulative native-lineage owner per external decision query. Internal
//! restarts, consumers, roots, instances and rejected offers never renew it.

// Same work envelope as existing proof-surgery planning, restricted to this
// optional native producer. Exhaustion declines production, not the query.
const WORK: usize = 32 * 1024 * 1024;
const BYTES: usize = 32 * 1024 * 1024;

pub(in crate::executor) struct NativeUniversalBudget {
    work: usize,
    bytes: usize,
    refused: bool,
    offers_started: bool,
    refutation_started: bool,
    controls: Option<(
        ay_core::resource::Guard,
        crate::executor::solve_deadline::DeadlinePoll,
    )>,
}

impl Default for NativeUniversalBudget {
    fn default() -> Self {
        Self {
            work: 0,
            bytes: 0,
            refused: true,
            offers_started: false,
            refutation_started: false,
            controls: None,
        }
    }
}

impl NativeUniversalBudget {
    pub(in crate::executor) fn begin_external_query(&mut self) {
        *self = Self {
            work: WORK,
            bytes: BYTES,
            refused: false,
            offers_started: false,
            refutation_started: false,
            controls: None,
        };
    }

    pub(super) fn claim_source_offers(&mut self) -> Option<()> {
        if self.refused || self.offers_started {
            return None;
        }
        self.offers_started = true;
        Some(())
    }

    /// One proof-only attempt, charged to the same external query ledger as
    /// all working offers. Retries do not remint witnesses or renew work.
    pub(super) fn claim_source_refutation(&mut self) -> Option<()> {
        if self.refused || self.refutation_started {
            return None;
        }
        self.refutation_started = true;
        Some(())
    }

    pub(super) fn needs_controls(&self) -> bool {
        !self.refused && self.controls.is_none()
    }

    pub(super) fn bind_controls(
        &mut self,
        guard: ay_core::resource::Guard,
        deadline: crate::executor::solve_deadline::DeadlinePoll,
    ) {
        self.controls = Some((guard, deadline));
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize, stopped: bool) -> Option<()> {
        if self.refused
            || stopped
            || self
                .controls
                .as_ref()
                .is_some_and(|(guard, deadline)| guard.cancelled().is_some() || deadline.expired())
        {
            self.refused = true;
            return None;
        }
        let Some(work) = self.work.checked_sub(work.max(1)) else {
            self.refused = true;
            return None;
        };
        self.work = work;
        let Some(bytes) = self.bytes.checked_sub(bytes) else {
            self.refused = true;
            return None;
        };
        self.bytes = bytes;
        Some(())
    }
}
