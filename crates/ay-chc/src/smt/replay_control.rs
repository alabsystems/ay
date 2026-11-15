// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One inherited wall and sticky cancellation across nested replay solvers.
//! This scope only declines work; it never authorizes a solver verdict.

use super::deadline::{
    current_lane_token, effective_thread_deadline, lane_interrupt_flag, ScopedLaneCancellation,
    ScopedSmtDeadline,
};
use crate::CancellationToken;
use ay_core::time::Instant;
use std::{marker::PhantomData, rc::Rc};

pub(crate) struct ScopedReplayControl {
    deadline: Instant,
    cancellation: Option<CancellationToken>,
    _lane: Option<ScopedLaneCancellation>,
    _deadline: ScopedSmtDeadline,
    _thread: PhantomData<Rc<()>>,
}

impl ScopedReplayControl {
    pub(crate) fn install_until(requested: Instant, supplied: Option<&CancellationToken>) -> Self {
        let deadline = effective_thread_deadline().map_or(requested, |outer| outer.min(requested));
        let ambient = current_lane_token();
        let cancellation = match (supplied, ambient.as_ref()) {
            (Some(supplied), ambient) => {
                // Link before taking the sticky snapshot. No caller flag is
                // changed, and active descendants share this observation.
                let mut linked = supplied.child();
                if let Some(ambient) = ambient {
                    linked.link_upstream(ambient);
                }
                Some(linked.sticky_child())
            }
            (None, Some(ambient)) => Some(ambient.sticky_child()),
            (None, None) => None,
        };
        let interrupt = lane_interrupt_flag();
        // A tightening SMT scope survives nested solve-deadline replacement.
        let deadline_scope = ScopedSmtDeadline::install_until(deadline);
        let lane = cancellation
            .as_ref()
            .map(|token| ScopedLaneCancellation::install(token.clone(), interrupt));
        Self {
            deadline,
            cancellation,
            _lane: lane,
            _deadline: deadline_scope,
            _thread: PhantomData,
        }
    }

    pub(crate) fn deadline(&self) -> Instant {
        self.deadline
    }

    pub(crate) fn cancellation(&self) -> Option<&CancellationToken> {
        self.cancellation.as_ref()
    }

    pub(crate) fn open(&self) -> bool {
        !self
            .cancellation
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
            && Instant::now() < self.deadline
    }
}

#[cfg(test)]
mod tests;
