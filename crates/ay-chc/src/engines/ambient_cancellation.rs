// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attempt-local observation; no upstream or interrupt flag is written.
//! Descendants must be obtained through the installed lane or linked config;
//! an unrelated observer's cancel/reset pulse is not retained by this owner.

use crate::smt::deadline::ScopedLaneCancellation;
use crate::CancellationToken;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

pub(super) struct Ambient {
    token: Option<CancellationToken>,
    interrupt: Option<Arc<AtomicBool>>,
}

impl Ambient {
    pub(super) fn capture() -> Self {
        Self {
            token: crate::smt::deadline::current_lane_token()
                .as_ref()
                .map(CancellationToken::sticky_child),
            // Keep the existing caller-owned interrupt identity, not the new
            // child's flag. Bare interrupt users retain their prior semantics.
            interrupt: crate::smt::deadline::lane_interrupt_flag(),
        }
    }

    pub(super) fn link_into(&self, target: &mut Option<CancellationToken>) {
        if let (Some(target), Some(ambient)) = (target, &self.token) {
            target.link_upstream(ambient);
        }
        // None remains None: primary presence affects search policy.
    }

    pub(super) fn install(&self) -> Option<ScopedLaneCancellation> {
        self.token
            .as_ref()
            .map(|token| ScopedLaneCancellation::install(token.clone(), self.interrupt.clone()))
    }

    pub(super) fn is_cancelled(&self) -> bool {
        self.token
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
    }
}

#[cfg(test)]
pub(super) mod support;
