// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The producers' renderability check, reached under this solve's stop
//! signals (DR-PROOF-RENDER-BUDGET-20261118).
//!
//! Guard 5 of every bridge lane and the congruence-explanation producer ask
//! the PRINTER whether a planned fragment renders. That check ran with no
//! work budget and no stop, and a fragment carries whole authored roots as
//! literals: on a `let`-shared root the printer wrote TREE-sized text (1e14
//! bytes on CHC-COMP 2026 `oral_messages`), and the process memout ended every
//! portfolio engine. Now each check spends at most
//! [`ay_proof::DERIVATION_RENDER_WORK_BUDGET`] of rendering work and ends on
//! the solve's interrupt, deadline or memory limit. Either ending is
//! [`ay_proof::DerivationRender::OutOfBudget`], which every caller reads as
//! "keep the `trust` leaf": nothing new is published.

use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;

use super::poll::strided_memory_poll;
use crate::executor::Executor;

/// Printer progress callbacks between two reads of the solve's stop signals.
/// The printer asks at every term boundary; one stride is a few hundred
/// bounded writes.
const RENDER_STOP_STRIDE: u32 = 256;

#[cfg(test)]
thread_local! {
    /// Renderability checks this thread has run (the conjunct lane's
    /// per-root decline memo is pinned by counting them).
    pub(in crate::executor) static RENDER_CHECKS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

impl Executor {
    /// `ay_proof::congruence_derivation_renders_within` under the per-check
    /// work budget and this solve's interrupt, deadline and memory limit.
    pub(in crate::executor) fn congruence_derivation_renders_until_stopped(
        &self,
        overrides: Option<&DetHashMap<TermId, String>>,
        derivation: &ay_proof::CongruenceDerivation,
    ) -> ay_proof::DerivationRender {
        #[cfg(test)]
        RENDER_CHECKS.with(|checks| checks.set(checks.get() + 1));
        let should_stop = self.make_strict_check_stop();
        let stopped = strided_memory_poll(&should_stop, self.memory_limit());
        let mut calls = 0u32;
        ay_proof::congruence_derivation_renders_within(
            &self.ctx.terms,
            overrides,
            derivation,
            ay_proof::DERIVATION_RENDER_WORK_BUDGET,
            &mut || {
                let first = calls == 0;
                calls = calls.wrapping_add(1) % RENDER_STOP_STRIDE;
                !(first && stopped.poll())
            },
        )
    }
}
