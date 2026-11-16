// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::PdrSolver;
use crate::ground_derivation::compact::{Error, Owner, Result};
use crate::smt::deadline::{try_lane_cancellation, ScopedLaneCancellation};

impl PdrSolver {
    /// Number of transition clauses skipped by BV soft degradation (#5643).
    /// Non-zero means the model was not fully verified for inductiveness.
    #[cfg(test)]
    pub(crate) fn bv_soft_degradation_skips(&self) -> usize {
        self.telemetry.bv_soft_degradation_skips
    }

    /// Capture once before model traversal. The owner retains this intersection
    /// after the temporary scope leaves, and never replenishes between clauses.
    pub(super) fn structural_verification_owner(&self) -> Result<Owner<'static>> {
        // Public verify_model can run without the normal solve/replay lane.
        // Retain both configured tokens and the existing lane/interrupt before
        // the original callback can run or replace the ambient scope.
        let (ambient, interrupt) = try_lane_cancellation().map_err(|()| Error::Stopped)?;
        let mut cancellation = self.config.effective_cancellation_token();
        if let Some(ambient) = ambient {
            cancellation
                .get_or_insert_with(crate::CancellationToken::new)
                .link_upstream(&ambient);
        }
        let _lane = cancellation
            .map(|token| ScopedLaneCancellation::install(token.sticky_child(), interrupt));
        let deadline = [
            self.solve_deadline,
            self.smt.current_global_deadline(),
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min();
        let _deadline = deadline.map(crate::smt::deadline::ScopedSmtDeadline::install_until);
        Owner::capture()
    }
}

#[cfg(test)]
mod tests;
