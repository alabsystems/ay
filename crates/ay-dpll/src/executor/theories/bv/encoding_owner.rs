// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original refusal latch retained through encoding cleanup.

use super::{BvSolver, Executor, Result, SolveResult, UnknownReason};

impl Executor {
    pub(super) fn bv_encoding_owner(&self) -> ay_bv::BvEncodingGuard {
        let mut scope = BvSolver::new(&self.ctx.terms);
        if let Some(flag) = self.solve_interrupt.clone() {
            scope.set_interrupt(flag);
        }
        scope.original_encoding_guard()
    }

    pub(in crate::executor) fn abort_bv_encoding(&mut self) -> Result<SolveResult> {
        // Drop the incomplete transaction, not frontend push depth.
        if let Some(state) = self.incr_bv_state.as_mut() {
            state.reset_sat_encoding_for_rebuild();
        }
        // Exact live causes keep their normal classification. A callback or
        // previous refusal alone is Incomplete, not guessed cancellation.
        if !self.should_abort_theory_loop() {
            self.publish_unknown_from_origin(UnknownReason::Incomplete.origin());
        }
        Ok(self.finalize_unknown_publication(SolveResult::Unknown))
    }
}

#[cfg(test)]
mod tests;
