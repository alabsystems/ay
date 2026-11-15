// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{CexDecision, CexVerificationResult, Counterexample, PdrSolver};

impl PdrSolver {
    pub(super) fn decide_compact_counterexample(&self, candidate: &Counterexample) -> CexDecision {
        let cancellation = self.config.effective_cancellation_token();
        match crate::compact_datatype_route::acceptance::confirm(
            &self.problem,
            candidate,
            crate::smt::deadline::effective_thread_deadline(),
            cancellation.as_ref(),
            self.config.memory_budget,
        ) {
            Some(confirmed) => CexDecision::Substituted(confirmed),
            None => CexDecision::Checked(CexVerificationResult::Unknown),
        }
    }
}
