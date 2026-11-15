// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The compact datatype route as the authoritative solve's first dispatch.

use super::*;

impl AdaptivePortfolio {
    /// Runs the compact datatype route on the original problem, before the
    /// ordinary worker spawn and before classification expands product
    /// datatype fields, so the route captures the original thread-local
    /// authority.
    ///
    /// An already-stopped caller is left to the ordinary pipeline, whose
    /// pre-dispatch check reports the stop; the route is never entered to end
    /// the solve as its own terminal Unknown. An outcome that ends the solve
    /// crosses the same quantifier-polarity guard and publication boundary as
    /// the ordinary pipeline's, and is attributed in the strategy trace like
    /// any direct dispatch.
    pub(super) fn try_compact_datatype_route(
        &self,
        deadline: Option<Instant>,
    ) -> Option<crate::VerifiedChcResult> {
        if self.budget_exhausted(deadline) {
            return None;
        }
        let started = Instant::now();
        let result = crate::compact_datatype_route::acceptance::run(
            &self.problem,
            deadline,
            Some(&self.cancellation_token),
            self.config.memory_budget,
        )?;
        let verified = crate::VerifiedChcResult::from_validated(
            result,
            ValidationEvidence::CounterexampleVerification,
        );
        let guarded = self.apply_quantifier_polarity_guard(verified);
        let published = self.enforce_authoritative_publication_boundary(guarded, deadline);
        self.decision_log.log_decision(DecisionEntry {
            stage: "compact_datatype_route",
            gate_result: true,
            gate_reason: "authoritative direct dispatch".to_string(),
            budget_secs: self.config.time_budget.as_secs_f64(),
            elapsed_secs: started.elapsed().as_secs_f64(),
            result: Self::verified_result_to_str(&published),
            lemmas_learned: 0,
            max_frame: 0,
        });
        Some(published)
    }
}
