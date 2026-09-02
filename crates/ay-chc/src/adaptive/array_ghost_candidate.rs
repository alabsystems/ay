// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded query-anchored candidate attempt for the array ghost-pair route.

use super::*;
use crate::transform::{try_query_anchored_and_seal, GhostPairSpec};

const ATTEMPT_FRACTION: f64 = 0.75;
const SYNTHESIS_FRACTION: f64 = 0.60;

pub(super) enum CandidateAttempt {
    Miss,
    Stop,
    Sealed((PortfolioResult, ValidationEvidence)),
}

impl AdaptivePortfolio {
    pub(super) fn try_query_anchored_ghost_candidate(
        &self,
        raw_ghost_problem: &ChcProblem,
        spec: &GhostPairSpec,
        n: usize,
        lane_budget: Duration,
        route_deadline: Instant,
        route_start: Instant,
        route_budget: Duration,
    ) -> CandidateAttempt {
        let now = Instant::now();
        let available = lane_budget.min(route_deadline.saturating_duration_since(now));
        let attempt_budget = available.mul_f64(ATTEMPT_FRACTION);
        if attempt_budget < ARRAY_GHOST_PAIR_ROUTE_MIN_BUDGET {
            return CandidateAttempt::Miss;
        }
        let attempt_deadline = now + attempt_budget;
        let synthesis_deadline = now + attempt_budget.mul_f64(SYNTHESIS_FRACTION);
        let should_stop = || {
            self.cancellation_token.is_cancelled()
                || Instant::now() >= attempt_deadline
                || Instant::now() >= route_deadline
                || crate::smt::SmtContext::new().exact_term_memory_exceeded()
        };
        if let Some(sealed) = try_query_anchored_and_seal(
            &self.problem,
            raw_ghost_problem,
            spec,
            synthesis_deadline,
            attempt_deadline,
            &self.cancellation_token,
            self.config.memory_budget,
        ) {
            if should_stop() {
                return CandidateAttempt::Stop;
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "array_ghost_pairs",
                gate_result: true,
                gate_reason: format!(
                    "n={n}; raw query-anchored joint Houdini sealed on original clauses; \
                     {} candidates -> {} survivors in {} rounds/{} SMT calls",
                    sealed.candidates, sealed.survivors, sealed.rounds, sealed.smt_calls
                ),
                budget_secs: route_budget.as_secs_f64(),
                elapsed_secs: route_start.elapsed().as_secs_f64(),
                result: "safe",
                lemmas_learned: sealed.survivors,
                max_frame: 0,
            });
            let mut certified_model = InvariantModel::new();
            certified_model.set_ghost_pair_certificate(sealed.certificate);
            let result = (
                PortfolioResult::Safe(certified_model),
                ValidationEvidence::QuantifiedArrayInvariantCertificate,
            );
            return if should_stop() {
                CandidateAttempt::Stop
            } else {
                CandidateAttempt::Sealed(result)
            };
        }
        if should_stop() {
            CandidateAttempt::Stop
        } else {
            CandidateAttempt::Miss
        }
    }
}
