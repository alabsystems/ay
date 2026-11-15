// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation deadlines and per-query verification budgets.

use super::super::{InvariantModel, PdrSolver, VERIFY_RETRY_TIMEOUT};

/// Floor of the per-rule budget for validating a `Safe` model at a public
/// boundary: the fixed value every such boundary used before the budget
/// followed the caller.
const SAFE_BOUNDARY_PER_RULE_FLOOR: std::time::Duration = std::time::Duration::from_secs(2);

/// Per-rule budget for validating a `Safe` model at a public boundary (the
/// strict final validation of direct PDR, #9227, and the proof-run boundary of
/// `solve_pdr_proof`): whatever remains until `deadline`, never below
/// [`SAFE_BOUNDARY_PER_RULE_FLOOR`] and never above [`VERIFY_RETRY_TIMEOUT`];
/// with no deadline, the latter.
///
/// Both boundaries used a fixed two seconds, which made the verdict a function
/// of machine load rather than of the budget the caller granted: a clause check
/// that takes a fraction of a second serially exceeds two seconds once the host
/// is oversubscribed, and the already-found model is then demoted to Unknown.
/// Measured on the model-checker-consumer termination VC of a `u64` `decreases` loop, given a
/// 120s budget: refused in 9 of 20 compiles under parallel load, as
/// `CandidateNotAdmitted`. A larger budget only gives the full clause check
/// more time to answer; it admits no model that check does not confirm, and
/// every query stays capped by the solve deadline.
fn safe_boundary_per_rule_budget(deadline: Option<ay_core::time::Instant>) -> std::time::Duration {
    deadline
        .map_or(VERIFY_RETRY_TIMEOUT, |deadline| {
            deadline.saturating_duration_since(ay_core::time::Instant::now())
        })
        .clamp(SAFE_BOUNDARY_PER_RULE_FLOOR, VERIFY_RETRY_TIMEOUT)
}

impl PdrSolver {
    /// Fresh-context per-rule validation of a `Safe` model at a public
    /// boundary: [`verify_model_fresh`](Self::verify_model_fresh) with the
    /// per-rule budget following the caller's `deadline`
    /// ([`safe_boundary_per_rule_budget`]) instead of a fixed two seconds.
    /// The absolute clock also constrains fresh and nested SMT contexts; a
    /// later or absent argument never renews an already admitted deadline.
    pub(crate) fn verify_model_at_safe_boundary(
        &mut self,
        model: &InvariantModel,
        deadline: Option<ay_core::time::Instant>,
    ) -> bool {
        // The per-rule floor is not fresh solve credit. Preserve every
        // enclosing clock before replacing the warm context, including for a
        // standalone verifier that has never entered solve_init().
        self.solve_deadline = [
            self.solve_deadline,
            deadline,
            self.smt.current_global_deadline(),
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min();
        // This guard replaces its thread binding, so the intersection above
        // must include the existing ambient deadline before installing it.
        let _deadline = crate::smt::ScopedSolveDeadline::new(self.solve_deadline);
        if self.is_cancelled() {
            return false;
        }
        let per_rule_budget = safe_boundary_per_rule_budget(self.solve_deadline);
        let memory = self.validation_memory();
        let _memory_scope = memory.install();
        if !memory.open() {
            return false;
        }
        let warm_smt = std::mem::take(&mut self.smt);
        self.smt.set_global_solve_deadline(self.solve_deadline);
        let result = self.verify_model_per_rule(model, per_rule_budget);
        self.smt = warm_smt;
        result && !self.is_cancelled()
    }

    /// Set the wall-clock deadline used by direct model-validation entrypoints.
    ///
    /// `solve()` normally initializes `solve_deadline` from `config.solve_timeout`
    /// in `solve_init()`. External validation APIs call verification directly, so
    /// they need to seed the same deadline state before running per-clause checks.
    pub(crate) fn set_validation_deadline(&mut self, budget: std::time::Duration) {
        let effective_budget = self
            .config
            .solve_timeout
            .map_or(budget, |solve_timeout| solve_timeout.min(budget));
        self.config.solve_timeout = Some(effective_budget);

        let requested_deadline = ay_core::time::Instant::now() + effective_budget;
        self.solve_deadline = Some(self.solve_deadline.map_or(requested_deadline, |deadline| {
            deadline.min(requested_deadline)
        }));
    }

    /// Cap a per-query SMT timeout at the remaining solve deadline (#3225).
    ///
    /// When `solve_timeout` is set, individual SMT calls should not outlast the
    /// overall solve budget. Without this, a single 30s retry timeout can run
    /// long past the solve_deadline, preventing cooperative cancellation
    /// from taking effect.
    pub(in crate::pdr::verification) fn cap_timeout(
        &self,
        requested: std::time::Duration,
    ) -> std::time::Duration {
        if let Some(deadline) = self.solve_deadline {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            requested.min(remaining)
        } else {
            requested
        }
    }

    pub(in crate::pdr::verification) fn remaining_verification_budget(
        &self,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> Option<std::time::Duration> {
        let solve_remaining = self
            .solve_deadline
            .map(|deadline| deadline.saturating_duration_since(ay_core::time::Instant::now()));
        let clause_remaining = budget_start
            .and_then(|start| budget.map(|limit| limit.saturating_sub(start.elapsed())));
        match (solve_remaining, clause_remaining) {
            (Some(solve_remaining), Some(clause_remaining)) => {
                Some(solve_remaining.min(clause_remaining))
            }
            (Some(solve_remaining), None) => Some(solve_remaining),
            (None, Some(clause_remaining)) => Some(clause_remaining),
            (None, None) => None,
        }
    }

    pub(in crate::pdr::verification) fn current_verify_retry_timeout(
        &self,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> std::time::Duration {
        let requested = match self.remaining_verification_budget(budget_start, budget) {
            Some(remaining) => {
                VERIFY_RETRY_TIMEOUT.min((remaining / 4).max(std::time::Duration::from_secs(2)))
            }
            None => VERIFY_RETRY_TIMEOUT,
        };
        self.cap_timeout(requested)
    }

    pub(in crate::pdr::verification) fn current_verify_step_timeout(
        &self,
        requested: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> std::time::Duration {
        let requested = match self.remaining_verification_budget(budget_start, budget) {
            Some(remaining) => requested.min(remaining),
            None => requested,
        };
        self.cap_timeout(requested)
    }
}

#[cfg(test)]
#[path = "budget_tests.rs"]
mod tests;
