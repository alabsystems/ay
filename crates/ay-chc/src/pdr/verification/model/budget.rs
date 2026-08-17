// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation deadlines and per-query verification budgets.

use super::super::{PdrSolver, VERIFY_RETRY_TIMEOUT};

impl PdrSolver {
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
