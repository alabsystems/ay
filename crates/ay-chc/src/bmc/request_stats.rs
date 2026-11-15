// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Additive request telemetry for the exact-acyclic safe-first lane only.
//!
//! One request is one SmtContext API call, not its internal backend attempts.
//! Delegated polynomial, cone, symbolic and batch lanes are not counted here.
//! These counters neither establish coverage nor authorize a solver result.

use super::{BmcSolver, SmtResult};

#[derive(Clone, Copy)]
pub(super) enum SafeFirstRequestKind {
    Decision,
    RawModelCompletion,
}

impl BmcSolver {
    /// Count immediately around the call, after query preparation. Do not hold
    /// a stats borrow through the callback, or mark an unwound call completed.
    pub(super) fn safe_first_smt_request(
        &self,
        kind: SafeFirstRequestKind,
        request: impl FnOnce() -> SmtResult,
    ) -> SmtResult {
        {
            let mut stats = self.stats.borrow_mut();
            let started = match kind {
                SafeFirstRequestKind::Decision => &mut stats.safe_first_decision_requests_started,
                SafeFirstRequestKind::RawModelCompletion => {
                    &mut stats.safe_first_raw_model_requests_started
                }
            };
            *started = started.saturating_add(1);
        }
        let result = request();
        {
            let mut stats = self.stats.borrow_mut();
            let completed = match kind {
                SafeFirstRequestKind::Decision => &mut stats.safe_first_decision_requests_completed,
                SafeFirstRequestKind::RawModelCompletion => {
                    &mut stats.safe_first_raw_model_requests_completed
                }
            };
            *completed = completed.saturating_add(1);
        }
        result
    }
}

#[cfg(test)]
mod tests;
