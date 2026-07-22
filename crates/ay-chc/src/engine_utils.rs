// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared utility helpers for CHC engines.

use crate::engine_config::ChcEngineConfig;
use crate::smt::{SmtContext, SmtResult};
use crate::ChcExpr;
use ay_core::time::Instant;
use std::time::Duration;

/// Run a single SMT satisfiability query with a timeout.
#[inline]
pub(crate) fn check_sat_with_timeout(constraint: &ChcExpr, timeout: Duration) -> SmtResult {
    let mut smt = SmtContext::new();
    smt.check_sat_with_timeout(constraint, timeout)
}

/// Returns true when engine execution should stop due to cancellation or timeout.
#[inline]
pub(crate) fn search_budget_exhausted(
    base_config: &ChcEngineConfig,
    start: Instant,
    total_timeout: Duration,
) -> bool {
    base_config.is_cancelled() || start.elapsed() >= total_timeout
}
