// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One remaining wall-clock grant for the existing two safety checkers.

use ay::chc::{engines, ChcProblem, InvariantModel, PdrConfig};
use ay_core::time::Instant;
use std::time::Duration;

pub(super) fn discharges_with_clock(
    problem: &ChcProblem,
    model: &InvariantModel,
    timeout_ms: u64,
    start: Option<Instant>,
    clock: impl FnMut() -> Instant,
) -> bool {
    check_with_clock(
        timeout_ms,
        start,
        clock,
        |remaining| {
            let mut config = PdrConfig::default().with_strict_proofs(true);
            config.solve_timeout = Some(remaining);
            // Preserve the existing query/safety checker, not a new full
            // inductiveness pass. Only its positive discharge can accept.
            matches!(
                engines::external_invariant_model_excludes_error(problem, model, &config),
                Ok(true)
            )
        },
        |deadline| {
            // Preserve the same cata-aware obligations and 1500ms per-query
            // cap, but never renew the first checker's wall-clock grant.
            engines::cata_composed_model_excludes_error(
                problem,
                model,
                Duration::from_millis(1500),
                Some(deadline),
            )
        },
    )
}

fn shared_deadline(timeout_ms: u64, start: Option<Instant>, now: Instant) -> Option<Instant> {
    let cap = Duration::from_secs(10);
    let remaining = if timeout_ms == 0 {
        cap
    } else {
        // An active global timeout without its origin cannot justify a new
        // grant. Normal CLI initialization always installs both together.
        let elapsed = now.checked_duration_since(start?)?;
        Duration::from_millis(timeout_ms)
            .saturating_sub(elapsed)
            .min(cap)
    };
    if remaining.is_zero() {
        return None;
    }
    now.checked_add(remaining)
}

fn check_with_clock(
    timeout_ms: u64,
    start: Option<Instant>,
    mut clock: impl FnMut() -> Instant,
    first: impl FnOnce(Duration) -> bool,
    fallback: impl FnOnce(Instant) -> bool,
) -> bool {
    let Some(deadline) = shared_deadline(timeout_ms, start, clock()) else {
        return false;
    };
    let remaining = deadline.saturating_duration_since(clock());
    if remaining.is_zero() {
        return false;
    }
    let discharged = first(remaining);
    if clock() >= deadline {
        return false;
    }
    if discharged {
        return true;
    }
    // The checker APIs contain opaque intervals. Pre/post guards prevent an
    // overrun from granting authority; they are not a hard latency guarantee.
    if clock() >= deadline {
        return false;
    }
    let discharged = fallback(deadline);
    clock() < deadline && discharged
}

#[cfg(test)]
mod tests;
