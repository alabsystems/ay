// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Keep the batch's original cancellation token alive across its replay phase.

use super::{CancellationToken, Duration, QueryProofReplay};

/// This dispatch seam neither creates evidence nor changes a solve outcome.
/// The production callback is the report's fail-closed checked-replay method;
/// tests inject phase work without launching a solver or racing a timer.
pub(super) fn checked_replay_if_requested<T>(
    report: T,
    replay: QueryProofReplay,
    cancellation: Option<&CancellationToken>,
    run_replay: impl FnOnce(T, Duration, &mut dyn FnMut() -> bool) -> T,
) -> T {
    let QueryProofReplay::Checked(budget) = replay else {
        return report;
    };
    // Preserve the existing stage-boundary no-op when replay has not started.
    if cancellation.is_some_and(CancellationToken::is_cancelled) {
        return report;
    }
    let mut stopped = false;
    let mut progress = || {
        if stopped || cancellation.is_some_and(CancellationToken::is_cancelled) {
            stopped = true;
            false
        } else {
            true
        }
    };
    run_replay(report, budget, &mut progress)
}

#[cfg(test)]
mod tests;
