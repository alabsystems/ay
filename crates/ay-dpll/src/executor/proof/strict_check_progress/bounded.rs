// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Keep a specialized proof route's existing local ceilings while composing
//! the same original caller and actual-walk Guard as the general strict route.

use super::*;

pub(in crate::executor::proof) fn check_bounded_with_executor_progress<T>(
    executor: &Executor,
    max_work: usize,
    max_bytes: usize,
    check: impl FnOnce(&mut dyn FnMut(usize, usize) -> bool) -> Result<T, ProofCheckError>,
) -> Result<T, ProofCheckError> {
    let should_stop = executor.make_strict_check_stop();
    let stopped = strided_memory_poll(&should_stop, executor.memory_limit());
    let mut meter = StrictCheckMeter::with_limits(max_work, max_bytes);
    let outcome = {
        let mut progress = |work, bytes| {
            if meter.refusal.is_some() {
                return false;
            }
            meter.charge_while_running(
                work,
                bytes,
                || stopped.poll(),
                || describe_stop_signal(executor),
                || {
                    Some(
                        stopped
                            .reason()
                            .unwrap_or_else(|| typed_stop_signal(executor)),
                    )
                },
            )
        };
        if progress(0, 0) {
            check(&mut progress)
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    };
    // Record only observations made by this walk. A completed document fact
    // must not acquire a new cancellation poll after its final checker offer.
    record_walk_stop(executor, &meter);
    meter.settle(outcome)
}

// A `#[path]` module's `mod tests;` resolves beside this file, to
// `strict_check_progress/tests.rs`: that compiled the parent's suite a second
// time here, and never this module's own.
#[cfg(test)]
#[path = "bounded/tests.rs"]
mod tests;
