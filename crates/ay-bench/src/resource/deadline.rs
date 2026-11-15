// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deadline cleanup retains the watchdog's terminal, timestamped cause.

use super::{
    monotonic_time_ns, watchdog_breached_before, BenchError, Child, ExitStatus, GroupCleanup,
    GuardedChildOutcome, Result, RssWatchdog, WatchdogOutcome,
};

/// Terminate an already-expired guarded run without discarding an earlier RSS
/// breach. The timeout trigger is observed before cleanup; a breach recorded
/// only after that trigger cannot replace the timeout as the first cause.
///
/// Always attempt both group reaping and final watchdog cleanup, even if the
/// monotonic timestamp or one cleanup operation fails. No result is admitted
/// unless those operations all succeed. Cleanup itself has bounded waits but
/// does not establish a hard process-through-reaping wall-time guarantee.
pub(crate) fn terminate_after_deadline(
    child: &mut Child,
    watchdog: RssWatchdog,
    label: &str,
) -> Result<GuardedChildOutcome> {
    let trigger = monotonic_time_ns().map_err(|error| {
        BenchError::msg(format!(
            "{label}: cannot timestamp timeout trigger: {error}"
        ))
    });
    watchdog.observe_owned_child(child, label)?;
    let cleanup = GroupCleanup::begin(child)?;
    let watchdog = watchdog.finish_after_target_cleanup();
    let status = cleanup.reap(label).map_err(Into::into);
    finish_deadline_cleanup(trigger, status, watchdog)
}

fn finish_deadline_cleanup(
    trigger: Result<u64>,
    status: Result<ExitStatus>,
    watchdog: Result<WatchdogOutcome>,
) -> Result<GuardedChildOutcome> {
    let cleanup = match (status, watchdog) {
        (Ok(status), Ok(watchdog)) => Ok((status, watchdog)),
        (Err(error), Ok(_)) => Err(error),
        (Ok(_), Err(error)) => Err(BenchError::msg(format!("watchdog cleanup failed: {error}"))),
        (Err(status), Err(watchdog)) => Err(BenchError::msg(format!(
            "{status}; watchdog cleanup failed: {watchdog}"
        ))),
    };
    match (trigger, cleanup) {
        (Ok(trigger_ns), Ok((status, watchdog))) => {
            let memout = watchdog_breached_before(watchdog, trigger_ns)?;
            Ok(GuardedChildOutcome {
                status: Some(status),
                timed_out: !memout,
                memout,
            })
        }
        (Err(error), Ok(_)) | (Ok(_), Err(error)) => Err(error),
        (Err(trigger), Err(cleanup)) => Err(BenchError::msg(format!("{trigger}; {cleanup}"))),
    }
}

#[cfg(all(test, unix))]
mod tests;
