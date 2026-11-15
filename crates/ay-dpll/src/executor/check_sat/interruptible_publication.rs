// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Panic-safe ownership of one solve/publication watchdog transaction.

use super::{Executor, Instant, Result, SolveResult};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod watchdog;
use watchdog::Watchdog;

/// Restore both walls independently: a nested search slice may legitimately
/// have a tighter deadline than the surrounding certification transaction.
struct InstalledControls<'a, C> {
    context: &'a mut C,
    executor_of: fn(&mut C) -> &mut Executor,
    interrupt: Option<Arc<AtomicBool>>,
    search_deadline: Option<Instant>,
    certification_deadline: Option<Instant>,
    restored: bool,
}

impl<'a, C> InstalledControls<'a, C> {
    fn new(
        context: &'a mut C,
        executor_of: fn(&mut C) -> &mut Executor,
        interrupt: Arc<AtomicBool>,
    ) -> Self {
        let executor = executor_of(context);
        let previous = Self {
            interrupt: executor.solve_interrupt.replace(interrupt),
            search_deadline: executor.solve_deadline.get(),
            certification_deadline: executor.certification_deadline.get(),
            restored: false,
            context,
            executor_of,
        };
        // No new relative timeout and no replacement of the certification wall
        // with a possibly narrower search wall.
        previous
    }

    fn restore(&mut self) {
        if self.restored {
            return;
        }
        let executor = (self.executor_of)(&mut *self.context);
        executor.solve_interrupt = self.interrupt.take();
        executor.solve_deadline.set(self.search_deadline);
        executor
            .certification_deadline
            .set(self.certification_deadline);
        self.restored = true;
    }
}

impl<C> Drop for InstalledControls<'_, C> {
    fn drop(&mut self) {
        self.restore();
    }
}

fn cleanup_during_unwind(cleanup: impl FnOnce()) {
    if let Err(secondary) = catch_unwind(AssertUnwindSafe(cleanup)) {
        // Only a secondary cleanup panic is discarded: dropping its arbitrary
        // payload could itself panic and replace the original unwind. Leaking
        // that payload is intentional here, with no bounded-byte claim. Normal
        // operation/finalization panics are never discarded by this helper.
        std::mem::forget(secondary);
    }
}

pub(super) fn run<F, G>(
    executor: &mut Executor,
    should_stop: F,
    operation: G,
) -> Result<SolveResult>
where
    F: Fn() -> bool + Send + 'static,
    G: FnOnce(&mut Executor) -> Result<SolveResult>,
{
    run_with_context(
        executor,
        |executor| executor,
        should_stop,
        operation,
        |executor, result| match result {
            Ok(proposed) => Ok(executor.decline_definite_publication_on_external_stop(proposed)),
            Err(error) => match executor.finalize_external_stop_for_publication() {
                Some(unknown) => Ok(unknown),
                None => Err(error),
            },
        },
    )
}

/// Own the callback through the context's complete publication operation.
/// Native APIs include capability consumption in `operation`; `finalize`
/// makes a final deny-only check after callback sampling and destruction.
pub(crate) fn run_with_context<C, F, G, H, O, R>(
    context: &mut C,
    executor_of: fn(&mut C) -> &mut Executor,
    should_stop: F,
    operation: G,
    finalize: H,
) -> R
where
    F: Fn() -> bool + Send + 'static,
    G: FnOnce(&mut C) -> O,
    H: FnOnce(&mut C, O) -> R,
{
    let mut watchdog = Watchdog::new(should_stop, executor_of(context).solve_interrupt.clone());
    let mut controls = InstalledControls::new(context, executor_of, watchdog.interrupt());
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let result = operation(&mut *controls.context);
        watchdog.finish();
        // Callback cleanup may itself raise the enclosing interrupt flag.
        // Retain that source as well as the watchdog's latched local stop.
        if controls
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            watchdog.interrupt().store(true, Ordering::Relaxed);
        }
        finalize(&mut *controls.context, result)
    }));
    match outcome {
        Ok(result) => result,
        Err(payload) => {
            // Stop and join before resuming the original panic. Restore the
            // controls before invoking lifecycle diagnostics during cleanup.
            // Revocation uses the same lifecycle as assertion mutation,
            // so no partial model, proof, core or certificate remains current.
            // Diagnostic/destructor cleanup must not replace the original panic.
            cleanup_during_unwind(|| watchdog.join());
            controls.restore();
            // Keep callback ownership outside the revocation catch: a panic in
            // lifecycle diagnostics must not drop a panicking F while unwinding.
            cleanup_during_unwind(|| {
                (controls.executor_of)(&mut *controls.context).invalidate_last_check_result();
            });
            cleanup_during_unwind(|| drop(watchdog));
            drop(controls);
            resume_unwind(payload)
        }
    }
}

#[cfg(test)]
mod tests;
