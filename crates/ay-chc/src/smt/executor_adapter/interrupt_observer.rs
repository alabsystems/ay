// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attempt-local cancellation bridge for ordinary Executor execution.
//!
//! Only owned token state is read on the worker. Caller progress callbacks stay
//! on the caller thread. Polling, scheduling and opaque solver phases do not
//! establish a hard cancellation latency bound.

use super::ReplayCancellation;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Condvar, Mutex,
};
use std::thread::JoinHandle;
use std::time::Duration;

#[derive(Debug, thiserror::Error)]
pub(crate) enum ObserverStartError {
    #[error("could not start executor interrupt observer: {0}")]
    Spawn(#[from] std::io::Error),
}

struct State {
    stopped: Mutex<bool>,
    wake: Condvar,
    interrupted: Arc<AtomicBool>,
}

pub(crate) struct InterruptObserver {
    cancellation: ReplayCancellation,
    state: Arc<State>,
    worker: Option<JoinHandle<()>>,
}

impl InterruptObserver {
    pub(crate) fn new(cancellation: &ReplayCancellation) -> Result<Self, ObserverStartError> {
        Self::with_spawner(cancellation, |worker| {
            std::thread::Builder::new()
                .name("ay-chc-interrupt".into())
                .spawn(move || worker.run_with(Worker::observe))
        })
    }

    fn with_spawner(
        cancellation: &ReplayCancellation,
        spawn: impl FnOnce(Worker) -> std::io::Result<JoinHandle<()>>,
    ) -> Result<Self, ObserverStartError> {
        let mut owner = Self {
            cancellation: cancellation.clone(),
            state: Arc::new(State {
                stopped: Mutex::new(false),
                wake: Condvar::new(),
                interrupted: Arc::new(AtomicBool::new(cancellation.is_cancelled())),
            }),
            worker: None,
        };
        if !owner.state.interrupted.load(Ordering::Relaxed) {
            let worker = Worker {
                cancellation: owner.cancellation.clone(),
                state: Arc::clone(&owner.state),
            };
            match spawn(worker) {
                Ok(handle) => owner.worker = Some(handle),
                Err(error) => {
                    owner.state.interrupted.store(true, Ordering::Relaxed);
                    return Err(error.into());
                }
            }
        }
        Ok(owner)
    }

    pub(crate) fn interrupt(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.state.interrupted)
    }

    pub(crate) fn finish(&mut self) -> bool {
        self.stop_and_join();
        // Sample the entire sticky attempt once more after the joined worker
        // boundary. Never clear the local flag or any caller/parent token.
        if self.cancellation.is_cancelled() {
            self.state.interrupted.store(true, Ordering::Relaxed);
        }
        !self.state.interrupted.load(Ordering::Relaxed)
    }

    fn stop_and_join(&mut self) {
        {
            let mut stopped = match self.state.stopped.lock() {
                Ok(stopped) => stopped,
                Err(poisoned) => {
                    self.state.interrupted.store(true, Ordering::Relaxed);
                    poisoned.into_inner()
                }
            };
            *stopped = true;
        }
        // Never join while retaining the lock the worker needs to exit.
        self.state.wake.notify_all();
        if let Some(worker) = self.worker.take() {
            if let Err(payload) = worker.join() {
                self.state.interrupted.store(true, Ordering::Relaxed);
                // A worker panic is a failed observer, not permission to keep
                // solving. Disposal must also remain safe during caller unwind.
                if let Err(secondary) = catch_unwind(AssertUnwindSafe(|| drop(payload))) {
                    // Only this secondary destructor-panic payload is leaked;
                    // dropping it could double-panic. No bounded-byte claim.
                    std::mem::forget(secondary);
                }
            }
        }
    }
}

impl Drop for InterruptObserver {
    fn drop(&mut self) {
        self.stop_and_join();
    }
}

struct Worker {
    cancellation: ReplayCancellation,
    state: Arc<State>,
}

/// Atomic-only unwind backstop: a worker panic must stop the *active* executor,
/// rather than first becoming visible after the executor returns and joins.
struct PanicInterrupt<'a> {
    interrupted: &'a AtomicBool,
    completed: bool,
}

impl Drop for PanicInterrupt<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.interrupted.store(true, Ordering::Relaxed);
        }
    }
}

impl Worker {
    fn run_with(self, operation: impl FnOnce(&Self)) {
        let mut guard = PanicInterrupt {
            interrupted: &self.state.interrupted,
            completed: false,
        };
        // The production operation is always observe; the private seam lets
        // lifecycle tests force a worker panic without unsafe or caller code.
        operation(&self);
        guard.completed = true;
    }

    fn observe(&self) {
        loop {
            if self.cancellation.is_cancelled() {
                self.state.interrupted.store(true, Ordering::Relaxed);
                return;
            }
            let stopped = match self.state.stopped.lock() {
                Ok(stopped) => stopped,
                Err(_) => {
                    self.state.interrupted.store(true, Ordering::Relaxed);
                    return;
                }
            };
            if *stopped {
                return;
            }
            // Drop notifies this Condvar, so normal/unwind cleanup never waits
            // for an entire polling period. Spurious wakes simply resample.
            if self
                .state
                .wake
                .wait_timeout(stopped, Duration::from_millis(1))
                .is_err()
            {
                self.state.interrupted.store(true, Ordering::Relaxed);
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests;
