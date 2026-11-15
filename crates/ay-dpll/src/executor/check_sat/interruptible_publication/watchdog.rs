// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{catch_unwind, Arc, AssertUnwindSafe, AtomicBool, Ordering};

pub(super) struct Watchdog<F> {
    callback: Option<F>,
    interrupt: Arc<AtomicBool>,
    done: Arc<AtomicBool>,
    #[cfg(not(target_arch = "wasm32"))]
    worker: Option<std::thread::JoinHandle<Option<F>>>,
}

impl<F: Fn() -> bool + Send + 'static> Watchdog<F> {
    pub(super) fn new(callback: F, previous: Option<Arc<AtomicBool>>) -> Self {
        // Preserve the no-worker path and its initial short-circuit behavior.
        // An initial callback panic precedes any executor control mutation.
        let interrupted = previous
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || callback();
        let mut owner = Self {
            callback: Some(callback),
            interrupt: Arc::new(AtomicBool::new(interrupted)),
            done: Arc::new(AtomicBool::new(false)),
            #[cfg(not(target_arch = "wasm32"))]
            worker: None,
        };
        // wasm has no worker; entry and final synchronous polling remain.
        #[cfg(not(target_arch = "wasm32"))]
        if !interrupted {
            if let Some(callback) = owner.callback.take() {
                let interrupt = Arc::clone(&owner.interrupt);
                let done = Arc::clone(&owner.done);
                owner.worker = Some(std::thread::spawn(move || {
                    poll(callback, previous, interrupt, done)
                }));
            }
        }
        owner
    }

    pub(super) fn finish(&mut self) {
        self.join();
        // Retain the final synchronous sample after joining: it observes a stop
        // flipped immediately before operation returned even if the worker was
        // asleep. A callback panic cannot authorize a definite result.
        if self
            .callback
            .as_ref()
            .is_some_and(|callback| catch_unwind(AssertUnwindSafe(callback)).unwrap_or(true))
        {
            self.interrupt.store(true, Ordering::Relaxed);
        }
        // A callback's owned destructor also runs inside the transaction's
        // unwind boundary, before a definite result is finalized.
        drop(self.callback.take());
    }
}

impl<F> Watchdog<F> {
    pub(super) fn interrupt(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.interrupt)
    }

    pub(super) fn join(&mut self) {
        self.done.store(true, Ordering::Relaxed);
        #[cfg(not(target_arch = "wasm32"))]
        if let Some(worker) = self.worker.take() {
            match worker.join() {
                Ok(callback) => self.callback = callback,
                Err(_) => self.interrupt.store(true, Ordering::Relaxed),
            }
        }
    }
}

impl<F> Drop for Watchdog<F> {
    fn drop(&mut self) {
        // Joining is required even when the operation or publication unwinds.
        // As with the public callback contract, this assumes callbacks return;
        // a blocking user callback cannot be forcibly terminated safely.
        self.join();
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn poll<F: Fn() -> bool>(
    callback: F,
    previous: Option<Arc<AtomicBool>>,
    interrupt: Arc<AtomicBool>,
    done: Arc<AtomicBool>,
) -> Option<F> {
    loop {
        let stopping = previous
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed));
        let sample = if stopping {
            Ok(true)
        } else {
            catch_unwind(AssertUnwindSafe(&callback))
        };
        match sample {
            Ok(true) => {
                interrupt.store(true, Ordering::Relaxed);
                break;
            }
            Err(_) => {
                // Latch *before* leaving the worker, not only when the caller
                // eventually joins: the active operation must see the stop.
                interrupt.store(true, Ordering::Relaxed);
                return None;
            }
            Ok(false) => {}
        }
        // Poll before completion, matching the original linearization rule.
        if done.load(Ordering::Relaxed) {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    Some(callback)
}
