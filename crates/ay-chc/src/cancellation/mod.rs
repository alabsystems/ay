// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative cancellation for CHC solvers
//!
//! This module provides a cancellation token that allows portfolio solving to
//! stop losing engines early when a winner is found. The token is thread-safe
//! and can be shared across multiple engine threads.
//!
//! # Usage
//!
//! ```rust,no_run
//! use ay_chc::CancellationToken;
//!
//! // Create a token (portfolio solver)
//! let token = CancellationToken::new();
//!
//! // Share with engines
//! let engine_token = token.clone();
//!
//! // In engine main loop
//! if engine_token.is_cancelled() {
//!     // Return early from solver
//! }
//!
//! // When winner found (portfolio)
//! token.cancel();
//! ```

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

/// A thread-safe cancellation token for cooperative engine cancellation.
///
/// Engines check this token periodically in their main loops and return early
/// if cancellation is requested. This allows portfolio solving to stop losing
/// engines promptly when a winner is found.
#[derive(Debug, Clone)]
pub struct CancellationToken {
    cancelled: Arc<AtomicBool>,
    /// Upstream cancellation flags this token OBSERVES but never sets.
    ///
    /// Populated by [`CancellationToken::child`] and
    /// [`CancellationToken::link_upstream`]. A token reports cancelled when
    /// either its own flag or any upstream flag is set. This lets a scheduler
    /// hand each lane a per-lane token (whose `cancel_after` budget timer
    /// cancels only that lane) while an embedding driver's cancel request on
    /// the shared parent still propagates into every lane. Usually empty, so
    /// `is_cancelled` stays a single atomic load in the common case.
    upstream: Vec<Arc<AtomicBool>>,
}

impl Default for CancellationToken {
    fn default() -> Self {
        Self::new()
    }
}

impl CancellationToken {
    /// Create a new cancellation token in the non-cancelled state.
    pub fn new() -> Self {
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
            upstream: Vec::new(),
        }
    }

    /// Check if cancellation has been requested.
    ///
    /// This is a cheap atomic load operation and can be called frequently
    /// in main loops without significant overhead. Returns true when either
    /// this token's own flag or any linked upstream (parent) flag is set.
    #[inline]
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Relaxed)
            || self
                .upstream
                .iter()
                .any(|flag| flag.load(Ordering::Relaxed))
    }

    /// Request cancellation. All clones of this token will see the request.
    ///
    /// This operation is idempotent - calling it multiple times has no
    /// additional effect. Only this token's own flag is set: linked upstream
    /// (parent) tokens are never cancelled by a child.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    /// Reset the token to non-cancelled state.
    ///
    /// This is useful for reusing tokens across multiple solving attempts.
    /// Only this token's own flag is reset; a cancelled upstream (parent)
    /// flag cannot be cleared from a child.
    pub fn reset(&self) {
        self.cancelled.store(false, Ordering::Relaxed);
    }

    /// Create a child token linked to this one.
    ///
    /// The child starts non-cancelled and observes this token (and all of its
    /// upstream links): cancelling the parent cancels the child, but
    /// cancelling or resetting the child never affects the parent. This is
    /// the building block for cooperative external cancellation of the
    /// adaptive portfolio (wishlist item 5): each lane's budget timer runs
    /// `cancel_after` on its own child token without poisoning the shared
    /// parent handle, while an embedding driver's `cancel()` on the parent
    /// reaches every lane.
    pub fn child(&self) -> Self {
        let mut upstream = self.upstream.clone();
        upstream.push(Arc::clone(&self.cancelled));
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
            upstream,
        }
    }

    /// Link an existing token so it additionally observes `parent`.
    ///
    /// After linking, `is_cancelled` on THIS instance (and clones made from
    /// it afterwards) also returns true when `parent` is cancelled. Clones
    /// made BEFORE the link do not see the new upstream flags, so link before
    /// handing the token to a solver. Self-links and duplicate links are
    /// ignored.
    pub fn link_upstream(&mut self, parent: &CancellationToken) {
        for flag in std::iter::once(&parent.cancelled).chain(parent.upstream.iter()) {
            if !Arc::ptr_eq(&self.cancelled, flag)
                && !self.upstream.iter().any(|f| Arc::ptr_eq(f, flag))
            {
                self.upstream.push(Arc::clone(flag));
            }
        }
    }

    /// Schedule cancellation after a timeout duration, returning a guard that
    /// stops the timer thread when dropped.
    ///
    /// This replaces the anti-pattern of `thread::spawn(|| { sleep(d); token.cancel(); })`
    /// which wastes a thread sleeping for the full duration even when the solver
    /// finishes early. The returned [`CancellationGuard`] uses a `Condvar` to
    /// wake the timer thread immediately on drop.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use ay_chc::CancellationToken;
    /// use std::time::Duration;
    ///
    /// let token = CancellationToken::new();
    /// let _guard = token.cancel_after(Duration::from_secs(10));
    /// // ... run solver with token ...
    /// // When _guard is dropped (solver finished), the timer thread exits
    /// // immediately instead of sleeping for the remaining duration.
    /// ```
    pub fn cancel_after(&self, timeout: Duration) -> CancellationGuard {
        let stop = Arc::new((Mutex::new(false), Condvar::new()));
        let stop_clone = Arc::clone(&stop);
        let token = self.clone();
        let handle = std::thread::spawn(move || {
            let (lock, cvar) = &*stop_clone;
            let guard = lock.lock().expect("cancellation timer mutex poisoned");
            // Wait until either the timeout expires or we're told to stop.
            let (guard, _timeout_result) = cvar
                .wait_timeout_while(guard, timeout, |stopped| !*stopped)
                .expect("cancellation timer condvar wait failed");
            // Only cancel the token if we weren't stopped early (i.e., the
            // timeout actually expired).
            if !*guard {
                token.cancel();
            }
        });
        CancellationGuard {
            stop,
            handle: Some(handle),
        }
    }
}

/// Guard returned by [`CancellationToken::cancel_after`].
///
/// When dropped, signals the timer thread to exit immediately and joins it.
/// This ensures no timer threads are left sleeping after the solver finishes.
pub struct CancellationGuard {
    stop: Arc<(Mutex<bool>, Condvar)>,
    handle: Option<std::thread::JoinHandle<()>>,
}

impl Drop for CancellationGuard {
    fn drop(&mut self) {
        let (lock, cvar) = &*self.stop;
        if let Ok(mut stopped) = lock.lock() {
            *stopped = true;
            cvar.notify_one();
        }
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
