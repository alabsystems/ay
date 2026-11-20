// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SIGTERM that waits for a block of output to be written whole.
//!
//! A run that writes its answer as blocks (an `o`/`v` incumbent of
//! `ay lp solve`) and is stopped by SIGTERM must not leave a cut-off last
//! block: the reader takes the last block as the answer. With the default
//! disposition a SIGTERM that arrives between two `write(2)` calls of one
//! block (a block larger than the pipe buffer is several) ends the process
//! there.
//!
//! [`install`] replaces the default action with one that terminates at once
//! when no block is being written and otherwise marks the signal pending;
//! the [`BlockGuard`] that [`begin_block`] returns terminates on drop if a
//! SIGTERM came while it was held. Termination restores the default
//! disposition and re-raises SIGTERM, so the process still ends by SIGTERM,
//! as before.

use std::sync::atomic::{AtomicU8, Ordering};

/// No block is being written.
const IDLE: u8 = 0;
/// A block is being written.
const WRITING: u8 = 1;
/// A block is being written and a SIGTERM came meanwhile.
const PENDING: u8 = 2;
/// The process is terminating; no block may start.
const TERMINATING: u8 = 3;

static STATE: AtomicU8 = AtomicU8::new(IDLE);

/// What the SIGTERM action does in the current state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OnSignal {
    /// Terminate now.
    Terminate,
    /// A block is being written; terminate when it is done.
    Defer,
}

/// The state change of a SIGTERM (async-signal-safe: atomics only).
fn on_signal() -> OnSignal {
    loop {
        match STATE.load(Ordering::SeqCst) {
            IDLE | TERMINATING => {
                STATE.store(TERMINATING, Ordering::SeqCst);
                return OnSignal::Terminate;
            }
            WRITING => {
                if STATE
                    .compare_exchange(WRITING, PENDING, Ordering::SeqCst, Ordering::SeqCst)
                    .is_ok()
                {
                    return OnSignal::Defer;
                }
            }
            _ => return OnSignal::Defer,
        }
    }
}

/// Restore the default disposition and re-raise SIGTERM: the process ends
/// by SIGTERM. In the handler the signal is blocked until it returns, so it
/// is delivered then; elsewhere at once.
fn terminate() {
    // SAFETY: `signal(2)` with a valid signal number and `SIG_DFL`, and
    // `raise(3)` with a valid signal number, have no memory preconditions
    // and are async-signal-safe.
    unsafe {
        libc::signal(libc::SIGTERM, libc::SIG_DFL);
        libc::raise(libc::SIGTERM);
    }
}

extern "C" fn sigterm_action(_signal: libc::c_int) {
    if on_signal() == OnSignal::Terminate {
        terminate();
    }
}

/// Install the deferring SIGTERM action for this process. Call once, before
/// the first block; it replaces whatever action SIGTERM had.
pub fn install() {
    let handler: extern "C" fn(libc::c_int) = sigterm_action;
    // SAFETY: `sigaction` is POD and zeroed is a valid empty value;
    // `sigemptyset` fills its owned mask, and `sigaction(2)` reads the owned
    // local. The installed handler is async-signal-safe (atomics, then
    // `signal` and `raise`). SA_RESTART restarts a `write(2)` it interrupts.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = handler as libc::sighandler_t;
        action.sa_flags = libc::SA_RESTART;
        libc::sigemptyset(&raw mut action.sa_mask);
        libc::sigaction(libc::SIGTERM, &raw const action, std::ptr::null_mut());
    }
}

/// Held while one block is written; see the module docs.
#[must_use = "the block is protected only while the guard lives"]
pub struct BlockGuard {
    _private: (),
}

/// Start writing a block. A SIGTERM from now until the guard drops ends the
/// process after the drop. If the process is already terminating this does
/// not return (the pending SIGTERM ends it), so no block starts after a
/// SIGTERM was acted on.
pub fn begin_block() -> BlockGuard {
    loop {
        match STATE.compare_exchange(IDLE, WRITING, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => return BlockGuard { _private: () },
            Err(TERMINATING) => {
                terminate();
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            // Another thread is writing a block; blocks do not interleave.
            Err(_) => std::thread::yield_now(),
        }
    }
}

impl Drop for BlockGuard {
    fn drop(&mut self) {
        if STATE
            .compare_exchange(WRITING, IDLE, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            // PENDING: a SIGTERM came during the block, which is now whole.
            STATE.store(TERMINATING, Ordering::SeqCst);
            terminate();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The state machine: a signal outside a block terminates at once, one
    /// inside a block is deferred to the guard's drop. (The drop itself would
    /// end the test process, so the pending state is checked and reset.)
    #[test]
    fn a_signal_inside_a_block_is_deferred() {
        STATE.store(IDLE, Ordering::SeqCst);
        let guard = begin_block();
        assert_eq!(STATE.load(Ordering::SeqCst), WRITING);
        assert_eq!(on_signal(), OnSignal::Defer);
        assert_eq!(STATE.load(Ordering::SeqCst), PENDING);
        assert_eq!(on_signal(), OnSignal::Defer);
        std::mem::forget(guard);
        STATE.store(IDLE, Ordering::SeqCst);
        assert_eq!(on_signal(), OnSignal::Terminate);
        STATE.store(IDLE, Ordering::SeqCst);
        drop(begin_block());
        assert_eq!(STATE.load(Ordering::SeqCst), IDLE);
    }
}
