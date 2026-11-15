// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SIGTERM in a solve's start-up window.
//!
//! The solve's SIGTERM contract is cooperative: `unknown` on stdout, exit 124
//! (`ay help exit-codes`). Its handler is installed once the run knows it is a
//! solve, and the supervising wrapper installs its own reaper; before either,
//! the default disposition killed the process with no verdict. Measured:
//! SIGTERM 20 ms after start ended 7 of 16 runs with exit -15 (or 143 from the
//! wrapper) and an empty stdout.
//!
//! [`hold_sigterm`] blocks SIGTERM before the kernel-governance re-exec (the
//! mask survives `exec`, and that re-exec keeps the pid), and
//! [`arm_early_sigterm_answer`] installs the start-up answer in the final
//! image before unblocking it, so a SIGTERM from the first instruction on is
//! either pending or answered. The answer stands down once a real handler owns
//! the signal ([`hand_over_sigterm`]; signal-hook chains to a handler it finds
//! installed, which then does nothing), or gives the signal back to the
//! default disposition for a subcommand that is not a solve
//! ([`terminate_by_default_on_sigterm`]). A solve child the re-exec
//! supervisor spawns starts with SIGTERM already blocked
//! ([`start_child_with_sigterm_held`]), so a SIGTERM the supervisor forwards
//! during the child's start-up is answered by the child, once.
//!
//! One window stays open and cannot be closed from inside the binary: a
//! SIGTERM delivered after `exec` but before the first statement of `main`
//! (the dynamic loader and the runtime's start-up, 0-3 ms on the 2026-10
//! measurements) meets the default disposition, and the process dies of
//! SIGTERM with no output. Only a launcher that starts the process with
//! SIGTERM blocked closes it, as the re-exec supervisor does for its child.

use std::sync::atomic::{AtomicU8, Ordering};

/// Answer `unknown` and exit 124.
const ANSWER: u8 = 0;
/// Another registered handler owns SIGTERM; do nothing.
const HANDED_OVER: u8 = 1;

static STATE: AtomicU8 = AtomicU8::new(ANSWER);

const UNKNOWN_LINE: &[u8] = b"unknown\n";
const EXIT_TIMEOUT: libc::c_int = 124;

fn mask_sigterm(how: libc::c_int) {
    // SAFETY: `sigset_t` is POD; `sigemptyset`/`sigaddset` fill an owned stack
    // local with a valid signal number, and `pthread_sigmask` reads it (a null
    // old-mask pointer is allowed). Only the calling thread's mask changes.
    unsafe {
        let mut set: libc::sigset_t = std::mem::zeroed();
        libc::sigemptyset(&raw mut set);
        libc::sigaddset(&raw mut set, libc::SIGTERM);
        libc::pthread_sigmask(how, &raw const set, std::ptr::null_mut());
    }
}

/// Block SIGTERM. The first statement of `main`, before the governance
/// re-exec: allocation-free and thread-free.
pub fn hold_sigterm() {
    mask_sigterm(libc::SIG_BLOCK);
}

/// Install the start-up answer, then unblock SIGTERM (a SIGTERM held since
/// [`hold_sigterm`] is delivered now). Call right after the governance
/// re-exec, before any thread exists, so every later thread inherits the
/// unblocked mask. If the handler cannot be installed, the default
/// disposition stays, as before.
pub fn arm_early_sigterm_answer() {
    let handler: extern "C" fn(libc::c_int) = early_sigterm_action;
    // SAFETY: `sigaction` is POD and zeroed is a valid empty value;
    // `sigemptyset` fills its owned mask, and `sigaction(2)` reads the owned
    // local. The installed handler is async-signal-safe (see there).
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = handler as libc::sighandler_t;
        action.sa_flags = libc::SA_RESTART;
        libc::sigemptyset(&raw mut action.sa_mask);
        libc::sigaction(libc::SIGTERM, &raw const action, std::ptr::null_mut());
    }
    mask_sigterm(libc::SIG_UNBLOCK);
}

/// The start-up SIGTERM action: an atomic load, then `write(2)` of static
/// bytes and `_exit(2)`, all async-signal-safe.
extern "C" fn early_sigterm_action(_signal: libc::c_int) {
    if STATE.load(Ordering::SeqCst) != ANSWER {
        return;
    }
    // SAFETY: fd 1 and a static buffer of exactly the given length; `_exit`
    // runs no handler or destructor and is async-signal-safe.
    unsafe {
        libc::write(1, UNKNOWN_LINE.as_ptr().cast(), UNKNOWN_LINE.len());
        libc::_exit(EXIT_TIMEOUT);
    }
}

/// A registered handler (the solve's cooperative one, the wrapper's reaper,
/// the PB monitor) now owns SIGTERM.
pub fn hand_over_sigterm() {
    STATE.store(HANDED_OVER, Ordering::SeqCst);
}

/// The forked solve child answers again until its own handler is installed:
/// it inherits the wrapper's hand-over, whose reaper does not run in it.
pub fn answer_until_handed_over() {
    STATE.store(ANSWER, Ordering::SeqCst);
}

/// Start a spawned child with SIGTERM blocked, so the child's own
/// [`arm_early_sigterm_answer`] owns a SIGTERM from its first instruction.
///
/// `hold_sigterm` cannot do this for a child the re-exec supervisor spawns:
/// `std::process::Command` empties the child's signal mask between `fork`
/// and `exec`, so a SIGTERM the supervisor forwards while the child is still
/// starting up hit the default disposition and the child died with no
/// answer (measured: exit 143, empty stdout, 7 of 10 runs at 12 ms). The
/// mask survives `exec`; the child's `arm_early_sigterm_answer` unblocks it.
///
/// `std` runs `pre_exec` callbacks after it resets the mask, so this block
/// is the one the new image starts with. Registering a callback also keeps
/// `std` off its `posix_spawn` path, which would reset the mask itself;
/// `spawn` then returns only once the `exec` has happened.
pub fn start_child_with_sigterm_held(command: &mut std::process::Command) {
    use std::os::unix::process::CommandExt as _;

    // SAFETY: `pre_exec` is unsafe because only async-signal-safe operations
    // are permitted between fork and exec. The closure captures nothing and
    // calls only `sigemptyset`, `sigaddset` and `sigprocmask`, all
    // async-signal-safe, on an owned stack local (zeroed is a valid
    // `sigset_t`); it allocates nothing, takes no lock, touches no shared
    // Rust state and never fails the spawn.
    unsafe {
        command.pre_exec(|| {
            let mut set: libc::sigset_t = std::mem::zeroed();
            libc::sigemptyset(&raw mut set);
            libc::sigaddset(&raw mut set, libc::SIGTERM);
            // `sigprocmask` cannot fail with a valid `how` and set; the spawn
            // never depends on it.
            libc::sigprocmask(libc::SIG_BLOCK, &raw const set, std::ptr::null_mut());
            Ok(())
        });
    }
}

/// A subcommand that is not a solve keeps the default SIGTERM termination,
/// never a verdict line on its stdout. Call before any other SIGTERM handler
/// is registered (it restores the default disposition outright).
pub fn terminate_by_default_on_sigterm() {
    STATE.store(HANDED_OVER, Ordering::SeqCst);
    // SAFETY: `signal(2)` with a valid signal number and `SIG_DFL` has no
    // memory preconditions.
    unsafe {
        libc::signal(libc::SIGTERM, libc::SIG_DFL);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A handed-over answer does nothing; the start state answers.
    #[test]
    fn the_answer_stands_down_once_handed_over() {
        assert_eq!(STATE.load(Ordering::SeqCst), ANSWER);
        hand_over_sigterm();
        // With the state handed over the action returns without exiting.
        early_sigterm_action(libc::SIGTERM);
        answer_until_handed_over();
        assert_eq!(STATE.load(Ordering::SeqCst), ANSWER);
    }
}
