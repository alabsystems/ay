// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fork-before-threads solve-supervisor primitives (unix).
//!
//! The `ay` binary isolates every solve behind a supervisor process that converts
//! a solver-child crash / OOM / hang into a sound `unknown` instead of a lost
//! answer. Historically the supervisor re-`exec`'d the full binary as a child,
//! paying process startup (dyld) twice; fork-before-threads replaces that second
//! `exec` with a `fork()` taken while the process is provably single-threaded, so
//! the child shares the already-linked image via copy-on-write.
//!
//! `fork`, `waitpid`, `pthread_sigmask` and `pthread_is_threaded_np` are all FFI
//! (unsafe), and the `ay` crate is `#![forbid(unsafe_code)]`, so the raw calls live
//! here — the workspace's single unsafe-permitting crate — behind safe wrappers.
//! The soundness-critical ORCHESTRATION (observe wait-status, classify a fatal
//! signal into `unknown`, reap orphans) stays in `ay`; this module only provides
//! the mechanical syscalls.

#![cfg(unix)]

/// True iff the process currently has ONLY its main thread — the precondition for
/// the textbook-safe `fork()` the solve supervisor uses (no other thread can be
/// mid-mutation of an async-signal-unsafe lock the child would inherit and deadlock
/// on). macOS uses the libSystem `pthread_is_threaded_np` predicate; every other
/// platform conservatively returns `false`, so the caller keeps its re-exec
/// fallback — soundness is never traded for the speedup off macOS.
#[must_use]
pub fn process_is_single_threaded() -> bool {
    #[cfg(target_os = "macos")]
    {
        extern "C" {
            // libSystem: `int pthread_is_threaded_np(void)` — 0 iff single-threaded.
            // Not exposed by the `libc` crate, so declared here.
            fn pthread_is_threaded_np() -> libc::c_int;
        }
        // SAFETY: a pure libSystem query — no arguments, no side effects.
        unsafe { pthread_is_threaded_np() == 0 }
    }
    #[cfg(not(target_os = "macos"))]
    {
        false
    }
}

/// A saved signal mask (opaque) returned by [`block_control_signals`], handed back
/// to [`restore_sigmask`] to undo the block after the fork.
pub struct SavedSigmask(libc::sigset_t);

/// Block SIGINT/SIGTERM/SIGHUP on the calling thread, returning the previous mask.
///
/// Blocking these ACROSS the fork closes the "child exists but the parent's reaper
/// is not yet installed" race: a control signal arriving in that window stays
/// pending until the parent restores the mask, then fires against the (by-then
/// installed) reaper instead of the default terminate disposition.
#[must_use]
pub fn block_control_signals() -> SavedSigmask {
    // SAFETY: `sigset_t` is POD; `sigemptyset`/`sigaddset`/`pthread_sigmask` fill and
    // read owned stack locals and take only valid signal numbers. The old mask is
    // captured for a later exact restore.
    unsafe {
        let mut block: libc::sigset_t = std::mem::zeroed();
        let mut old: libc::sigset_t = std::mem::zeroed();
        libc::sigemptyset(&raw mut block);
        libc::sigaddset(&raw mut block, libc::SIGINT);
        libc::sigaddset(&raw mut block, libc::SIGTERM);
        libc::sigaddset(&raw mut block, libc::SIGHUP);
        libc::pthread_sigmask(libc::SIG_BLOCK, &raw const block, &raw mut old);
        SavedSigmask(old)
    }
}

/// Restore a mask captured by [`block_control_signals`].
pub fn restore_sigmask(saved: &SavedSigmask) {
    // SAFETY: `saved.0` is a valid `sigset_t` produced by `pthread_sigmask`; setting
    // it back has no preconditions.
    unsafe {
        libc::pthread_sigmask(libc::SIG_SETMASK, &raw const saved.0, std::ptr::null_mut());
    }
}

/// Outcome of [`fork_solve_child`].
pub enum ForkOutcome {
    /// We are the PARENT observer; carries the child's PID.
    Parent(i32),
    /// We are the forked CHILD (single-threaded, sharing the parent image).
    Child,
    /// `fork()` failed (e.g. resource exhaustion) — caller must fall back.
    Failed,
}

/// `fork()` the process for the solve supervisor.
///
/// USAGE CONTRACT: the caller MUST have verified [`process_is_single_threaded`]
/// immediately beforehand, so this is the textbook-safe use of `fork()` — there is
/// no other thread mid-mutation of an async-signal-unsafe lock the child could
/// inherit and deadlock on, and the child is a normal single-threaded process
/// afterward (free to allocate and spawn its own threads).
#[must_use]
pub fn fork_solve_child() -> ForkOutcome {
    // SAFETY: `fork` has no pointer arguments; the single-threaded precondition is
    // the caller's documented responsibility (see USAGE CONTRACT above).
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        ForkOutcome::Failed
    } else if pid == 0 {
        ForkOutcome::Child
    } else {
        ForkOutcome::Parent(pid)
    }
}

/// Blocking-reap a child by PID, retrying across `EINTR` (signal-hook handlers on
/// the reaping thread may interrupt the syscall). Returns the raw wait-status —
/// feed it to `std::os::unix::process::ExitStatusExt::from_raw` to classify — or
/// `None` if `waitpid` failed unrecoverably (the caller should then
/// [`kill_and_reap`] and error out so nothing is leaked).
#[must_use]
pub fn wait_for_child(pid: i32) -> Option<i32> {
    loop {
        let mut status: libc::c_int = 0;
        // SAFETY: `status` is an owned writable local that `waitpid` fills.
        let reaped = unsafe { libc::waitpid(pid, &raw mut status, 0) };
        if reaped == pid {
            return Some(status);
        }
        if reaped < 0 {
            let errno = std::io::Error::last_os_error().raw_os_error();
            if errno == Some(libc::EINTR) {
                continue;
            }
            return None;
        }
        // `reaped == 0` cannot occur without WNOHANG; any other positive value is
        // not our child, so keep waiting for the target PID.
    }
}

/// Force-kill a child and reap its zombie (best-effort), used on the unrecoverable
/// [`wait_for_child`] error path so no orphan is left behind.
pub fn kill_and_reap(pid: i32) {
    // SAFETY: `kill`/`waitpid` take a pid and (for waitpid) an owned writable local.
    unsafe {
        libc::kill(pid, libc::SIGKILL);
        let mut status: libc::c_int = 0;
        let _ = libc::waitpid(pid, &raw mut status, 0);
    }
}

// ---------------------------------------------------------------------------
// Crash-injection helpers for the fork-supervisor gate (test support).
//
// These deterministically drive the solve child into each fatal-signal class so
// the parent observer's conversion to a sound `unknown` can be exercised
// end-to-end against the REAL binary's fork path. They are reachable ONLY through
// `ay`'s gated `AY_INTERNAL_TEST_ABORT_SOLVE_CHILD` env hook and never on any
// production path. Each diverges (the process dies before returning).
// ---------------------------------------------------------------------------

/// Trigger a genuine `SIGSEGV` by writing through a null pointer — the most
/// faithful crash probe (matches the design's real null-deref measurement, which
/// dies with signal 11 even past Rust's stack-overflow guard handler).
pub fn crash_null_deref() -> ! {
    // SAFETY: intentionally dereferencing null to raise a real SIGSEGV for the
    // crash-injection gate. This is unreachable on any production path (gated by a
    // test-only env var), and the process dies here.
    unsafe {
        let p: *mut u8 = std::ptr::null_mut();
        std::ptr::write_volatile(p, 0);
    }
    // The volatile null write does not return; belt-and-suspenders.
    std::process::abort();
}

/// Die from the given signal by resetting its disposition to default and raising
/// it. Reliable for signals (e.g. `SIGBUS`) that Rust's runtime otherwise installs
/// a returning guard handler for — the `SIG_DFL` reset guarantees termination, and
/// the parent still reaps the identical `WIFSIGNALED` status a hardware fault would
/// produce (per the design §5.4 guidance to use a real fault or a `SIG_DFL` reset
/// rather than a bare `raise`).
pub fn die_with_signal(sig: i32) -> ! {
    // SAFETY: `signal`/`raise` take a valid signal number; resetting to `SIG_DFL`
    // and raising a fatal signal terminates the process. Gated test-only path.
    unsafe {
        libc::signal(sig, libc::SIG_DFL);
        libc::raise(sig);
    }
    std::process::abort();
}

/// Trigger a genuine stack overflow via unbounded recursion, hitting the guard
/// page — on arm64 macOS this surfaces as `SIGILL` (in the parent's fatal set).
/// `black_box` defeats tail-call elimination so the stack really grows.
pub fn crash_stack_overflow() -> ! {
    // The unbounded recursion is the entire point of this fixture (see doc above).
    #[allow(unconditional_recursion)]
    fn recurse(depth: u64) -> u64 {
        let scratch = [depth; 32];
        let sink = std::hint::black_box(&scratch);
        std::hint::black_box(recurse(std::hint::black_box(depth).wrapping_add(1)))
            .wrapping_add(sink[0])
    }
    std::hint::black_box(recurse(std::hint::black_box(0)));
    std::process::abort();
}
