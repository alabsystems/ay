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

use std::process::Command;

/// Arrange for `command` and all of its descendants to inherit a hard virtual
/// address-space ceiling.
///
/// The limit is installed in the forked child immediately before `exec`, so it
/// never constrains the supervising AY process. Lowering both the soft and hard
/// limits prevents the executed program from raising its own allowance again.
/// A failure in `getrlimit`/`setrlimit` makes `Command::spawn` fail closed.
pub fn configure_child_address_space_limit(command: &mut Command, bytes: u64) {
    use std::os::unix::process::CommandExt as _;

    let requested = libc::rlim_t::try_from(bytes).unwrap_or(libc::rlim_t::MAX);
    // SAFETY: `pre_exec` is necessarily unsafe because only async-signal-safe
    // operations are permitted after fork. This closure captures one POD
    // integer and calls only `getrlimit(2)`/`setrlimit(2)` on owned stack
    // storage. It performs no allocation, locking, or access to shared Rust
    // state. Returning `last_os_error` is the standard `Command` pre-exec error
    // path and causes the parent-side spawn to fail.
    unsafe {
        command.pre_exec(move || {
            let mut inherited: libc::rlimit = std::mem::zeroed();
            if libc::getrlimit(libc::RLIMIT_AS, &raw mut inherited) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            let effective = requested.min(inherited.rlim_max);
            let limit = libc::rlimit {
                rlim_cur: effective,
                rlim_max: effective,
            };
            if libc::setrlimit(libc::RLIMIT_AS, &raw const limit) == 0 {
                Ok(())
            } else {
                Err(std::io::Error::last_os_error())
            }
        });
    }
}

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

/// A child state observed without consuming its wait status on macOS.
///
/// Keeping an exited process-group leader waitable prevents its numeric PID
/// (and therefore PGID) from being reused before the caller has terminated any
/// residual descendants. The caller must eventually reap the child through its
/// owned [`std::process::Child`] handle.
#[cfg(target_os = "macos")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnreapedChildState {
    /// The child has neither stopped nor exited.
    Running,
    /// The child stopped because of the contained signal number.
    Stopped(i32),
    /// The child exited normally or because of a signal.
    Exited,
}

/// Observe a child on macOS without consuming its wait status.
///
/// `nix` deliberately does not expose `waitid(2)` on Apple targets, even though
/// macOS provides `waitid(P_PID, ..., WNOWAIT)`. Isolating that call here keeps
/// the rest of the workspace free of unsafe code while retaining the process-
/// group ownership invariant required by benchmark watchdog cleanup.
#[cfg(target_os = "macos")]
pub fn observe_child_unreaped(
    child: &std::process::Child,
    include_stopped: bool,
) -> std::io::Result<UnreapedChildState> {
    let raw_pid = libc::pid_t::try_from(child.id()).map_err(|_| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "child PID does not fit macOS pid_t",
        )
    })?;
    let child_id = libc::id_t::try_from(raw_pid).map_err(|_| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "child PID does not fit macOS id_t",
        )
    })?;
    let mut options = libc::WEXITED | libc::WNOHANG | libc::WNOWAIT;
    if include_stopped {
        options |= libc::WSTOPPED;
    }

    loop {
        // `waitid(..., WNOHANG)` reports no event by leaving `si_pid` zero, so
        // start from a fully initialized value on every try (including EINTR).
        // SAFETY: `siginfo_t` is a C POD value; `waitid` receives a valid owned
        // output pointer, a positive PID obtained from an owned `Child`, and the
        // documented wait flags. WNOWAIT guarantees that the status is observed
        // but not consumed.
        let (result, info) = unsafe {
            let mut info: libc::siginfo_t = std::mem::zeroed();
            let result = libc::waitid(libc::P_PID, child_id, &raw mut info, options);
            (result, info)
        };
        if result != 0 {
            let error = std::io::Error::last_os_error();
            if error.raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(error);
        }
        if info.si_pid == 0 {
            return Ok(UnreapedChildState::Running);
        }
        if info.si_pid != raw_pid {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "waitid returned PID {} while observing child {raw_pid}",
                    info.si_pid
                ),
            ));
        }
        return match info.si_code {
            libc::CLD_EXITED | libc::CLD_KILLED | libc::CLD_DUMPED => {
                Ok(UnreapedChildState::Exited)
            }
            libc::CLD_STOPPED if include_stopped => Ok(UnreapedChildState::Stopped(info.si_status)),
            libc::CLD_CONTINUED => Ok(UnreapedChildState::Running),
            code => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "waitid returned unexpected child status code {code} (status {})",
                    info.si_status
                ),
            )),
        };
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

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;

    #[test]
    fn child_address_space_limit_is_installed_before_exec() {
        const LIMIT_BYTES: u64 = 512 * 1024 * 1024;
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "ulimit -v"]);
        configure_child_address_space_limit(&mut command, LIMIT_BYTES);
        let output = command.output().expect("spawn address-space-limited shell");
        assert!(output.status.success());
        let kib: u64 = String::from_utf8(output.stdout)
            .expect("shell output is UTF-8")
            .trim()
            .parse()
            .expect("ulimit -v reports KiB");
        assert!(
            kib <= LIMIT_BYTES / 1024,
            "child limit {kib} KiB exceeds requested {} KiB",
            LIMIT_BYTES / 1024
        );
    }
}

#[cfg(all(test, target_os = "macos"))]
mod macos_tests {
    use super::*;
    use std::io::Write as _;
    use std::process::{Child, Stdio};
    use std::time::{Duration, Instant};

    struct ChildGuard(Option<Child>);

    impl Drop for ChildGuard {
        fn drop(&mut self) {
            if let Some(child) = self.0.as_mut() {
                let _ = child.kill();
                let _ = child.wait();
            }
        }
    }

    fn wait_for_non_running(child: &Child, include_stopped: bool) -> UnreapedChildState {
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let state = observe_child_unreaped(child, include_stopped)
                .expect("observe child without reaping");
            if state != UnreapedChildState::Running {
                return state;
            }
            assert!(Instant::now() < deadline, "timed out observing child state");
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    #[test]
    fn waitid_observes_stop_and_exit_without_reaping() {
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "read token; kill -STOP $$; exit 7"])
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let mut guarded = ChildGuard(Some(command.spawn().expect("spawn waitid probe")));
        let child = guarded.0.as_mut().expect("guard owns child");

        assert_eq!(
            observe_child_unreaped(child, true).expect("observe blocked child"),
            UnreapedChildState::Running
        );
        child
            .stdin
            .take()
            .expect("probe stdin")
            .write_all(b"continue\n")
            .expect("release child read");
        assert_eq!(
            wait_for_non_running(child, true),
            UnreapedChildState::Stopped(libc::SIGSTOP)
        );

        let raw_pid = libc::pid_t::try_from(child.id()).expect("child PID fits pid_t");
        // SAFETY: `raw_pid` names the live child owned by `guarded`; SIGCONT has
        // no memory-safety preconditions and merely resumes the stopped probe.
        assert_eq!(unsafe { libc::kill(raw_pid, libc::SIGCONT) }, 0);
        assert_eq!(
            wait_for_non_running(child, false),
            UnreapedChildState::Exited
        );

        let mut child = guarded.0.take().expect("guard owns child");
        let status = child.wait().expect("owned Child reaps observed exit");
        assert_eq!(status.code(), Some(7));
    }
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
