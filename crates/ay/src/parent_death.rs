// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Child-side guard against outliving the solve supervisor.
//!
//! Every solve runs behind a supervising parent (`run_wrapped_solve_session`)
//! that reaps the solver child and converts a crash into a sound `unknown`. The
//! parent's signal reaper takes the child down on SIGINT/SIGTERM/SIGHUP, but a
//! parent that is SIGKILLed runs no handler at all — and `SIGKILL` is exactly
//! what benchmark harnesses send to the top-level process (`timeout -s KILL`,
//! Python's `subprocess.run(timeout=..)`, runsolver's escalation, a cancelled CI
//! job). Measured on macOS before this module existed: the child kept solving
//! with no deadline, reparented to pid 1, and a 100-file sweep left 11 orphans
//! at ~60% CPU each. z3, a single process, just dies; a drop-in replacement
//! must too.
//!
//! The child therefore watches its parent through a death pipe
//! ([`ay_sys::supervisor::DeathPipe`]): the parent holds the write end for its
//! lifetime and never writes, the child parks a thread in `read(2)` on the
//! read end, and the parent's death — for ANY reason — is the EOF that read
//! returns. On observing it the child takes the same road as a SIGTERM: raise
//! the cooperative stop flags, give the solve a short grace, then leave through
//! [`crate::hard_timeout_fallback_exit`], which reaps a live composed stage
//! and exits via `process::exit` so the proof-staging sweep still runs.
//!
//! Both supervisors are covered. The fork supervisor creates the pipe before
//! `fork()` and splits it ([`watch_in_forked_child`] / `into_parent_writer`);
//! the re-exec supervisor hands the read end across `execve` and names its
//! number to the child through [`DEATH_PIPE_FD_ENV`] ([`configure_reexec_child`]
//! / [`adopt_in_reexec_child`]). On Linux `PR_SET_PDEATHSIG` is armed as well,
//! as a backstop only. There is no user-facing switch: a solver that survives
//! its supervisor is never the right default.

use std::env;
use std::process::Command;
use std::sync::atomic::Ordering;
use std::time::Duration;

use ay_sys::supervisor::{
    adopt_inherited_death_pipe, arm_parent_death_signal, configure_child_death_pipe,
    wait_for_parent_death, DeathPipe, DeathPipeReader, ParentDeath,
};

/// Environment entry through which the re-exec supervisor names the inherited
/// read end to its child. Internal wiring, not a knob: the child consumes it
/// (removes it from its own environment) before it can spawn anything, so no
/// grandchild ever sees a number that means something else in its own table.
const DEATH_PIPE_FD_ENV: &str = "AY_INTERNAL_DEATH_PIPE_FD";

/// Grace between raising the cooperative stop flags and the hard exit. Shorter
/// than the 2 s a SIGTERM allows: nobody is left to read a verdict, the point
/// is to stop burning a CPU promptly, and the hard exit still runs the
/// process-exit sweep that discards unpublished staging files.
const PARENT_DEATH_GRACE: Duration = Duration::from_millis(500);

/// Create the pipe, before the fork or spawn. Best-effort: a process that
/// cannot get a pipe (descriptor exhaustion) still solves, supervised exactly
/// as before — the guard is hygiene, never a verdict.
pub(crate) fn create() -> Option<DeathPipe> {
    DeathPipe::new().ok()
}

/// CHILD side of the fork supervisor, to be called while still
/// single-threaded: keep only the read end (closing this process's copy of the
/// write end, without which EOF could never arrive) and park the watchdog on
/// it. Also arms the Linux parent-death signal backstop.
pub(crate) fn watch_in_forked_child(pipe: Option<DeathPipe>) {
    arm_parent_death_signal();
    if let Some(pipe) = pipe {
        spawn_watchdog(pipe.into_child_reader());
    }
}

/// PARENT side of the re-exec supervisor: let the exec'd child inherit the
/// read end and tell it which descriptor number that is.
pub(crate) fn configure_reexec_child(command: &mut Command, pipe: Option<&DeathPipe>) {
    if let Some(pipe) = pipe {
        configure_child_death_pipe(command, pipe);
        command.env(DEATH_PIPE_FD_ENV, pipe.reader_fd().to_string());
    }
}

/// CHILD side of the re-exec supervisor, to be called first thing in `main`
/// while the process is still single-threaded: consume the environment entry,
/// adopt the descriptor it names (refusing anything that is not the read end
/// of a pipe), and park the watchdog on it. A child launched without a
/// supervisor — tests set the provenance env by hand — finds no entry and
/// returns at once.
pub(crate) fn adopt_in_reexec_child() {
    let Some(value) = env::var_os(DEATH_PIPE_FD_ENV) else {
        return;
    };
    env::remove_var(DEATH_PIPE_FD_ENV);
    let Some(reader) = value
        .to_str()
        .and_then(|fd| fd.parse().ok())
        .and_then(adopt_inherited_death_pipe)
    else {
        return;
    };
    spawn_watchdog(reader);
}

fn spawn_watchdog(reader: DeathPipeReader) {
    let _ = std::thread::Builder::new()
        .name("ay-parent-death".to_string())
        .spawn(move || match wait_for_parent_death(reader) {
            ParentDeath::Observed => shutdown_after_parent_death(),
            // The descriptor cannot tell us anything: keep solving under the
            // parent's own reaper rather than guess about its state.
            ParentDeath::WatchFailed(_) => {}
        });
}

/// The supervisor is gone: stop the way a SIGTERM stops (see
/// `install_sigterm_handler`), with a shorter grace.
fn shutdown_after_parent_death() -> ! {
    crate::TIMED_OUT.store(true, Ordering::SeqCst);
    if let Some(handle) = crate::INTERRUPT_HANDLE.get() {
        handle.store(true, Ordering::SeqCst);
    }
    std::thread::sleep(PARENT_DEATH_GRACE);
    crate::hard_timeout_fallback_exit()
}
