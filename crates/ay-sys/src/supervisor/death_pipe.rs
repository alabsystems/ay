// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parent-death pipe for the solve supervisor (unix).
//!
//! The supervising parent can die in ways it cannot intercept — `SIGKILL`
//! above all, which is what `timeout -s KILL`, Python's
//! `subprocess.run(timeout=..)`, runsolver's escalation and CI job
//! cancellation send to the top-level process. The parent's signal reaper
//! (`install_child_reaper_on_signal` in `ay`) cannot cover that, so the solver
//! child has to notice on its own. Measured before this module existed: a
//! 100-file sweep under `timeout -s KILL` left 11 orphans at ~60% CPU each and
//! drove the load average to 57, where z3 — a single process — simply dies.
//!
//! The mechanism is the classic death pipe. The parent creates a pipe before it
//! forks or spawns, keeps the WRITE end for its whole lifetime and never writes
//! to it; the child keeps the READ end and parks a watchdog thread in `read(2)`
//! on it. When the parent dies for any reason the kernel closes its write end,
//! the read returns 0 (EOF), and the watchdog terminates the child. Nothing here
//! depends on signal delivery, on the parent running any code while dying, or
//! on a Linux-only facility: `PR_SET_PDEATHSIG` is armed IN ADDITION where it
//! exists, as a backstop, never as the primary mechanism.
//!
//! Invariants the API enforces:
//!
//! - the child closes its copy of the WRITE end before it starts watching
//!   ([`DeathPipe::into_child_reader`]) — a child holding its own write end
//!   would never see EOF;
//! - both ends are `FD_CLOEXEC`, so the processes the child `exec`s (external
//!   checkers, `--fallback-solver`, a composed stage) inherit neither end. The
//!   one deliberate exception is the re-exec supervisor's own child, which
//!   needs the read end ACROSS `execve`: [`configure_child_death_pipe`] clears
//!   the flag in the pre-exec hook of that one spawn, and
//!   [`adopt_inherited_death_pipe`] sets it back in the child before anything
//!   else can be spawned.
//!
//! The soundness-critical decision — what the child does when it observes its
//! parent's death — stays in `ay`; this module only owns the descriptors.

use std::io::{self, Read as _};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::process::Command;

/// Both ends of a freshly created death pipe, before the fork/spawn splits
/// them between parent and child.
#[derive(Debug)]
pub struct DeathPipe {
    reader: OwnedFd,
    writer: OwnedFd,
}

/// The child's end. Consumed by [`wait_for_parent_death`].
#[derive(Debug)]
pub struct DeathPipeReader(OwnedFd);

/// The parent's end. Dropping it — or the parent dying with it open — is the
/// EOF the child's watchdog waits for, so the supervisor must hold it until it
/// has reaped the child.
#[derive(Debug)]
#[must_use = "dropping the write end tells the solver child that its supervisor is gone"]
pub struct DeathPipeWriter {
    /// Held open purely for its close-on-drop; nothing is ever written to it.
    _held_open: OwnedFd,
}

impl DeathPipe {
    /// Create the pipe. Both ends are `FD_CLOEXEC` (the standard library sets
    /// the flag atomically where the platform allows, `pipe2(O_CLOEXEC)` on
    /// Linux) so no process either side later `exec`s inherits them.
    pub fn new() -> io::Result<Self> {
        let (reader, writer) = io::pipe()?;
        Ok(Self {
            reader: OwnedFd::from(reader),
            writer: OwnedFd::from(writer),
        })
    }

    /// Raw number of the read end, for handing to a re-exec'd child through its
    /// environment (see [`configure_child_death_pipe`]).
    #[must_use]
    pub fn reader_fd(&self) -> RawFd {
        self.reader.as_raw_fd()
    }

    /// CHILD side of a fork: close this process's copy of the write end and
    /// keep the read end. Closing the write end here is load-bearing — the
    /// kernel delivers EOF only once EVERY write end is closed, and a child
    /// that kept its own copy would wait on itself forever.
    #[must_use]
    pub fn into_child_reader(self) -> DeathPipeReader {
        drop(self.writer);
        DeathPipeReader(self.reader)
    }

    /// PARENT side of a fork or spawn: close this process's copy of the read
    /// end and keep the write end until the child has been reaped.
    pub fn into_parent_writer(self) -> DeathPipeWriter {
        drop(self.reader);
        DeathPipeWriter {
            _held_open: self.writer,
        }
    }
}

/// Let the child `command` is about to `exec` inherit the READ end of `pipe`
/// (and nothing else): a pre-exec hook clears `FD_CLOEXEC` on that one
/// descriptor in the forked child, after the fork and before the `execve`, so
/// the parent's own copy keeps the flag and no other spawn ever sees the pipe.
/// The write end stays `FD_CLOEXEC` and is therefore NOT inherited, which is
/// what makes the parent's death observable from the child.
///
/// On Linux the same hook also arms `PR_SET_PDEATHSIG(SIGTERM)` as a backstop.
///
/// Best-effort by design: a failure inside the hook leaves the child without a
/// death pipe ([`adopt_inherited_death_pipe`] then finds no usable descriptor)
/// but never fails the spawn — the orphan guard is process hygiene, not a
/// verdict, and losing it must not cost a solve.
pub fn configure_child_death_pipe(command: &mut Command, pipe: &DeathPipe) {
    use std::os::unix::process::CommandExt as _;

    let reader = pipe.reader_fd();
    // SAFETY: `pre_exec` is unsafe because only async-signal-safe operations
    // are permitted between fork and exec. This closure captures one POD
    // integer and calls only `fcntl(2)` (and `prctl(2)` on Linux), both
    // async-signal-safe; it performs no allocation, locking, or access to
    // shared Rust state, and it never fails the spawn (see the doc above).
    unsafe {
        command.pre_exec(move || {
            let flags = libc::fcntl(reader, libc::F_GETFD);
            if flags >= 0 {
                libc::fcntl(reader, libc::F_SETFD, flags & !libc::FD_CLOEXEC);
            }
            arm_parent_death_signal_raw();
            Ok(())
        });
    }
}

/// Ask the kernel to send `SIGTERM` when the parent thread that created this
/// process exits (Linux `PR_SET_PDEATHSIG`). A backstop for the pipe: it can
/// race the parent's death (a parent already gone when this runs delivers
/// nothing — the pipe's EOF covers that case) and it is cleared by a
/// set-user-ID `exec`, so it is never relied on alone. No-op elsewhere.
///
/// Call in the forked child immediately after the fork.
pub fn arm_parent_death_signal() {
    // SAFETY: `prctl` (Linux only; a no-op function elsewhere) takes integer
    // arguments only and has no memory-safety preconditions.
    unsafe { arm_parent_death_signal_raw() }
}

/// Async-signal-safe body shared by [`arm_parent_death_signal`] and the
/// pre-exec hook: a single `prctl(2)` on Linux, nothing elsewhere.
///
/// # Safety
///
/// Always safe to call; marked `unsafe` only so it can be invoked from the
/// pre-exec hook without a nested `unsafe` block hiding that it is FFI.
unsafe fn arm_parent_death_signal_raw() {
    #[cfg(target_os = "linux")]
    {
        // `SIGTERM` is a small positive constant; the widening is lossless and
        // the fallback of 0 would merely clear a death signal that was never set.
        let signal = libc::c_ulong::try_from(libc::SIGTERM).unwrap_or(0);
        // SAFETY: `PR_SET_PDEATHSIG` takes one integer argument and touches no
        // memory owned by this process; the return value is deliberately
        // ignored because the pipe, not this call, is the primary mechanism.
        unsafe {
            libc::prctl(libc::PR_SET_PDEATHSIG, signal);
        }
    }
}

/// Take ownership of a death-pipe read end inherited across `execve` (the fd
/// number arrives through the environment; see `parent_death` in `ay`).
///
/// Refuses anything that is not the read end of a pipe: a stale or forged
/// number that names a regular file, a terminal, a socket, or a WRITE end is
/// rejected rather than watched, because reading EOF off the wrong descriptor
/// would terminate a healthy solve. On success the descriptor is marked
/// `FD_CLOEXEC` again so nothing this process spawns inherits it.
#[must_use]
pub fn adopt_inherited_death_pipe(fd: RawFd) -> Option<DeathPipeReader> {
    if fd < 0 {
        return None;
    }
    // SAFETY: `fstat` and `fcntl` take a descriptor number and (for `fstat`)
    // an owned, writable `stat` buffer; a number that is not an open
    // descriptor is reported through the return value, never dereferenced.
    let is_pipe_read_end = unsafe {
        let mut info: libc::stat = std::mem::zeroed();
        let is_fifo =
            libc::fstat(fd, &raw mut info) == 0 && (info.st_mode & libc::S_IFMT) == libc::S_IFIFO;
        let access = libc::fcntl(fd, libc::F_GETFL);
        is_fifo && access >= 0 && (access & libc::O_ACCMODE) == libc::O_RDONLY
    };
    if !is_pipe_read_end {
        return None;
    }
    // SAFETY: the descriptor was just verified open and is the read end of a
    // pipe this process inherited for exactly this purpose; the caller consumes
    // the environment entry that named it, so ownership is transferred once and
    // nothing else in the process refers to the number.
    let owned = unsafe { OwnedFd::from_raw_fd(fd) };
    // SAFETY: `fcntl` on an owned, open descriptor with valid flag arguments.
    unsafe {
        let flags = libc::fcntl(owned.as_raw_fd(), libc::F_GETFD);
        if flags < 0 || libc::fcntl(owned.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC) < 0
        {
            return None;
        }
    }
    Some(DeathPipeReader(owned))
}

/// Why [`wait_for_parent_death`] returned.
#[derive(Debug)]
pub enum ParentDeath {
    /// EOF: every write end is closed, so the supervising parent is gone.
    Observed,
    /// The read failed for a reason other than `EINTR`; the caller cannot
    /// learn anything about the parent from this descriptor.
    WatchFailed(io::Error),
}

/// Block until the supervising parent dies (EOF on the read end) or the
/// descriptor becomes unreadable. Retries `EINTR`; bytes are never expected
/// (the parent never writes) and are discarded if they ever arrive, so only a
/// closed write end returns [`ParentDeath::Observed`].
pub fn wait_for_parent_death(reader: DeathPipeReader) -> ParentDeath {
    let mut end = std::fs::File::from(reader.0);
    let mut sink = [0_u8; 64];
    loop {
        match end.read(&mut sink) {
            Ok(0) => return ParentDeath::Observed,
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return ParentDeath::WatchFailed(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Stdio;
    use std::sync::mpsc;
    use std::time::{Duration, Instant};

    fn fd_flags(fd: RawFd) -> libc::c_int {
        // SAFETY: `F_GETFD` reads a flag word for an open descriptor and
        // touches no memory.
        unsafe { libc::fcntl(fd, libc::F_GETFD) }
    }

    fn is_cloexec(fd: RawFd) -> bool {
        let flags = fd_flags(fd);
        flags >= 0 && (flags & libc::FD_CLOEXEC) != 0
    }

    /// Wait for `child` to exit, killing it if it outlives `budget`.
    fn wait_bounded(child: &mut std::process::Child, budget: Duration) -> Option<i32> {
        let deadline = Instant::now() + budget;
        loop {
            if let Ok(Some(status)) = child.try_wait() {
                return status.code();
            }
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn both_ends_are_created_close_on_exec() {
        let pipe = DeathPipe::new().expect("create death pipe");
        assert!(
            is_cloexec(pipe.reader.as_raw_fd()),
            "read end must be CLOEXEC"
        );
        assert!(
            is_cloexec(pipe.writer.as_raw_fd()),
            "write end must be CLOEXEC"
        );
    }

    #[test]
    fn watchdog_returns_when_the_parent_end_is_dropped() {
        let pipe = DeathPipe::new().expect("create death pipe");
        // Simulate the split: a "child" reader and a "parent" writer. The
        // writer is a fresh copy so the reader-side close of the original
        // write end (the child invariant) is exercised too.
        let parent_writer = DeathPipeWriter {
            _held_open: pipe.writer.try_clone().expect("dup write end"),
        };
        let reader = pipe.into_child_reader();

        let (tx, rx) = mpsc::channel();
        let watchdog = std::thread::spawn(move || {
            let outcome = wait_for_parent_death(reader);
            tx.send(()).expect("report watchdog return");
            outcome
        });
        assert!(
            rx.recv_timeout(Duration::from_millis(300)).is_err(),
            "the watchdog must block while the parent's write end is open"
        );

        drop(parent_writer);
        rx.recv_timeout(Duration::from_secs(5))
            .expect("the watchdog must return within 5 s of the write end closing");
        assert!(
            matches!(
                watchdog.join().expect("join watchdog"),
                ParentDeath::Observed
            ),
            "a closed write end is observed as the parent's death"
        );
    }

    #[test]
    fn child_reader_does_not_keep_its_own_write_end() {
        // If `into_child_reader` failed to close the write end, this read would
        // block forever: the process itself would be the surviving writer.
        let reader = DeathPipe::new()
            .expect("create death pipe")
            .into_child_reader();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let outcome = wait_for_parent_death(reader);
            let _ = tx.send(matches!(outcome, ParentDeath::Observed));
        });
        assert!(
            rx.recv_timeout(Duration::from_secs(5))
                .expect("EOF must arrive at once when no write end is open"),
            "the only write end was closed by into_child_reader, so EOF is immediate"
        );
    }

    #[test]
    fn exec_child_inherits_the_read_end_and_not_the_write_end() {
        let pipe = DeathPipe::new().expect("create death pipe");
        let reader_fd = pipe.reader_fd();
        let writer_fd = pipe.writer.as_raw_fd();

        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "ls /dev/fd"])
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null());
        configure_child_death_pipe(&mut command, &pipe);
        let output = command.output().expect("list the child's descriptors");
        assert!(output.status.success(), "ls /dev/fd failed: {output:?}");
        let listing = String::from_utf8_lossy(&output.stdout);
        let open_in_child: Vec<RawFd> = listing
            .split_whitespace()
            .filter_map(|entry| entry.parse().ok())
            .collect();
        assert!(
            open_in_child.contains(&reader_fd),
            "the exec'd child must inherit the read end {reader_fd}; it has {open_in_child:?}"
        );
        assert!(
            !open_in_child.contains(&writer_fd),
            "the exec'd child must NOT inherit the write end {writer_fd}; it has {open_in_child:?}"
        );
        // The parent's own copy of the read end keeps its CLOEXEC flag: only
        // the forked child cleared it, after the fork.
        assert!(
            is_cloexec(reader_fd),
            "the pre-exec hook must not touch the parent's descriptor flags"
        );
    }

    #[test]
    fn exec_child_sees_eof_when_the_parent_end_closes() {
        let pipe = DeathPipe::new().expect("create death pipe");
        let reader_fd = pipe.reader_fd();

        // `cat` on the inherited read end blocks until every write end is gone.
        let mut command = Command::new("/bin/cat");
        command
            .arg(format!("/dev/fd/{reader_fd}"))
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        configure_child_death_pipe(&mut command, &pipe);
        let mut child = command
            .spawn()
            .expect("spawn cat on the inherited read end");

        // Parent side: close the read end, keep the write end — then let it go.
        let writer = pipe.into_parent_writer();
        std::thread::sleep(Duration::from_millis(200));
        assert!(
            matches!(child.try_wait(), Ok(None)),
            "cat must still be blocked while the parent holds the write end"
        );
        drop(writer);

        let code = wait_bounded(&mut child, Duration::from_secs(5));
        assert_eq!(
            code,
            Some(0),
            "cat must exit at EOF within 5 s of the parent's write end closing"
        );
    }

    #[test]
    fn adopt_accepts_only_a_pipe_read_end() {
        let pipe = DeathPipe::new().expect("create death pipe");
        // A write end is a pipe but the wrong direction.
        let writer_dup = pipe.writer.try_clone().expect("dup write end");
        assert!(
            adopt_inherited_death_pipe(writer_dup.as_raw_fd()).is_none(),
            "a write end must be refused"
        );
        // A non-pipe descriptor.
        let null = std::fs::File::open("/dev/null").expect("open /dev/null");
        assert!(
            adopt_inherited_death_pipe(null.as_raw_fd()).is_none(),
            "a non-pipe descriptor must be refused"
        );
        // Nonsense numbers.
        assert!(adopt_inherited_death_pipe(-1).is_none());
        assert!(adopt_inherited_death_pipe(RawFd::MAX).is_none());

        // The genuine read end, handed over as a raw number the way the
        // environment delivers it: adoption takes ownership and re-marks it
        // CLOEXEC (an exec'd child inherits it without the flag).
        let reader = pipe.reader.try_clone().expect("dup read end");
        let raw = reader.as_raw_fd();
        // SAFETY: clearing CLOEXEC on a descriptor this test owns, to model the
        // post-exec state; `fcntl` with valid flag arguments.
        unsafe {
            libc::fcntl(raw, libc::F_SETFD, 0);
        }
        assert!(!is_cloexec(raw));
        std::mem::forget(reader); // ownership moves to the adopted OwnedFd
        let adopted = adopt_inherited_death_pipe(raw).expect("a pipe read end is adopted");
        assert!(is_cloexec(raw), "adoption must restore CLOEXEC");
        drop(adopted);
    }
}
