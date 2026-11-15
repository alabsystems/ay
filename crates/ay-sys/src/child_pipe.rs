// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Writes to a pipe whose reader may already be gone — a child process's
//! stdin above all — that report the dead reader as `EPIPE`, never as a
//! process-killing `SIGPIPE`.
//!
//! WHY THIS EXISTS. `std` ignores SIGPIPE at startup only under Rust's DEFAULT
//! broken-pipe policy. This workspace builds with the Trust verification
//! profile `unix_hardened`, and for that profile the compiler declares
//! `-Zon-broken-pipe=kill` whenever no explicit `-Zon-broken-pipe` is given
//! (trust `Session::trust_effective_on_broken_pipe`, since 2026-09-14): the
//! generated `main` hands `SIG_DFL` to `std::rt::lang_start`, which installs it.
//! That is the C-tool behaviour the profile wants for stdout — `ay … | head`
//! exits quietly — but it applies to EVERY write to a pipe with no reader, so a
//! write to a child that has died kills the parent before the caller's
//! `io::Result` is ever looked at. Measured 2026-09-26: the certified-SDP
//! bridge's tests and `ay model-count` with a FlowCutter that exits early both
//! died with exit 141 on the code paths written to handle exactly that error.
//!
//! The disposition is process-global and belongs to whichever binary links
//! this code, so a writer that must survive a dead reader cannot rely on it.
//! Switching the whole process back to "ignore" is no substitute either: under
//! an explicit `-Zon-broken-pipe` std stops resetting SIGPIPE in the children
//! it spawns, so every child (an `xz` whose output is closed early, say) would
//! inherit "ignore" and fail with an error instead of exiting on the signal.
//! [`ChildPipeWriter`] suppresses the signal for its own descriptor only:
//!
//! - Apple: `fcntl(F_SETNOSIGPIPE)` on the descriptor at construction. XNU
//!   raises a pipe's SIGPIPE against the whole PROCESS (`psignal` in
//!   `dofilewrite`), so a per-thread mask could not contain it; the
//!   per-open-file flag makes the kernel skip the signal and return `EPIPE`.
//! - Linux and Android: POSIX sends a pipe's SIGPIPE to the writing THREAD
//!   (Linux: `send_sig(SIGPIPE, current, 0)` in `anon_pipe_write`). Every write
//!   runs with SIGPIPE blocked on the calling thread, and a SIGPIPE the write
//!   left pending is consumed with a zero-timeout `sigtimedwait` before the
//!   previous mask is restored — WHATEVER the write returned. The signal does
//!   not only come with `EPIPE`: when the reader goes away while a blocking
//!   write is parked on a full pipe, having already copied part of the buffer,
//!   Linux sends SIGPIPE AND returns the partial count as success (`if (!ret)
//!   ret = -EPIPE;` — the error replaces only a zero count), and the caller
//!   sees `EPIPE` only on its next write. That is the ordinary shape of a
//!   child that reads a little of a larger-than-pipe input and dies. A SIGPIPE
//!   that was ALREADY pending before the write is left alone, to be delivered
//!   exactly as it would have been. The one signal this can take that the
//!   write did not raise: a process-directed SIGPIPE sent by someone else
//!   during the write, while every thread of the process has it blocked
//!   (otherwise the kernel hands it to a thread that accepts it).
//! - Anywhere else: the write is passed through unchanged. Windows has no
//!   SIGPIPE (a broken pipe is an ordinary error there); another Unix keeps
//!   the process disposition.
//!
//! [`ChildPipeWriter::take_from`] is how production code takes a child's
//! stdin. In non-test Rust under `crates/`, `ay-quality-gate`'s child-pipe
//! policy (which runs when the gate is run; nothing runs it automatically)
//! fails on a `Child`'s `stdin` field taken or borrowed any other way (a flag
//! test, `drop`, an assignment and a `Write` call on the field are allowed), on
//! a bare `ChildStdin` type, and on a function that spawns with
//! `Stdio::piped()` stdin or creates a raw pipe without naming this writer.
//! The policy is lexical and per function; its module docs list what it sees.
//!
//! THE PROCESS'S OWN STDOUT AND STDERR KEEP THE SIGNAL, deliberately. When the
//! reader of `ay … | head` (or `ay-pb …`, or any AY binary) goes away, the next
//! write to stdout ends the process on SIGPIPE: exit status 141 in a shell,
//! no panic, no "Broken pipe" message, like `cat` or `grep` (measured
//! 2026-09-27: `{ sleep 1; ay --version; } | true` and the same with a solve
//! both give status 141 and nothing on stderr but the solve's session
//! record, `c ay.session.end exit.signal=13`). A verdict written after its
//! reader left has nobody to read it, so there is no error path to keep alive
//! there, and the alternatives are worse: `-Zon-broken-pipe=error` turns every
//! `println!` into a panic and stops std resetting SIGPIPE in spawned
//! children; ignoring the signal process-wide leaks "ignore" into every child
//! (above). A CHILD's death is different — it is an event the parent reports
//! (`unknown`, a failed check, a declined bridge) — so only writes to a child
//! go through [`ChildPipeWriter`].
//!
//! SOCKETS are not covered by std everywhere. On Linux std's
//! `UnixStream`/`TcpStream` `write` passes `MSG_NOSIGNAL`, but `write_vectored`
//! is a plain `writev` that still raises SIGPIPE. On Apple `MSG_NOSIGNAL` is
//! 0 and std sets `SO_NOSIGPIPE` only on a socket it opens with `socket()`
//! (`connect`, `bind`), not on a `UnixStream::pair` end, an `accept`ed
//! connection or a descriptor adopted with `from_raw_fd`. AY has one
//! production socket writer (inventory 2026-10-08; the one `UnixListener` is a
//! test fixture): `ay submission`'s live Zenodo upload, built only with
//! `--features submission-live`. It talks HTTPS through `ureq`, whose rustls
//! layer writes TLS records with `write_vectored`, so on Linux a server that
//! resets the connection mid-request would raise SIGPIPE. Each Zenodo exchange
//! runs inside [`with_sigpipe_held`], which turns that into the request's
//! `EPIPE` error; on Apple `ureq`'s sockets come from std's `connect` and carry
//! `SO_NOSIGPIPE`. A new socket writer needs the same care: it is not a
//! child's pipe, so the quality gate's child-pipe policy does not look at it.

use std::io::{self, Write};

/// A pipe writer whose writes fail with [`io::ErrorKind::BrokenPipe`] when the
/// reader is gone, instead of raising SIGPIPE. See the module docs for why a
/// child's stdin needs this in a `unix_hardened` build and how each platform
/// provides it.
#[derive(Debug)]
pub struct ChildPipeWriter<W> {
    inner: W,
}

#[cfg(target_vendor = "apple")]
impl<W: Write + std::os::fd::AsFd> ChildPipeWriter<W> {
    /// Wrap `inner`, typically a [`std::process::ChildStdin`], and mark its
    /// descriptor `F_SETNOSIGPIPE`.
    ///
    /// # Errors
    ///
    /// When the kernel refuses the mark. The caller must then treat the pipe
    /// as unusable: a write through it could still kill the process.
    pub fn new(inner: W) -> io::Result<Self> {
        mark_no_sigpipe(inner.as_fd())?;
        Ok(Self { inner })
    }
}

#[cfg(not(target_vendor = "apple"))]
impl<W: Write> ChildPipeWriter<W> {
    /// Wrap `inner`, typically a [`std::process::ChildStdin`]. Nothing is
    /// marked here: on Linux every write holds SIGPIPE itself, and Windows has
    /// no SIGPIPE.
    ///
    /// # Errors
    ///
    /// Never; the `Result` matches the Apple constructor, which can fail.
    pub const fn new(inner: W) -> io::Result<Self> {
        Ok(Self { inner })
    }
}

impl ChildPipeWriter<std::process::ChildStdin> {
    /// Take the stdin pipe of `child`, spawned with `Stdio::piped()` stdin,
    /// as a writer that reports a dead child as `EPIPE`.
    ///
    /// # Errors
    ///
    /// When `child` has no stdin pipe (it was not spawned with a piped stdin,
    /// or the pipe was already taken), or when the pipe cannot be marked
    /// ([`Self::new`]); the pipe is closed in that case. Either way the child
    /// is still running and still the caller's: kill and reap it.
    pub fn take_from(child: &mut std::process::Child) -> io::Result<Self> {
        let stdin = child.stdin.take().ok_or_else(|| {
            io::Error::other("the child has no stdin pipe (not piped, or already taken)")
        })?;
        Self::new(stdin)
    }
}

impl<W: Write> Write for ChildPipeWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        without_sigpipe(|| self.inner.write(buf))
    }

    fn flush(&mut self) -> io::Result<()> {
        without_sigpipe(|| self.inner.flush())
    }
}

/// `F_SETNOSIGPIPE` from the macOS SDK's `<sys/fcntl.h>` ("No SIGPIPE
/// generated on EPIPE"); the pinned `libc` crate does not export it for Apple.
#[cfg(target_vendor = "apple")]
const F_SETNOSIGPIPE: libc::c_int = 73;

#[cfg(target_vendor = "apple")]
fn mark_no_sigpipe(fd: std::os::fd::BorrowedFd<'_>) -> io::Result<()> {
    use std::os::fd::AsRawFd as _;
    // SAFETY: `fd` is a borrowed descriptor that stays open for this call.
    // `F_SETNOSIGPIPE` takes one int argument and only sets a flag on the open
    // file; it touches no memory of ours.
    let status = unsafe { libc::fcntl(fd.as_raw_fd(), F_SETNOSIGPIPE, 1) };
    if status == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn without_sigpipe<T>(write: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
    let held = SigpipeHeld::block()?;
    let result = write();
    // On EVERY result, not only `Err(BrokenPipe)`: a blocking write that the
    // reader's exit cut short returns `Ok(partial)` with the signal already
    // raised (module docs). Left pending, it would kill the process the moment
    // `held` restores the caller's mask.
    held.consume_raised();
    // `held` restores the caller's mask when it drops, on every path.
    result
}

#[cfg(not(any(target_os = "linux", target_os = "android")))]
fn without_sigpipe<T>(write: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
    write()
}

/// Run `io` with SIGPIPE held off the calling thread: the scope for a writer
/// this module cannot mark, such as a socket that a library writes with
/// `write_vectored` (rustls under `ureq`; module docs, SOCKETS).
///
/// - Linux and Android: SIGPIPE is blocked on the calling thread for the
///   whole of `io`, and one that `io` raised is consumed before the caller's
///   mask is restored, exactly as around a [`ChildPipeWriter`] write. A peer
///   that is gone is then the `EPIPE` error `io` reports. Only writes made on
///   the calling thread are covered.
/// - Apple and anywhere else: `io` simply runs. On Apple a socket std opened
///   with `socket()` (`TcpStream::connect`, `connect_timeout`) already carries
///   `SO_NOSIGPIPE`; a pipe, or a socket that did not come from std's
///   `connect`/`bind`, is not covered by this scope there.
///
/// Spawn no child inside `io`: std's `Command` hands the spawning thread's
/// signal mask to the child on both its `posix_spawn` and its fork/exec path,
/// so on Linux the child would start with SIGPIPE blocked.
///
/// # Errors
///
/// When SIGPIPE cannot be blocked; `io` has not run then.
pub fn with_sigpipe_held<T>(io: impl FnOnce() -> T) -> io::Result<T> {
    without_sigpipe(|| Ok(io()))
}

/// SIGPIPE blocked on the calling thread, with the caller's mask saved.
#[cfg(any(target_os = "linux", target_os = "android"))]
struct SigpipeHeld {
    previous: libc::sigset_t,
    already_pending: bool,
}

#[cfg(any(target_os = "linux", target_os = "android"))]
impl SigpipeHeld {
    fn sigpipe_only() -> libc::sigset_t {
        // SAFETY: `sigset_t` is plain data; `sigemptyset` initializes the
        // owned local and `sigaddset` adds a valid signal number to it.
        unsafe {
            let mut set: libc::sigset_t = std::mem::zeroed();
            libc::sigemptyset(&raw mut set);
            libc::sigaddset(&raw mut set, libc::SIGPIPE);
            set
        }
    }

    fn block() -> io::Result<Self> {
        let sigpipe = Self::sigpipe_only();
        // SAFETY: both pointers name owned, initialized `sigset_t` locals;
        // `pthread_sigmask` reads the first and writes the caller's current
        // mask into the second.
        let (status, previous) = unsafe {
            let mut previous: libc::sigset_t = std::mem::zeroed();
            let status =
                libc::pthread_sigmask(libc::SIG_BLOCK, &raw const sigpipe, &raw mut previous);
            (status, previous)
        };
        if status != 0 {
            return Err(io::Error::from_raw_os_error(status));
        }
        // SAFETY: `sigpending` fills the owned local; `sigismember` reads it
        // with a valid signal number.
        let already_pending = unsafe {
            let mut pending: libc::sigset_t = std::mem::zeroed();
            libc::sigpending(&raw mut pending) == 0
                && libc::sigismember(&raw const pending, libc::SIGPIPE) == 1
        };
        Ok(Self {
            previous,
            already_pending,
        })
    }

    /// Consume the SIGPIPE the write raised on this thread, if it raised one,
    /// unless one was already pending before it (standard signals do not
    /// queue, so that one and ours are the same pending signal and it must
    /// survive). A write that raised nothing costs one `sigtimedwait` that
    /// finds nothing (`EAGAIN`).
    fn consume_raised(&self) {
        if self.already_pending {
            return;
        }
        let sigpipe = Self::sigpipe_only();
        let immediately = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        loop {
            // SAFETY: `sigpipe` and `immediately` are initialized locals; a
            // null `siginfo_t` pointer is permitted. SIGPIPE is blocked on
            // this thread, so it can only be dequeued, never delivered.
            let status = unsafe {
                libc::sigtimedwait(
                    &raw const sigpipe,
                    std::ptr::null_mut(),
                    &raw const immediately,
                )
            };
            if status == -1 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return;
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "android"))]
impl Drop for SigpipeHeld {
    fn drop(&mut self) {
        // SAFETY: `previous` is the mask `pthread_sigmask` saved in `block`;
        // restoring it has no other preconditions.
        unsafe {
            libc::pthread_sigmask(
                libc::SIG_SETMASK,
                &raw const self.previous,
                std::ptr::null_mut(),
            );
        }
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::ChildPipeWriter;
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    /// A write to a child that has exited returns `BrokenPipe` and the process
    /// lives. This test binary is built with the workspace's `unix_hardened`
    /// profile, so SIGPIPE is `SIG_DFL` here: without the wrapper the
    /// `write_all` below ends the test run with exit 141.
    #[test]
    fn a_write_to_an_exited_child_is_an_epipe_error_not_a_signal() {
        let mut child = Command::new("/bin/sh")
            .args(["-c", "exit 0"])
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn a child that exits at once");
        let stdin = child.stdin.take().expect("piped stdin");
        // Reap it first, so the read end is closed before the first write.
        child.wait().expect("reap the child");
        let mut writer = ChildPipeWriter::new(stdin).expect("mark the pipe");
        // Larger than any pipe buffer: even a reader that were still alive
        // could not absorb it without reading.
        let payload = vec![b'x'; 1 << 20];
        let error = writer
            .write_all(&payload)
            .and_then(|()| writer.flush())
            .expect_err("no reader is left");
        assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe);
        // A second write fails the same way: nothing about the first one was
        // left pending to fire later.
        let error = writer.write_all(b"again\n").expect_err("still no reader");
        assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe);
    }

    /// `take_from` hands the pipe out once, as a working writer, and is an
    /// error (never a panic, never a bare `ChildStdin`) for a second take or
    /// for a child spawned without a stdin pipe.
    #[test]
    fn take_from_hands_out_the_stdin_pipe_once() {
        let mut child = Command::new("/bin/sh")
            .args(["-c", "cat"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn cat");
        let mut writer = ChildPipeWriter::take_from(&mut child).expect("take the piped stdin");
        assert!(
            ChildPipeWriter::take_from(&mut child).is_err(),
            "the pipe was already taken"
        );
        writer
            .write_all(b"through the writer\n")
            .expect("cat reads");
        writer.flush().expect("flush");
        drop(writer);
        let output = child.wait_with_output().expect("reap cat");
        assert!(output.status.success());
        assert_eq!(output.stdout, b"through the writer\n");

        let mut unpiped = Command::new("/bin/sh")
            .args(["-c", "exit 0"])
            .stdin(Stdio::null())
            .spawn()
            .expect("spawn a child without a stdin pipe");
        assert!(ChildPipeWriter::take_from(&mut unpiped).is_err());
        unpiped.wait().expect("reap the unpiped child");
    }

    /// A reader that takes a little of a larger-than-pipe write and then exits
    /// ends the write in `BrokenPipe`, and the process lives. A reaped child
    /// cannot reach this path: here the blocking write is PARKED on the full
    /// pipe when the reader goes, and Linux then raises SIGPIPE and returns
    /// the bytes it had already copied as `Ok(partial)`. A wrapper that
    /// consumed the signal only on `Err(BrokenPipe)` left it pending, and the
    /// process died with exit 141 the moment the mask was restored (measured
    /// 2026-09-26 on Linux 6.12 aarch64 with `-Zon-broken-pipe=kill`, the
    /// disposition `unix_hardened` gives `main`). On Apple `F_SETNOSIGPIPE`
    /// stops the kernel raising it at all, and the parked write fails with
    /// `EPIPE` there.
    #[test]
    fn a_reader_that_exits_mid_write_is_an_epipe_error_not_a_signal() {
        // Built before the spawn, so the write starts as soon as it can.
        let payload = vec![b'x'; 4 << 20];
        let mut child = Command::new("/bin/sh")
            .args(["-c", "head -c 1000 >/dev/null"])
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn a child that reads a little and exits");
        let stdin = child.stdin.take().expect("piped stdin");
        let mut writer = ChildPipeWriter::new(stdin).expect("mark the pipe");
        // `write_all` by hand, so each call's result is seen: the short
        // success the reader's exit produces is the case under test.
        let mut written = 0;
        let mut short_successes = 0;
        let error = loop {
            match writer.write(&payload[written..]) {
                Ok(0) => panic!("a pipe write accepted nothing without an error"),
                Ok(accepted) => {
                    if accepted < payload.len() - written {
                        short_successes += 1;
                    }
                    written += accepted;
                    assert!(
                        written < payload.len(),
                        "a reader that takes 1000 bytes cannot absorb 4 MiB"
                    );
                }
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                Err(error) => break error,
            }
        };
        assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe);
        assert!(
            child.wait().expect("reap the child").success(),
            "the reader exited on its own after its 1000 bytes"
        );
        // Linux: the parked write returned what it had copied, with the
        // signal raised, and the next one failed. Without this the test could
        // pass without ever reaching the partial-success path.
        #[cfg(any(target_os = "linux", target_os = "android"))]
        assert!(
            short_successes >= 1 && written > 0,
            "the reader's exit must cut a parked write short: \
             {short_successes} short successes, {written} bytes accepted"
        );
        #[cfg(not(any(target_os = "linux", target_os = "android")))]
        let _ = short_successes;
    }

    /// Inside `with_sigpipe_held`, a vectored write to a socket whose peer is
    /// gone is an `EPIPE` error and the process lives. std's socket `write`
    /// passes `MSG_NOSIGNAL` on Linux, but `write_vectored` is a plain `writev`
    /// (what rustls uses under the Zenodo upload), so without the scope this
    /// test binary, whose SIGPIPE is `SIG_DFL` under `unix_hardened`, dies with
    /// exit 141. Linux and Android only: on Apple the scope does nothing (std's
    /// `connect` marks its sockets `SO_NOSIGPIPE`, and a `pair` end is not
    /// one of those).
    #[cfg(any(target_os = "linux", target_os = "android"))]
    #[test]
    fn a_vectored_socket_write_inside_the_scope_is_an_epipe_error_not_a_signal() {
        use std::io::IoSlice;
        use std::os::unix::net::UnixStream;

        let (ours, theirs) = UnixStream::pair().expect("a socket pair");
        drop(theirs);
        let written = super::with_sigpipe_held(|| (&ours).write_vectored(&[IoSlice::new(b"x")]))
            .expect("hold SIGPIPE");
        // Reaching this line after the scope restored the mask also shows that
        // the signal the write raised was consumed, not left pending.
        let error = written.expect_err("the peer is gone");
        assert_eq!(error.kind(), std::io::ErrorKind::BrokenPipe);
    }
}
