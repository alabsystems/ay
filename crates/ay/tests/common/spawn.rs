// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Timeout-bounded subprocess spawning for CLI integration tests.
//!
//! ntest's `#[timeout]` runs the test body on a worker thread and panics on
//! the harness thread when the deadline expires — the worker thread stays
//! parked inside `Command::output()` (blocking waitpid) and the `ay` child is
//! orphaned when the test process exits (observed 29→135 GB RSS incident,
//! 2026-07-10). The fix must live INSIDE the blocking call: the child gets its
//! own process group, and on expiry the waiting thread itself SIGKILLs the
//! whole group (covering grandchildren such as flow_cutter spawned by
//! ay-count/src/td.rs:93 and run.sh wrappers) before ntest's deadline fires.
#![allow(dead_code)]

use std::io::{self, Read, Write};
use std::process::{Child, Command, Output, Stdio};
use std::thread;
use std::time::Duration;
use wait_timeout::ChildExt;

/// Default child deadline. Keep it BELOW the file's ntest #[timeout] (most
/// files use 30_000 ms) so this helper fires first and the test thread
/// unwinds normally instead of being detached.
pub const DEFAULT_CHILD_TIMEOUT: Duration = Duration::from_secs(25);

pub trait OutputTimeout {
    /// Drop-in replacement for `Command::output()`.
    /// Differences: own process group; stdout/stderr drained on reader
    /// threads (no 64 KiB pipe-buffer deadlock — the sat_par2_harness house
    /// pattern reads only after exit and would hang on verbose "v "-line
    /// output); on expiry the whole group is SIGKILLed and an
    /// io::ErrorKind::TimedOut error is returned carrying partial stderr.
    fn output_timeout(&mut self, timeout: Duration) -> io::Result<Output>;

    /// Same, but writes `input` to a piped stdin (writer thread; ignores
    /// EPIPE if the child exits early). For the stdin-driving sites
    /// (e.g. group_cli/z3_compat_args.rs run_ay_stdin_with_args).
    fn output_timeout_with_stdin(&mut self, input: &[u8], timeout: Duration) -> io::Result<Output>;
}

impl OutputTimeout for Command {
    fn output_timeout(&mut self, timeout: Duration) -> io::Result<Output> {
        self.stdin(Stdio::null()); // parity with Command::output()
        run(self, None, timeout)
    }
    fn output_timeout_with_stdin(&mut self, input: &[u8], timeout: Duration) -> io::Result<Output> {
        self.stdin(Stdio::piped());
        run(self, Some(input.to_vec()), timeout)
    }
}

fn run(cmd: &mut Command, stdin: Option<Vec<u8>>, timeout: Duration) -> io::Result<Output> {
    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0); // child pgid = child pid; stable std API
    }
    let mut child = cmd.spawn()?;
    if let Some(bytes) = stdin {
        let mut pipe = child.stdin.take().expect("stdin was piped");
        thread::spawn(move || {
            let _ = pipe.write_all(&bytes); // EPIPE ok: child may exit first
        });
    }
    let out_h = drain(child.stdout.take());
    let err_h = drain(child.stderr.take());
    let waited = child.wait_timeout(timeout);
    match waited {
        Ok(Some(status)) => Ok(Output {
            status,
            stdout: out_h.join().expect("stdout drain thread"),
            stderr: err_h.join().expect("stderr drain thread"),
        }),
        Ok(None) => {
            kill_group(&mut child);
            let stderr = err_h.join().expect("stderr drain thread");
            let stdout = out_h.join().expect("stdout drain thread");
            Err(io::Error::new(
                io::ErrorKind::TimedOut,
                format!(
                    "child exceeded {timeout:?}; process group killed. \
                     partial stdout ({}B): {:.400} | partial stderr: {:.400}",
                    stdout.len(),
                    String::from_utf8_lossy(&stdout),
                    String::from_utf8_lossy(&stderr)
                ),
            ))
        }
        Err(e) => {
            kill_group(&mut child);
            let _ = out_h.join();
            let _ = err_h.join();
            Err(e)
        }
    }
}

fn drain<R: Read + Send + 'static>(pipe: Option<R>) -> thread::JoinHandle<Vec<u8>> {
    thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(mut p) = pipe {
            let _ = p.read_to_end(&mut buf);
        }
        buf
    })
}

fn kill_group(child: &mut Child) {
    #[cfg(unix)]
    {
        use nix::sys::signal::{killpg, Signal};
        use nix::unistd::Pid;
        let _ = killpg(Pid::from_raw(child.id() as i32), Signal::SIGKILL);
    }
    let _ = child.kill(); // fallback / non-unix
    let _ = child.wait(); // reap — no zombie
}
