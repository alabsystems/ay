// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Run one test ALONE, in a re-exec of its own test binary where SIGPIPE
//! terminates the process — the harness for regression tests of writes to a
//! child process whose reader is gone.
//!
//! Such a test cannot run in the ordinary multi-threaded test process:
//!
//! - Whether a write to a pipe with no reader KILLS the process depends on the
//!   build. AY's `unix_hardened` Trust profile gives every `main`, test
//!   harnesses included, SIGPIPE at `SIG_DFL`; a stock toolchain ignores it,
//!   and there a write that bypasses `ay_sys::child_pipe::ChildPipeWriter`
//!   fails with an ordinary `EPIPE` the test could not tell from the fix. The
//!   re-exec installs the default action itself, so the test means the same on
//!   every toolchain: a bypass is a SIGPIPE death, named as one.
//! - "The child exited, so its stdin has no reader" is false while other tests
//!   spawn children at the same time. macOS has no `pipe2`: std sets
//!   `FD_CLOEXEC` in a second call, and a child another test spawns in that
//!   window inherits the read end and keeps the pipe open. The write then
//!   succeeds, or blocks until that unrelated child exits. In the re-exec
//!   nothing else spawns.
//!
//! `ay-pb-core`'s dead-SDP-worker test introduced the pattern; this is it for
//! every crate. The re-exec is recognised by its own libtest arguments
//! (`--exact <test> --test-threads=1`), not by an environment key: a harness
//! running exactly one test on one thread IS that test alone, whoever started
//! it.
//!
//! [`stops_reading_watch_server`] is the one dead-reader child such tests
//! share: a campaign sidecar that stays healthy after its stdin has no reader.

use std::io;
use std::process::Command;

#[cfg(test)]
use crate::isolated_test::{exact_test_name, running_exactly};

/// Gate a test on running alone with SIGPIPE at its default action.
///
/// Call it first in the test body:
/// `if !run_alone(module_path!(), "<test fn name>").expect("run alone") { return; }`.
///
/// Inside the re-exec (or a human's `--exact <test> --test-threads=1`) it
/// makes SIGPIPE terminate the process and returns `true`: the caller then runs
/// its scenario. Otherwise it re-execs the current test binary for exactly this
/// test, requires that the re-exec was not killed by SIGPIPE (naming the signal
/// when it was), that it passed, and that it ran the test, then returns `false`
/// and the caller returns.
///
/// # Errors
///
/// When SIGPIPE's default action cannot be installed in the re-exec, or the
/// re-exec cannot be started.
///
/// # Panics
///
/// When the re-exec is killed by SIGPIPE, fails, or does not run the test.
pub fn run_alone(module_path: &str, test: &str) -> io::Result<bool> {
    run_alone_with(module_path, test, |_| {})
}

/// [`run_alone`], with `configure` applied to the re-exec's command only — for
/// a scenario that needs process-global configuration its siblings must not
/// see (an environment variable naming the z3 oracle a `OnceLock` resolves
/// once per process, say).
///
/// # Errors
///
/// As [`run_alone`].
///
/// # Panics
///
/// As [`run_alone`].
pub fn run_alone_with(
    module_path: &str,
    test: &str,
    configure: impl FnOnce(&mut Command),
) -> io::Result<bool> {
    use std::os::unix::process::ExitStatusExt as _;

    let execution = crate::isolated_test::execute(module_path, test, configure)?;
    let crate::isolated_test::Execution::Reexecuted { exact, output } = execution else {
        // Replaces SIGPIPE's disposition for this whole process, which is why
        // it only happens here, where one test runs. The handler runs the
        // signal's default action: it restores `SIG_DFL` and re-raises.
        signal_hook::flag::register_conditional_default(
            signal_hook::consts::SIGPIPE,
            std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true)),
        )?;
        return Ok(true);
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_ne!(
        output.status.signal(),
        Some(signal_hook::consts::SIGPIPE),
        "`{exact}` was KILLED by SIGPIPE: a write to a pipe with no reader \
         bypassed `ChildPipeWriter`\n{stdout}{stderr}"
    );
    crate::isolated_test::require_passed(&exact, &output);
    Ok(false)
}

/// A stand-in for `scripts/_oom_guard.py watch-server`, run with `python3`,
/// that stops reading: it prints `ready_marker` (the line the campaign parent
/// waits for), answers ONE `WATCH` registration with `READY` after CLOSING its
/// stdin, and keeps heartbeating. It is healthy by every check the parent
/// makes, with no reader left on its registration pipe, so the parent's next
/// registration writes into a pipe whose reader is gone.
///
/// # Errors
///
/// When `ready_marker` is not UTF-8.
pub fn stops_reading_watch_server(ready_marker: &[u8]) -> Result<String, std::str::Utf8Error> {
    let marker = std::str::from_utf8(ready_marker)?;
    Ok(STOPS_READING_WATCH_SERVER.replace("@READY_MARKER@", marker.trim_end()))
}

/// [`stops_reading_watch_server`]'s script, before its ready marker is filled
/// in.
const STOPS_READING_WATCH_SERVER: &str = r#"
import os, sys, threading, time
lock = threading.Lock()
def emit(line):
    with lock:
        sys.stdout.write(line + '\n')
        sys.stdout.flush()
emit('@READY_MARKER@')
def beat():
    while True:
        emit('HEARTBEAT %d' % max(1, time.monotonic_ns()))
        time.sleep(0.05)
threading.Thread(target=beat, daemon=True).start()
fields = sys.stdin.buffer.readline().decode('ascii').split()
os.close(0)
emit('READY ' + fields[1])
time.sleep(2)
# `os._exit`, not the end of the script: interpreter shutdown while the
# daemon heartbeat thread is mid-write aborts Python (a crash report, and a
# "quit unexpectedly" dialog for Homebrew's Python.app).
os._exit(0)
"#;

#[cfg(test)]
mod tests {
    use super::{exact_test_name, running_exactly};

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|arg| (*arg).to_owned()).collect()
    }

    #[test]
    fn the_test_name_drops_the_crate() {
        assert_eq!(
            exact_test_name("ay_bench::resource::tests", "dead_child"),
            "resource::tests::dead_child"
        );
        assert_eq!(exact_test_name("group_cli", "dead_child"), "dead_child");
    }

    #[test]
    fn only_an_exact_single_threaded_run_of_the_test_is_alone() {
        let exact = "resource::tests::dead_child";
        assert!(running_exactly(
            exact,
            args(&["--exact", exact, "--nocapture", "--test-threads=1"])
        ));
        // A filter run, a multi-threaded run and a run of another test are
        // ordinary runs: they re-exec.
        assert!(!running_exactly(exact, args(&[exact])));
        assert!(!running_exactly(exact, args(&["--exact", exact])));
        assert!(!running_exactly(
            exact,
            args(&["--exact", "resource::tests::other", "--test-threads=1"])
        ));
    }
}
