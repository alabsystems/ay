// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::io::{BufRead as _, BufReader, Write as _};
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::process::{ChildStdout, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

struct OwnedChild {
    child: Child,
    output: BufReader<ChildStdout>,
    reaped: bool,
}

impl OwnedChild {
    fn waiting() -> Self {
        Self::with_script("printf 'ready\\n'; read hold; exit 7")
    }

    fn with_script(script: &str) -> Self {
        let mut child = Command::new("/bin/sh")
            .args(["-c", script])
            .process_group(0)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn owned child");
        let mut line = String::new();
        let mut output = BufReader::new(child.stdout.take().expect("stdout"));
        output.read_line(&mut line).expect("child readiness");
        assert_eq!(line, "ready\n");
        Self {
            child,
            output,
            reaped: false,
        }
    }

    fn signal(&self, signal: i32) {
        let pid = i32::try_from(self.child.id()).expect("pid");
        // SAFETY: this is the still-unreaped owned child, with a positive PID.
        assert_eq!(unsafe { libc::kill(pid, signal) }, 0, "signal owned child");
    }

    fn wait(&mut self) -> ExitStatus {
        let status = self.child.wait().expect("final owner reaps");
        self.reaped = true;
        status
    }
}

impl Drop for OwnedChild {
    fn drop(&mut self) {
        if !self.reaped {
            // This PID is still an unreaped owned child, so its group cannot
            // have been reused. SIGKILL also terminates a stopped child.
            let pid = i32::try_from(self.child.id()).expect("pid");
            // SAFETY: the positive group is owned and its leader is unreaped.
            let _ = unsafe { libc::killpg(pid, libc::SIGKILL) };
            let _ = self.child.wait();
        }
    }
}

fn await_event(child: &Child, expected: Event) {
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if observe(child, Events::ExitOrStop).expect("observe owned child") == Some(expected) {
            return;
        }
        assert!(
            Instant::now() < deadline,
            "owned child event did not arrive"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn repeated_running_stop_and_exit_observations_leave_status_for_the_owner() {
    let mut owned = OwnedChild::waiting();
    for _ in 0..2 {
        assert_eq!(
            observe(&owned.child, Events::ExitOnly).expect("running"),
            None
        );
    }
    owned.signal(libc::SIGSTOP);
    for _ in 0..2 {
        await_event(&owned.child, Event::Stopped(libc::SIGSTOP));
        assert_eq!(
            observe(&owned.child, Events::ExitOrStop).expect("stop"),
            Some(Event::Stopped(libc::SIGSTOP))
        );
        let exit_only = observe(&owned.child, Events::ExitOnly).expect("exit-only");
        assert!(
            matches!(exit_only, None | Some(Event::Stopped(libc::SIGSTOP))),
            "an exit-only peek may omit the stop or report it, never an exit: {exit_only:?}"
        );
    }
    owned.signal(libc::SIGCONT);
    drop(owned.child.stdin.take());
    await_event(&owned.child, Event::Exited(7));
    for _ in 0..2 {
        assert_eq!(
            observe(&owned.child, Events::ExitOnly).expect("unreaped exit"),
            Some(Event::Exited(7))
        );
    }
    assert_eq!(owned.wait().code(), Some(7));
    assert!(
        observe(&owned.child, Events::ExitOrStop).is_err(),
        "ECHILD must remain an error"
    );
}

#[test]
fn signal_exit_stays_waitable_for_its_owner() {
    let mut owned = OwnedChild::waiting();
    owned.signal(libc::SIGTERM);
    await_event(&owned.child, Event::Killed(libc::SIGTERM));
    for _ in 0..2 {
        assert_eq!(
            observe(&owned.child, Events::ExitOnly).expect("unreaped signal"),
            Some(Event::Killed(libc::SIGTERM))
        );
    }
    assert_eq!(owned.wait().signal(), Some(libc::SIGTERM));
}

#[test]
fn a_proven_resume_clears_the_old_stop_before_another_stop() {
    let mut owned = OwnedChild::with_script(
        "printf 'ready\\n'; read first; printf 'resumed\\n'; read hold; exit 7",
    );
    owned.signal(libc::SIGSTOP);
    await_event(&owned.child, Event::Stopped(libc::SIGSTOP));
    owned.signal(libc::SIGCONT);
    let mut input = crate::child_pipe::ChildPipeWriter::take_from(&mut owned.child)
        .expect("protected child pipe");
    input.write_all(b"continue\n").expect("release first read");
    input.flush().expect("flush first read");
    let mut resumed = String::new();
    owned
        .output
        .read_line(&mut resumed)
        .expect("actual resumed child");
    assert_eq!(resumed, "resumed\n");
    assert_eq!(
        observe(&owned.child, Events::ExitOrStop).expect("observe resumed child"),
        None,
        "the first stop must not remain after the child demonstrably resumed"
    );
    owned.signal(libc::SIGSTOP);
    await_event(&owned.child, Event::Stopped(libc::SIGSTOP));
    owned.signal(libc::SIGCONT);
    drop(input);
    await_event(&owned.child, Event::Exited(7));
    assert_eq!(owned.wait().code(), Some(7));
}
