// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A SIGTERM in the supervisor's start-up window gets exactly one answer.
//!
//! The solve's SIGTERM contract is one `unknown` on stdout and exit 124. Two
//! windows of the re-exec supervisor (the default off macOS) broke it, both
//! measured with a SIGTERM a fixed delay after launch:
//!
//! - 7-23 ms: the supervisor answered `unknown` itself because the child's pid
//!   was not published yet, while the child, already spawned, saw its parent
//!   die and answered too: `unknown` twice, exit 124.
//! - 10-20 ms: the supervisor forwarded the SIGTERM to a child still starting
//!   up, whose signal mask `Command::spawn` had emptied, so the child died of
//!   it with no answer: exit 143, empty stdout.
//!
//! The sweep below sends SIGTERM every half millisecond across the start-up of
//! both supervisors. The one accepted silence is a SIGTERM that lands before
//! `main` runs (the process dies of the signal itself, see `early_sigterm`);
//! anything else must be exactly one `unknown` and exit 124.

#[cfg(unix)]
mod unix_tests {
    use ntest::timeout;
    use std::io::{BufWriter, Read, Write};
    use std::os::unix::process::{CommandExt, ExitStatusExt};
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::sync::mpsc;
    use std::time::{Duration, Instant};
    use wait_timeout::ChildExt;

    /// The sweep: one SIGTERM every [`DELAY_STEP_US`] from launch to here. On
    /// a release build the defect windows were 7-12 ms after launch on an idle
    /// machine (2026-10-02: 119 of 240 trials wrong there before the fix) and
    /// up to 23 ms under load; the range runs past them so a loaded machine
    /// still crosses them.
    const LAST_DELAY_US: u64 = 40_000;
    /// The windows are a few milliseconds wide.
    const DELAY_STEP_US: u64 = 500;

    struct DirGuard(PathBuf);

    impl Drop for DirGuard {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// A random 3-SAT instance far above the threshold (see
    /// `supervisor_sigkill_orphan`): the solve is always still running when
    /// the SIGTERM lands.
    fn write_unbounded_formula(path: &Path) {
        const VARIABLES: u64 = 2_000;
        const CLAUSES: u64 = 9_000;
        let file = std::fs::File::create(path).expect("create formula");
        let mut out = BufWriter::new(file);
        for variable in 1..=VARIABLES {
            writeln!(out, "(declare-const p{variable} Bool)").expect("write declaration");
        }
        let mut state: u64 = 0x2026_1002;
        let mut literal = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let variable = (state >> 33) % VARIABLES + 1;
            if (state >> 20) & 1 == 0 {
                format!("p{variable}")
            } else {
                format!("(not p{variable})")
            }
        };
        for _ in 0..CLAUSES {
            writeln!(
                out,
                "(assert (or {} {} {}))",
                literal(),
                literal(),
                literal()
            )
            .expect("write clause");
        }
        writeln!(out, "(check-sat)").expect("write check-sat");
        out.flush().expect("flush formula");
    }

    /// What one trial ended with.
    #[derive(Debug)]
    struct Trial {
        delay_us: u64,
        code: Option<i32>,
        signal: Option<i32>,
        stdout: String,
    }

    /// Launch ay in its own process group, SIGTERM it `delay` after launch,
    /// and collect its exit and its whole stdout (which the solver child may
    /// write after the supervisor is gone). Everything in the group is killed
    /// if it outlives the budget.
    fn sigterm_after(
        formula: &Path,
        extra: &[&str],
        delay: Duration,
    ) -> (Option<i32>, Option<i32>, String) {
        let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--quiet")
            .args(extra)
            .arg(formula)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .process_group(0)
            .spawn()
            .expect("spawn ay");
        let launched = Instant::now();
        let group = nix::unistd::Pid::from_raw(child.id() as i32);
        let mut stdout = child.stdout.take().expect("stdout pipe");
        let (sender, receiver) = mpsc::channel();
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = stdout.read_to_end(&mut bytes);
            let _ = sender.send(bytes);
        });
        // Spin, not sleep: the windows are a few milliseconds wide.
        while launched.elapsed() < delay {
            std::hint::spin_loop();
        }
        let _ = nix::sys::signal::kill(group, nix::sys::signal::Signal::SIGTERM);
        let status = match child.wait_timeout(Duration::from_secs(15)).expect("wait") {
            Some(status) => status,
            None => {
                let _ = nix::sys::signal::killpg(group, nix::sys::signal::Signal::SIGKILL);
                child.wait().expect("reap")
            }
        };
        // The solver child holds the pipe until it is gone too.
        let bytes = match receiver.recv_timeout(Duration::from_secs(15)) {
            Ok(bytes) => bytes,
            Err(_) => {
                let _ = nix::sys::signal::killpg(group, nix::sys::signal::Signal::SIGKILL);
                receiver
                    .recv_timeout(Duration::from_secs(5))
                    .unwrap_or_default()
            }
        };
        (
            status.code(),
            status.signal(),
            String::from_utf8_lossy(&bytes).into_owned(),
        )
    }

    fn sweep(extra: &[&str]) {
        let dir = std::env::temp_dir().join(format!(
            "ay_startup_sigterm_{}_{}",
            std::process::id(),
            extra.len()
        ));
        std::fs::create_dir_all(&dir).expect("create scratch dir");
        let _guard = DirGuard(dir.clone());
        let formula = dir.join("unbounded.smt2");
        write_unbounded_formula(&formula);

        let trials: Vec<Trial> = (0..=LAST_DELAY_US)
            .step_by(DELAY_STEP_US as usize)
            .map(|delay_us| {
                let (code, signal, stdout) =
                    sigterm_after(&formula, extra, Duration::from_micros(delay_us));
                Trial {
                    delay_us,
                    code,
                    signal,
                    stdout,
                }
            })
            .collect();

        // Killed before `main` ran: the one window no code in the binary can
        // close. The supervisor itself dies of SIGTERM with nothing written.
        let before_main =
            |trial: &&Trial| trial.signal == Some(nix::libc::SIGTERM) && trial.stdout.is_empty();
        let wrong: Vec<&Trial> = trials
            .iter()
            .filter(|trial| !before_main(trial))
            .filter(|trial| trial.stdout != "unknown\n" || trial.code != Some(124))
            .collect();
        assert!(
            wrong.is_empty(),
            "{extra:?}: a SIGTERM after main must be answered by exactly one `unknown` and \
             exit 124; wrong trials: {wrong:#?}"
        );
        let answered = trials.iter().filter(|trial| !before_main(trial)).count();
        assert!(
            answered * 2 > trials.len(),
            "{extra:?}: the sweep never reached the supervisor's start-up (only {answered} of \
             {} trials got past main): {trials:#?}",
            trials.len()
        );
    }

    /// The re-exec supervisor, forced: the default off macOS.
    #[test]
    #[timeout(300_000)]
    fn reexec_supervisor_answers_a_start_up_sigterm_once() {
        sweep(&["--force-reexec-supervisor"]);
    }

    /// The default supervisor (the fork supervisor on macOS).
    #[test]
    #[timeout(300_000)]
    fn default_supervisor_answers_a_start_up_sigterm_once() {
        sweep(&[]);
    }
}
