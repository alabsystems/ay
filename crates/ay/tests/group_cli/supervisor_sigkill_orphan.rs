// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A SIGKILLed supervisor must not leave its solver child behind.
//!
//! Every solve runs behind a supervising parent that reaps the solver child.
//! SIGINT/SIGTERM/SIGHUP to that parent were already forwarded as a kill of the
//! child, but a SIGKILLed parent runs no handler at all, and `SIGKILL` is what
//! benchmark harnesses send to the top-level process (`timeout -s KILL`,
//! Python's `subprocess.run(timeout=..)`, runsolver, a cancelled CI job).
//! Measured on macOS before the death pipe existed: the child kept solving with
//! no deadline, reparented to pid 1, and a 100-file sweep left 11 orphans at
//! ~60% CPU each. These cases pin the process-level contract: the child is gone
//! within a few seconds of its parent's death, for SIGKILL and — as the control
//! that the older path still works — for SIGTERM.

#[cfg(unix)]
mod unix_tests {
    use ntest::timeout;
    use std::io::{BufWriter, Write};
    use std::path::Path;
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant};

    /// Generous on purpose: the design target is well under a second (a 500 ms
    /// grace plus the exit), but this runs on shared, heavily loaded machines.
    const CHILD_EXIT_BUDGET: Duration = Duration::from_secs(5);

    /// Write a random 3-SAT instance far above the satisfiability threshold
    /// (ratio 4.5 at 2000 variables): unsatisfiable with overwhelming
    /// probability and, by the exponential resolution lower bound, beyond any
    /// CDCL solver's reach in bounded time — so the solver child is still
    /// running whenever this test decides to kill its parent.
    fn write_unbounded_formula(path: &Path) {
        const VARIABLES: u64 = 2_000;
        const CLAUSES: u64 = 9_000;
        let file = std::fs::File::create(path).expect("create formula");
        let mut out = BufWriter::new(file);
        for variable in 1..=VARIABLES {
            writeln!(out, "(declare-const p{variable} Bool)").expect("write declaration");
        }
        let mut state: u64 = 0x2026_0905;
        let mut literal = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let variable = (state >> 33) % VARIABLES + 1;
            // Polarity from a HIGH bit: the lowest bit of a power-of-two LCG
            // simply alternates, which would give every clause a positive
            // literal and make the all-true assignment a 0.3 s `sat`.
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

    /// `(pid, ppid, stat)` rows of every process, the portable way (`ps -axo`
    /// is the same on macOS and procps).
    fn process_table() -> Vec<(u32, u32, String)> {
        let output = Command::new("ps")
            .args(["-axo", "pid=,ppid=,stat="])
            .output()
            .expect("run ps");
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| {
                let mut fields = line.split_whitespace();
                let pid = fields.next()?.parse().ok()?;
                let ppid = fields.next()?.parse().ok()?;
                let stat = fields.next().unwrap_or("").to_string();
                Some((pid, ppid, stat))
            })
            .collect()
    }

    /// True while `pid` exists and is not a zombie (an orphan reparented to a
    /// slow reaper would otherwise still count as alive after it exited).
    fn solver_alive(pid: u32) -> bool {
        process_table()
            .iter()
            .any(|(p, _, stat)| *p == pid && !stat.starts_with('Z'))
    }

    /// Wait for the supervisor to fork its solver child and return that pid.
    fn wait_for_solver_child(wrapper: &mut Child, budget: Duration) -> u32 {
        let deadline = Instant::now() + budget;
        loop {
            if let Some(status) = wrapper.try_wait().expect("poll the supervisor") {
                panic!("the supervisor exited ({status:?}) before forking a solver child");
            }
            if let Some((pid, _, _)) = process_table()
                .into_iter()
                .find(|(_, ppid, _)| *ppid == wrapper.id())
            {
                return pid;
            }
            assert!(
                Instant::now() < deadline,
                "no solver child appeared under supervisor {} within {budget:?}",
                wrapper.id()
            );
            std::thread::sleep(Duration::from_millis(50));
        }
    }

    /// Never leave an orphan behind when an assertion fails.
    struct OrphanGuard(u32);

    impl Drop for OrphanGuard {
        fn drop(&mut self) {
            if solver_alive(self.0) {
                let _ = nix::sys::signal::kill(
                    nix::unistd::Pid::from_raw(self.0 as i32),
                    nix::sys::signal::Signal::SIGKILL,
                );
            }
        }
    }

    /// Spawn a supervised solve of an unbounded formula and return the
    /// supervisor together with its live solver child's pid.
    fn start_supervised_solve(dir: &Path) -> (Child, u32) {
        let formula = dir.join("unbounded.smt2");
        write_unbounded_formula(&formula);
        let mut wrapper = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--quiet")
            .arg(&formula)
            // Cargo sets CARGO_TARGET_TMPDIR for integration tests, which
            // disables the supervisor; remove it so the wrapper engages as in a
            // real harness run.
            .env_remove("CARGO_TARGET_TMPDIR")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn ay");
        let solver = wait_for_solver_child(&mut wrapper, Duration::from_secs(30));
        // Give the child a moment to get into the solve proper, then confirm the
        // formula really is keeping it busy.
        std::thread::sleep(Duration::from_millis(500));
        assert!(
            solver_alive(solver),
            "the solver child must still be running on the unbounded formula"
        );
        (wrapper, solver)
    }

    /// Poll until the solver is gone; returns how long that took, or `None`.
    fn wait_for_solver_exit(solver: u32, budget: Duration) -> Option<Duration> {
        let started = Instant::now();
        while started.elapsed() < budget {
            if !solver_alive(solver) {
                return Some(started.elapsed());
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        None
    }

    #[test]
    #[timeout(120_000)]
    fn sigkilled_supervisor_takes_its_solver_child_down() {
        let dir = tempfile::tempdir().expect("tempdir");
        let (mut wrapper, solver) = start_supervised_solve(dir.path());
        let _guard = OrphanGuard(solver);

        // SIGKILL: the supervisor gets no chance to run any handler.
        wrapper.kill().expect("SIGKILL the supervisor");
        let status = wrapper.wait().expect("reap the supervisor");
        assert!(!status.success(), "the supervisor was killed: {status:?}");

        let elapsed = wait_for_solver_exit(solver, CHILD_EXIT_BUDGET);
        assert!(
            elapsed.is_some(),
            "solver child {solver} outlived its SIGKILLed supervisor by more than \
             {CHILD_EXIT_BUDGET:?} (an orphan burning CPU)"
        );
        eprintln!("solver child exited {elapsed:?} after the supervisor was SIGKILLed");
    }

    /// Control: the pre-existing SIGTERM path (the supervisor's own reaper)
    /// still takes the child down.
    #[test]
    #[timeout(120_000)]
    fn sigtermed_supervisor_still_takes_its_solver_child_down() {
        let dir = tempfile::tempdir().expect("tempdir");
        let (mut wrapper, solver) = start_supervised_solve(dir.path());
        let _guard = OrphanGuard(solver);

        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(wrapper.id() as i32),
            nix::sys::signal::Signal::SIGTERM,
        )
        .expect("SIGTERM the supervisor");
        let _ = wrapper.wait().expect("reap the supervisor");

        let elapsed = wait_for_solver_exit(solver, CHILD_EXIT_BUDGET);
        assert!(
            elapsed.is_some(),
            "solver child {solver} outlived its SIGTERMed supervisor by more than \
             {CHILD_EXIT_BUDGET:?}"
        );
        eprintln!("solver child exited {elapsed:?} after the supervisor was SIGTERMed");
    }
}
