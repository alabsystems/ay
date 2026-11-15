// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Staging-file hygiene across an abnormal exit (#68).
//!
//! An unsealed DIMACS proof lives in `.ay-dimacs-proof-<pid>-<nonce>.stage`
//! beside its target until publication renames it onto that target. Nothing
//! unlinked that file when the process left through `process::exit`, which is
//! how every timeout, termination and fatal error ends an `ay` run: a sweep of
//! this repository's benchmark tree on 2026-08-27 found 86 stranded stages
//! holding 40.1 GB, the oldest from 7 August, several of them inside the shared
//! CNF corpus.
//!
//! The two cases below pin both halves of the fix at the process level: an
//! abandoned stage does not survive the exit, and a proof that WAS published
//! survives it untouched.

#[cfg(unix)]
mod unix_tests {
    use ntest::timeout;
    use std::io::{BufWriter, Write};
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};
    use wait_timeout::ChildExt;

    const STAGING_PREFIX: &str = ".ay-dimacs-proof-";

    fn staging_files(dir: &Path) -> Vec<PathBuf> {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return Vec::new();
        };
        entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "stage")
                    && path
                        .file_name()
                        .and_then(|name| name.to_str())
                        .is_some_and(|name| name.starts_with(STAGING_PREFIX))
            })
            .collect()
    }

    /// Write a CNF large enough that parsing it outlasts the two-second grace
    /// the SIGTERM poller allows before it hard-exits.
    ///
    /// The size is what makes the case reach the destructor-skipping exit: the
    /// solver is still inside the parser when the signal lands, never reaches a
    /// cancellation checkpoint, and therefore never runs the cooperative
    /// shutdown that would have discarded the proof itself. On a machine fast
    /// enough to finish parsing inside the grace, the cooperative path wins
    /// instead and the assertion below still has to hold — this test can lose
    /// coverage on faster hardware, never soundness.
    fn write_parse_bound_cnf(path: &Path) {
        const VARIABLES: u64 = 700_000;
        const CLAUSES: u64 = 2_982_000; // 700_000 * 4.26, the phase transition.
        let file = std::fs::File::create(path).expect("create CNF");
        let mut out = BufWriter::with_capacity(1 << 20, file);
        writeln!(out, "p cnf {VARIABLES} {CLAUSES}").expect("write CNF header");
        let mut state: u64 = 0x2026_0827;
        let mut literal = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let variable = (state >> 33) % VARIABLES + 1;
            if state & 1 == 0 {
                variable as i64
            } else {
                -(variable as i64)
            }
        };
        for _ in 0..CLAUSES {
            writeln!(out, "{} {} {} 0", literal(), literal(), literal()).expect("write clause");
        }
        out.flush().expect("flush CNF");
    }

    fn wait_for_staging_file(dir: &Path, budget: Duration) -> bool {
        let deadline = Instant::now() + budget;
        while Instant::now() < deadline {
            if !staging_files(dir).is_empty() {
                return true;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        false
    }

    /// Whether `pid` holds an anonymous `O_TMPFILE` stage in `dir` open.
    ///
    /// That is how Linux stages an unsealed proof: the inode has no name to
    /// strand and none for [`staging_files`] to see, but the solver keeps it
    /// open, and `/proc/<pid>/fd` shows it as `<dir>/#<inode> (deleted)`.
    #[cfg(target_os = "linux")]
    fn holds_anonymous_stage(pid: u32, dir: &Path) -> bool {
        let Ok(dir) = dir.canonicalize() else {
            return false;
        };
        let Ok(entries) = std::fs::read_dir(format!("/proc/{pid}/fd")) else {
            return false;
        };
        entries
            .flatten()
            .filter_map(|entry| std::fs::read_link(entry.path()).ok())
            .any(|target| {
                target.parent() == Some(dir.as_path())
                    && target
                        .file_name()
                        .and_then(|name| name.to_str())
                        .is_some_and(|name| name.starts_with('#') && name.ends_with(" (deleted)"))
            })
    }

    /// Wait until `pid` has staged its unsealed proof in `dir`, under either
    /// staging scheme: a named sibling stage, or (Linux) an anonymous inode.
    ///
    /// Waiting only for the NAMED stage made the SAT-COMP case vacuous on
    /// Linux: it slept the whole budget, and the parse-bound formula (every
    /// clause has a positive literal, so all-true satisfies it) was solved
    /// before the signal -- measured at 14.6 s against a 30 s budget, with the
    /// anonymous stage visible from 0.35 s -- so `kill -TERM` hit a finished
    /// run that had printed `s SATISFIABLE`.
    fn wait_for_staged_proof(pid: u32, dir: &Path, budget: Duration) -> bool {
        let deadline = Instant::now() + budget;
        while Instant::now() < deadline {
            if !staging_files(dir).is_empty() {
                return true;
            }
            #[cfg(target_os = "linux")]
            if holds_anonymous_stage(pid, dir) {
                return true;
            }
            #[cfg(not(target_os = "linux"))]
            let _ = pid;
            std::thread::sleep(Duration::from_millis(20));
        }
        false
    }

    fn terminate(pid: u32) {
        let status = Command::new("kill")
            .args(["-TERM", &pid.to_string()])
            .status()
            .expect("signal the solver");
        assert!(status.success(), "kill -TERM should reach the solver");
    }

    #[test]
    #[timeout(120_000)]
    fn terminated_solve_strands_no_proof_staging_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = dir.path().join("parse-bound.cnf");
        let proof_dir = dir.path().join("proofs");
        std::fs::create_dir(&proof_dir).expect("create proof directory");
        write_parse_bound_cnf(&cnf);
        let proof = proof_dir.join("out.drat");

        let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--timeout")
            .arg("600000")
            .arg("--proof")
            .arg(&proof)
            .arg(&cnf)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn ay");

        // Linux stages an unsealed proof on an anonymous `O_TMPFILE` inode,
        // which has no pathname to strand and which the kernel reclaims at
        // exit; every other platform falls back to the named sibling stage this
        // waits for.
        let staged = wait_for_staging_file(&proof_dir, Duration::from_secs(30));
        if cfg!(not(target_os = "linux")) {
            assert!(
                staged,
                "the solver must stage its unsealed proof beside the target"
            );
        }

        terminate(child.id());
        let status = child
            .wait_timeout(Duration::from_secs(30))
            .expect("wait for the terminated solver");
        if status.is_none() {
            let _ = child.kill();
            let _ = child.wait();
            panic!("the terminated solver never exited");
        }

        assert!(
            staging_files(&proof_dir).is_empty(),
            "a terminated solve must strand no proof staging file; found {:?}",
            staging_files(&proof_dir)
        );
        assert!(
            !proof.exists(),
            "an unsealed proof must never be published by the exit sweep"
        );
    }

    /// The shipped SAT-COMP invocation (VeriPB proof, competition wrapper),
    /// terminated mid-solve: it answers `s UNKNOWN` with exit 0 and leaves its
    /// output directory empty. No proof, no stage, no quarantine directory
    /// (2026-09-13; a runner must never be left the proof of an unanswered run).
    #[test]
    #[timeout(120_000)]
    fn terminated_satcomp_veripb_solve_leaves_an_empty_output_directory() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = dir.path().join("parse-bound.cnf");
        let output_dir = dir.path().join("output");
        std::fs::create_dir(&output_dir).expect("create output directory");
        write_parse_bound_cnf(&cnf);
        let proof = output_dir.join("proof.out");

        let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
            .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
            .env(
                "AY_INTERNAL_SATCOMP_WRAPPER",
                "main-regular-default-veripb-v1",
            )
            .env("AY_SAT_COMPETITION_PROFILE", "regular")
            .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
            .env("AY_SAT_VARIANT", "default")
            .env("AY_COMPETITION_JIT_MODE", "off")
            .args(["solve", "--sat-variant", "default", "--proof"])
            .arg(&proof)
            .args([
                "--proof-format",
                "veripb",
                "--proof-checker",
                "veripb",
                "--no-verify-proof",
                "--timeout=600000",
            ])
            .arg(&cnf)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn ay");

        // Signal only once the proof is staged, on every platform: this case
        // is about a run terminated WITH a proof in progress.
        assert!(
            wait_for_staged_proof(child.id(), &output_dir, Duration::from_secs(30)),
            "the solver must stage its unsealed proof in the output directory"
        );
        terminate(child.id());
        let Some(status) = child
            .wait_timeout(Duration::from_secs(30))
            .expect("wait for the terminated solver")
        else {
            let _ = child.kill();
            let _ = child.wait();
            panic!("the terminated solver never exited");
        };
        let mut stdout = String::new();
        std::io::Read::read_to_string(&mut child.stdout.take().expect("piped stdout"), &mut stdout)
            .expect("read stdout");

        let status_lines: Vec<&str> = stdout
            .lines()
            .filter(|line| line.starts_with("s "))
            .collect();
        assert_eq!(status_lines, ["s UNKNOWN"], "stdout: {stdout}");
        assert_eq!(status.code(), Some(0), "the competition unknown exit code");
        let left: Vec<PathBuf> = std::fs::read_dir(&output_dir)
            .expect("read output directory")
            .map(|entry| entry.expect("entry").path())
            .collect();
        assert!(
            left.is_empty(),
            "an unanswered run must leave its output directory empty; found {left:?}"
        );
    }

    #[test]
    #[timeout(60_000)]
    fn published_proof_survives_the_exit_sweep() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = dir.path().join("unsat.cnf");
        std::fs::write(&cnf, "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n").expect("write CNF");
        let proof = dir.path().join("out.drat");

        let status = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--timeout")
            .arg("30000")
            .arg("--proof")
            .arg(&proof)
            .arg(&cnf)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("run ay");

        assert_eq!(status.code(), Some(20), "the instance is UNSAT");
        let published =
            std::fs::read(&proof).expect("the published proof must survive process exit");
        assert!(
            !published.is_empty(),
            "the published proof must keep its bytes"
        );
        assert!(
            staging_files(dir.path()).is_empty(),
            "publication must consume the staging name"
        );
    }
}
